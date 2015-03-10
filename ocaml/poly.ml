open Error
open Printing
open Int
open Quasiring
open Basicdefs

module type POLYNOMIALSIG =
sig
  type monomial
  type polynomial
  type coeff
  val coeffInjection : int -> coeff
  val zeroPol : polynomial
  val onePol : polynomial
  val degree : ?safe:bool -> polynomial -> int
  val makePol : (coeff*int) list -> polynomial
  val polToList : polynomial -> (coeff*int) list
  val polToFlatList : polynomial -> coeff list
  val flatListToPol : coeff list -> polynomial
  val shift : polynomial -> int -> polynomial
  val add : polynomial -> polynomial -> polynomial
  val mul : polynomial -> polynomial -> polynomial
  val sub : polynomial -> polynomial -> polynomial
  val neg : polynomial -> polynomial
  val exp : polynomial -> int -> polynomial
  val primitive : polynomial -> polynomial
  val eval : polynomial -> coeff -> coeff
  val polToString : string -> polynomial -> string
  val normal : polynomial -> polynomial
  val eq : polynomial -> polynomial -> bool
  val shiftCons : polynomial -> int -> coeff -> polynomial
  val intmul :  int -> polynomial -> polynomial
end;;

module PolyOfQuasiRing (R : QUASIRING) : (POLYNOMIALSIG with type coeff = R.element) =
struct
  type coeff = R.element
  
  type monomial = R.element*int
  
  type polynomial = monomial list   (* (coeff,deg) in increasing degree order, no zero coeffs (sparse polynomials)*)
  
  let coeffInjection (x:int) = R.injection x 

  let (zeroPol:polynomial) = []
  
  let (onePol:polynomial) = [(R.one,0)]
  
  let makePol x = x
  
  let degree ?(safe=true) p = List.fold_right (fun (x,y) e -> max y e) p (-1)
  
(* in these two functions we sort coefficients to avoid any unpleasant effects *)
  let makePol l = List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l;;

  let polToList (l : polynomial) = List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l;;

  let polToFlatList (l : polynomial) = List.map fst (polToList l);;
  
  let flatListToPol (l : coeff list) = (List.mapi (fun i x -> (x,i)) l : polynomial);;

  let rec add (p1 : polynomial) (p2:polynomial)  = match (p1,p2) with
    |([],p2) -> p2
    |(p1,[]) -> p1
    |((a,b)::t1,(c,d)::t2) ->
        if b < d then
          (a,b)::(add t1 p2)
        else
          if d < b then
            (c,d)::(add p1 t2)
          else (* b = c *)
            let u = (R.add a c) in
            match (R.eqZero u) with
              | true -> add t1 t2 (* here a better test of equality to zero might be needed *)
              | false -> (u,b)::(add t1 t2)  (* to multiply p by x^n *)
  
  let rec shiftCons p n cons =
    match R.eqZero(cons) with
      | true -> []
      | false ->
          match p with
            | [] -> []
            | (a,b)::t -> let u = b+n in
                          if u >= 0 then
                            (R.mul a cons,u)::(shiftCons t n cons)
                          else
                            raise(NegativePower(u))                            
  let shift p n = shiftCons p n R.one

  let intmul x p = shiftCons p 0 (R.injection x)

  let neg p = shiftCons p 0 (R.neg R.one)

  let sub p1 p2 = add p1 (neg p2)
  
  let rec mul (p1 : polynomial) (p2 : polynomial) = match (p1,p2) with
    |([],p2) -> []
    |(p1,[]) -> []
    |((a,b)::t1,p2) -> add (shiftCons p2 b a) (mul t1 p2)

  let primitive p = failwith "primitive not implemented yet"

  let eval p x = failwith "eval not implemented yet"

  let powerToString var n =
    if n = 0 then "1"
    else
      if n = 1 then var
      else
        (var^"^"^(soi n))

  let rec monomialToString var a n =
    if (R.eqOne a) then
      powerToString var n
    else
      (R.soe a)^" "^
        (
          if n = 0 then ""
          else if n=1 then var
          else (var^"^"^(soi n))
        )

  let rec polToString var = function
    | [] -> "0\n"
    | [(a,b)] -> (monomialToString var a b)^"\n"
    | (a,b)::t -> (monomialToString var a b)^" + "^(polToString var t)

  let rec compareMonoms (a,b) (c,d) = b < d

  let normal p =
    let d = degree p in
    let t = Array.make (d+1) (R.zero,-1) in
    let rec aux = function
      | [] -> ()
      | (a,b)::tail ->
          (
            if t.(b) = (R.zero,-1) then
              t.(b) <- (a,b)
            else
              let (u,v) = t.(b) in
              t.(b) <- (R.add u a,b)
          )
          ;
          aux tail
    in let res = ref [] in
       aux p;
       for i = 0 to d do
         let mon = t.(i) in
         if not(R.eqZero(fst(mon))) then
           res := mon::!res
       done;
       List.rev(!res)

  let eq p1 p2 = normal(p1) = normal(p2)

  let rec exp p n = match n with
    | 0 -> onePol
    | _ -> if n < 0 then raise(NegativePowerOfPol)
      else
        let m = n/2 in
        let p1 = exp p m in
        ps (polToString "x" p1);
        match n mod 2 with
          |0 -> mul p1 p1
          |_ -> mul (mul p1 p1) p

end;;



















module PolyFlatOfQuasiRing (R : QUASIRING) : (POLYNOMIALSIG with type coeff = R.element) =
struct
  type coeff = R.element
  
  type monomial = R.element
  
  type polynomial = monomial list   (* (coeff,deg) in increasing degree order, no zero coeffs (sparse polynomials)*)
  
  let coeffInjection (x:int) = R.injection x 

  let (zeroPol:polynomial) = []
  
  let (onePol:polynomial) = [(R.one)]
  
  let clean (p : polynomial) = 
    let rec aux = function
      | [] -> []
      | a::t -> if R.eqZero a then (aux t) else (a::t) in
    List.rev (aux (List.rev p));;

     let degree ?(safe=true) (p: polynomial)  = ((List.length (if safe then (clean p) else p) - 1));;

  let flatten (p : (coeff*int) list) = 
    if p = [] then [] else
      let rec aux res = function
	| [] -> res
	| [a,b] -> (a,b)::res
	| (a,b)::(c,d)::t -> if d < b then failwith "unsorted polynomial" else if d = (b+1) then aux ((a,b)::res) ((c,d)::t) else (* b < d *)
	    aux ((a,b)::res) ((R.zero,b+1)::(c,d)::t)
  in let p1 = match (List.hd p) with (* ok because we've ruled out p = [] *)
  | (_,0) -> p
  | (_,_) -> (R.zero,0)::p
     in List.rev (aux [] p1);;
  
    
  (* in these two functions we sort coefficients to avoid any unpleasant effects *)
  let makePol (l : (coeff*int) list) = List.map fst (flatten (List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l));;

  let polToList l = List.mapi (fun i x -> (x,i)) l;;
  
  

  let polToFlatList (p : polynomial) = (p : R.element list);;
  
  let flatListToPol (p : polynomial) = (p : coeff list);;

  let rec add (p1 : polynomial) (p2 : polynomial) = match (p1,p2) with
    |([],p2) -> p2
    |(p1,[]) -> p1
    |(a::t1,c::t2) ->
      let u = (R.add a c) in
      (u)::(add t1 t2)
 
  let rec make_n_zeros = function
    | 0 -> []
    | k -> (R.zero)::(make_n_zeros (k-1));;

  let mul_const (const : R.element) (p : polynomial) =
    match R.eqZero(const) with
    | true -> []
    | false -> 
      let rec aux res = function
	| [] -> res
	| a::t -> aux ((R.mul a const)::res) t
      in List.rev (aux [] p);;

(* multiply p by cons * (x**n) *)
  let shiftCons (p : polynomial) n const =
        match R.eqZero(const) with
      | true -> []
      | false ->
	match p with
	| [] -> []
        | a::t -> (make_n_zeros n)@(mul_const const (a::t));;
	  
            
  (* let shift p n = shiftCons p n R.one *)

  let shift p n =
    let rec aux res = function
      | 0 -> res
      | k -> aux ((R.zero)::res) (k-1)
    in aux p n;;

  let intmul x p = shiftCons p 0 (R.injection x)

  let neg p = shiftCons p 0 (R.neg R.one)

  let sub p1 p2 = add p1 (neg p2)
  
  let rec mul (p1 : polynomial) (p2 : polynomial) = match (p1,p2) with
    |([],p2) -> []
    |(p1,[]) -> []
    |(a::t1,p2) -> add (shiftCons p2 0 a) (shift (mul t1 p2) 1)

(* builds a formal primitive (integration constant = 0) *)
  let primitive (p : polynomial) =
    let rec aux (res,k) = function
      | [] -> List.rev res
      | h::t -> aux ((R.div h (R.injection (k)))::res,k+1) t
    in shift (aux ([],1) p) 1;;

  let eval p x =
    let rec aux res = function
      | [] -> res
      | h::t -> aux (R.add (R.mul res x) h) t
    in aux R.zero (List.rev p);;

  let powerToString var n =
    if n = 0 then "1"
    else
      if n = 1 then var
      else
        (var^"^"^(soi n))

  let rec monomialToString var a n =
    if (R.eqOne a) then
      powerToString var n
    else
      (R.soe a)^" "^
        (
          if n = 0 then ""
          else if n=1 then var
          else (var^"^"^(soi n))
        )

  let polToString var (p : polynomial) = 
    let rec aux = function
      | [] -> "0\n"
      | [(a,b)] -> (monomialToString var a b)^"\n"
      | (a,b)::t -> (monomialToString var a b)^" + "^(aux t)
    in aux (List.mapi (fun i x -> (x,i)) p);;


  let rec compareMonoms (a,b) (c,d) = b < d

  let normal p = clean p;;

  let eq p1 p2 = normal(p1) = normal(p2)

  let rec exp p n = match n with
    | 0 -> onePol
    | _ -> if n < 0 then raise(NegativePowerOfPol)
      else
        let m = n/2 in
        let p1 = exp p m in
        ps (polToString "x" p1);
        match n mod 2 with
          |0 -> mul p1 p1
          |_ -> mul (mul p1 p1) p

end;;




(* module type POLYNOMIALSIG = *)
(* sig *)
(*   type monomial *)
(*   type polynomial *)
(*   type coeff *)
(*   val coeffInjection : int -> coeff *)
(*   val zeroPol : polynomial *)
(*   val onePol : polynomial *)
(*   val degree : polynomial -> int *)
(*   val makePol : (coeff*int) list -> polynomial *)
(*   val polToList : polynomial -> (coeff*int) list *)
(*   val polToFlatList : polynomial -> coeff list *)
(*   val flatListToPol : coeff list -> polynomial *)
(*   val shift : polynomial -> int -> polynomial *)
(*   val add : polynomial -> polynomial -> polynomial *)
(*   val mul : polynomial -> polynomial -> polynomial *)
(*   val sub : polynomial -> polynomial -> polynomial *)
(*   val neg : polynomial -> polynomial *)
(*   val exp : polynomial -> int -> polynomial *)
(*   val primitive : polynomial -> polynomial *)
(*   val eval : polynomial -> coeff -> coeff *)
(*   val polToString : string -> polynomial -> string *)
(*   val normal : polynomial -> polynomial *)
(*   val eq : polynomial -> polynomial -> bool *)
(*   val shiftCons : polynomial -> int -> coeff -> polynomial *)
(*   val intmul :  int -> polynomial -> polynomial *)
(* end;; *)

module ChebFlatPolyOfQuasiRing (R : QUASIRING) : (POLYNOMIALSIG with type coeff = R.element) =
struct
  type coeff = R.element
  type monomial = coeff
  type polynomial = monomial list
  let coeffInjection (x:int) = R.injection x 
  let defInt = Basicdefs.makeIntervalle (~-.1.) 1.;; (* default interval for Chebyshev models is [-1,1] *)
  let zeroPol = (([]):polynomial)
  let onePol = (([(R.one)]):polynomial)
    
  let clean (p : polynomial) = 
    let rec aux = function
      | [] -> []
      | a::t -> if R.eqZero a then (aux t) else (a::t) in
    List.rev (aux (List.rev p));;

   let degree ?(safe=true) (p: polynomial)  = ((List.length  (if safe then (clean p) else p)) - 1);;
   
  let flatten (p : (coeff*int) list) = 
    if p = [] then [] else
      let rec aux res = function
	| [] -> res
	| [a,b] -> (a,b)::res
	| (a,b)::(c,d)::t -> if d < b then failwith "unsorted polynomial" else if d = (b+1) then aux ((a,b)::res) ((c,d)::t) else (* b < d *)
	    aux ((a,b)::res) ((R.zero,b+1)::(c,d)::t)
  in let p1 = match (List.hd p) with (* ok because we've ruled out p = [] *)
  | (_,0) -> p
  | (_,_) -> (R.zero,0)::p
     in List.rev (aux [] p1);;
  
    
  (* in these two functions we sort coefficients to avoid any unpleasant effects *)
  let makePol (l : (coeff*int) list) = List.map fst (flatten (List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l));;


   (* let makePol l = List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l;; *)

   let polToList l = List.mapi (fun i x -> (x,i)) l;;
   
   let polToFlatList (p : polynomial) = (p : R.element list);;
   
   let flatListToPol (p : polynomial) = (p : coeff list);;
   
   let rec add (p1 : polynomial) (p2 : polynomial) = match (p1,p2) with
    |([],p2) -> p2
     |(p1,[]) -> p1
     |(a::t1,c::t2) ->
       let u = (R.add a c) in
       (u)::(add t1 t2)
	 
  let rec make_n_zeros = function
    | 0 -> []
    | k -> (R.zero)::(make_n_zeros (k-1));;

  let mul_const (const : R.element) (p : polynomial) =
    match R.eqZero(const) with
    | true -> []
    | false -> 
      let rec aux res = function
	| [] -> res
	| a::t -> aux ((R.mul a const)::res) t
      in List.rev (aux [] p);;

(* multiply p by cons * (x**n) *)
  let shiftCons (p : polynomial) n const =
        match R.eqZero(const) with
      | true -> []
      | false ->
	match p with
	| [] -> []
        | a::t -> (make_n_zeros n)@(mul_const const (a::t));;
	  
            
  (* let shift p n = shiftCons p n R.one *)

  let shift p n =
    let rec aux res = function
      | 0 -> res
      | k -> aux ((R.zero)::res) (k-1)
    in aux p n;;

  let intmul x p = shiftCons p 0 (R.injection x)

  let neg p = shiftCons p 0 (R.neg R.one)

  let sub p1 p2 = add p1 (neg p2)
  
    (* naive for now, if it becomes a bottleneck this will have to be addressed *)
  let mul p1 p2 = 
    let n1 = List.length p1 in
    let n2 = List.length p2 in
    let resAr = Array.make (n1 + n2 - 1) R.zero in
    for i = 0 to (n1-1) do
      for j = 0 to (n2-1) do
	let k1 = abs (i - j) in
	let k2 = (i+j) in
	assert(k1 <= n1+n2-2 && k2 <= n1+n2-2);
	let newval = R.div ((R.mul (List.nth p1 i) (List.nth p2 j))) (R.injection 2) in
	resAr.(k1) <- R.add resAr.(k1) newval;
	resAr.(k2) <- R.add resAr.(k2) newval
      done
    done;
    Array.to_list resAr;;

  let powerToString var n =
    if n = 0 then "1"
    else
      if n = 1 then var
      else
        ("T_"^(soi n)^"("^var^")")

  let rec monomialToString var a n =
    if (R.eqOne a) then
      powerToString var n
    else
      (R.soe a)^" "^
        (
          if n = 0 then ""
          else if n=1 then var
          else (var^"^"^(soi n))
        )

  let polToString var (p : polynomial) = 
    let rec aux = function
      | [] -> "0\n"
      | [(a,b)] -> (monomialToString var a b)^"\n"
      | (a,b)::t -> (monomialToString var a b)^" + "^(aux t)
    in aux (List.mapi (fun i x -> (x,i)) p);;

  let normal p = clean p;;

  let eq p1 p2 = normal(p1) = normal(p2)

  let eval_clenshaw p x (i : intervalle) =
    let (a,b) = i in
    let (a,b) = (R.floatInj a,R.floatInj b) in
    let n = degree p in
    let bRec = Array.make (n+3) R.zero in
    let two = R.injection 2 in
    let coeffSk = R.div (R.mul two (R.sub (R.sub (R.mul two x) b) a)) (R.sub b a) in
    for k = n downto 0 do
      bRec.(k) <- R.sub 
	(R.add (List.nth p k) 
	   (R.mul coeffSk bRec.(k+1))) bRec.(k+2) 
    done;
    R.sub bRec.(0) (R.mul coeffSk bRec.(1));;

  let eval p x = eval_clenshaw p x defInt

  let rec exp p n = match n with
    | 0 -> onePol
    | _ -> if n < 0 then raise(NegativePowerOfPol)
      else
        let m = n/2 in
        let p1 = exp p m in
        ps (polToString "x" p1);
        match n mod 2 with
        |0 -> mul p1 p1
        |_ -> mul (mul p1 p1) p;;
  
  let primitive p =
    let n = degree p in 
    let resAr = Array.make (n+2) R.zero in
    let two = R.injection 2 in
    let get p i = 
      if (0 <= i && i <= n) then List.nth p i else R.zero in
    for i = 1 to (n+1) do
      resAr.(i) <- R.div (R.sub (get p (i-1)) (get p (i+1))) (R.mul two (R.injection i))
    done;
      Array.to_list resAr;;
    
	     
end;;


















(* module QuasiRingToPoly = (PolyOfQuasiRing : POLYNOMIAL);; *)

module PolyInt = PolyOfQuasiRing(IntRing);;

(* module PolyIsRing = *)
(*   functor (Poly : POLYNOMIALSIG) ->     *)
(* struct *)
(*       type element = Poly.polynomial *)
(*       let normal = Poly.normal *)
(*       let zero = Poly.zeroPol *)
(*       let one = Poly.onePol *)
(*       let eq = Poly.eq *)
(*       let eqZero p = (Poly.normal(p) = Poly.zeroPol) *)
(*       let eqOne p = (Poly.normal(p) = Poly.onePol) *)
(*       let add = Poly.add *)
(*       let sub = Poly.sub *)
(*       let neg = Poly.neg *)
(*       let mul = Poly.mul *)
(*       let exp = makeExp one mul *)
(*       let divides p1 p2 = false (\* best until Euclidean is programmed, if needed *\) *)
(*       let div p1 p2 = p1 (\* not intended to be used *\) *)
(*       let injection (x:int) = Poly.intmul x one *)
(*       let intmul x (p:element) = Poly.intmul x p *)
(*       let soe = Poly.polToString "x" *)
(* end;; *)

(* module PolyIntIsRing = PolyIsRing(PolyInt);; *)

(* module PolyPoly = RingToPoly(PolyIntIsRing);; *)

(* interval polynomials *)

module IntervalPoly = PolyOfQuasiRing(IntervalQuasiRing);;
module IntervalFlatPoly = PolyFlatOfQuasiRing(IntervalQuasiRing);;
module IntervalChebFlatPoly = ChebFlatPolyOfQuasiRing(IntervalQuasiRing);;

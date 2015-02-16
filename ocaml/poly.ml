open Error
open Printing
open Int
open Semiring
open Basicdefs

module type POLYNOMIALSIG =
sig
  type monomial
  type polynomial
  type coeff
  val coeffInjection : int -> coeff
  val zeroPol : polynomial
  val onePol : polynomial
  val degree : polynomial -> int
  val makePol : (coeff*int) list -> polynomial
  val polToList : polynomial -> (coeff*int) list
  val add : polynomial -> polynomial -> polynomial
  val mul : polynomial -> polynomial -> polynomial
  val sub : polynomial -> polynomial -> polynomial
  val neg : polynomial -> polynomial
  val exp : polynomial -> int -> polynomial
  val polToString : string -> polynomial -> string
  val normal : polynomial -> polynomial
  val eq : polynomial -> polynomial -> bool
  val shiftCons : polynomial -> int -> coeff -> polynomial
  val intmul :  int -> polynomial -> polynomial
end;;

module PolyOfSemiRing (R : SEMIRING) : (POLYNOMIALSIG with type coeff = R.element) =
struct
  type coeff = R.element
  
  type monomial = R.element*int
  
  type polynomial = monomial list   (* (coeff,deg) in increasing degree order, no zero coeffs (sparse polynomials)*)
  
  let coeffInjection (x:int) = R.injection x 

  let (zeroPol:polynomial) = []
  
  let (onePol:polynomial) = [(R.one,0)]
  
  let makePol x = x
  
  let degree p = List.fold_right (fun (x,y) e -> max y e) p (-1)
  
(* in these two functions we sort coefficients to avoid any unpleasant effects *)
  let makePol l = List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l;;
  let polToList l = List.sort (fun (_,x) (_,y) -> Pervasives.compare x y) l;;

  let rec add p1 p2 = match (p1,p2) with
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
  
  let rec mul p1 p2 = match (p1,p2) with
    |([],p2) -> []
    |(p1,[]) -> []
    |((a,b)::t1,p2) -> add (shiftCons p2 b a) (mul t1 p2)

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

(* module SemiRingToPoly = (PolyOfSemiRing : POLYNOMIAL);; *)

module PolyInt = PolyOfSemiRing(IntRing);;

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

module IntervalPoly = PolyOfSemiRing(IntervalSemiRing);;

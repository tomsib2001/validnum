(* attempt to formalize taylor models *)

open Basicdefs;;
open Poly;;
open Error;;
open Printing;;
open Reification;;

let mI = makeIntervalle;;
let zero = IntervalQuasiRing.zero;;
let one = IntervalQuasiRing.one;;


module PolI = IntervalFlatPoly;;

type taylorModel = PolI.polynomial * intervalle;;

let pol (mf : taylorModel) = fst mf;;
let error (mf : taylorModel) = snd mf;;

let taylorModelToString ((pol,err) : taylorModel) = 
  let sPol = PolI.polToString "x" pol and
      sErr = interval_to_string err in
  "("^sPol^" , "^sErr^", size = "^(soi (PolI.size pol))^")";;

let size (tm : taylorModel) = PolI.degree (fst tm);;

(* computes a valid polynomial bound on the polynomial represented by the sequence l on the interval i - x0  *)
let computeBound (l : PolI.polynomial) x0 i =
  let x = (iSub i x0) in
  (* assert(Basicdefs.contient x 0.); *)
  let rec aux res = function
    | [] -> res
    | h::t -> aux (iPlus (iMult res x) h) t
  in aux zero (List.rev (PolI.polToFlatList l));;

PolI.polToFlatList (PolI.makePol ([one,0;one,2]));;
computeBound (PolI.makePol ([one,0;one,2])) (thin 0.5) (0.,1.);;

let tm_const (c : intervalle) n = 
  let rec aux res = function
    | 0 -> (c,0)::res
    | k -> aux ((thin 0.,k)::res) (k-1)
  in ((PolI.makePol (aux [] n),thin 0.) : taylorModel);;

(* a small test *)
(* let tcst = tm_const (thin 1.) 3;; *)
(* PolI.polToList (fst tcst);; *)

let tm_var i x0 n =
  let a0 = (x0,0) in
  let a1 = (one,1) in
  let rec aux res = function
    | 0 -> a0::res
    | 1 -> a0::a1::res
    | k -> aux ((zero,k)::res) (k-1)
  in
  let delta = if n=0 then (iSub i x0) else zero in
  ((PolI.makePol (aux [] n),delta) : taylorModel);;

(* a small test *)
let tvar = tm_var zero zero 5;;
PolI.polToList (fst tvar);;
let tvar = tm_var (0.,1.) zero 0;;
PolI.polToList (fst tvar);;

let flatten p = 
  if p = [] then [] else
  let rec aux res = function
    | [] -> res
    | [a,b] -> (a,b)::res
    | (a,b)::(c,d)::t -> if d < b then failwith "unsorted polynomial" else if d = (b+1) then aux ((a,b)::res) ((c,d)::t) else (* b < d *)
	aux ((a,b)::res) ((thin 0.,b+1)::(c,d)::t)
  in let p1 = match (List.hd p) with (* ok because we've ruled out p = [] *)
  | (_,0) -> p
  | (_,_) -> (zero,0)::p
  in List.rev (aux [] p1);;


let tm_add (mf : taylorModel) (mg : taylorModel) n = 
  let polf = flatten (PolI.polToList (fst mf)) 
  and polg = flatten (PolI.polToList (fst mg)) in
  let l1 = List.length polf 
  and l2 = List.length polg in
  if l1 <> l2 then failwith (String.concat " " [soi l1; "and";soi l2; "are not the same sizes"; "\nhere are the taylor models : mf :"; taylorModelToString mf; "\nand mg : " ;taylorModelToString mg]) else
    let rec aux_add res = function
      | ([],[]) -> res
      | ((a,i)::s,(b,j)::t) when i=j -> aux_add ((iPlus a b,i)::res) (s,t)
      | ((a,i)::s,(b,j)::t) when i < j -> aux_add ((a,i)::(b,j)::res) (s,t)
      | ((a,i)::s,(b,j)::t) when i > j -> aux_add ((b,j)::(a,i)::res) (s,t)
      | _ -> raise (IncompatibleSizes "in addition of taylor models")
    in let p = PolI.makePol(aux_add [] (polf,polg))
    and delta = iPlus (error mf) (error mg) in
       (p,delta)
;;

(* a small test *)
let tvar1 = tm_var zero zero 5;;
let tvar2 = tm_const one 5;;
let tadd = tm_add tvar1 tvar2 5;;
PolI.polToList (pol tadd);;

let cut_list n l = 
  let rec aux res = function
    | (li,0) -> res
    | (h::t,k) -> aux (h::res) (t,k-1)
    | _ -> failwith "this list is too short to be thus shaved"
  in List.rev(aux [] (l,n));;

let cut_list_first n l =   
  let rec aux = function
    | (li,0) -> li
    | (h::t,k) -> aux (t,k-1)
    | _ -> failwith "this list is too short to be thus shaved"
  in (aux (l,n));;


cut_list 5 [1;2;3;4;5;6;7];;
cut_list_first 5 [1;2;3;4;5;6;7];;

let tm_mul (mf : taylorModel) (mg : taylorModel) i x0 n =
  let pf = pol mf 
  and pg = pol mg in
  let deltaf = error mf in
  let deltag = error mg in
  (* assert (Basicdefs.contient deltaf 0.); *)
  (* assert (Basicdefs.contient deltag 0.); *)
  let res = PolI.mul pf pg in
  let d = PolI.shift (PolI.flatListToPol (cut_list_first (n+1) (PolI.polToFlatList res))) (n+1) in
  let b = computeBound d x0 i in
  (* Basicdefs.print_interval b; *)
  assert(Basicdefs.contient b 0.);
  let bf = computeBound pf x0 i in
  let bg = computeBound pg x0 i in
  let delta = 
    iPlus
      b (iPlus (iPlus (iMult (deltaf) bg) (iMult (deltag) (bf))) (iMult deltaf deltag)) in
  let m = cut_list (n+1) (PolI.polToFlatList res) in
  ((PolI.flatListToPol m),delta);;

let p1 = PolI.flatListToPol [zero;thin 0.5];;
PolI.polToString "x"  (p1);;
let p2 = PolI.flatListToPol [zero;thin 0.5];;
PolI.polToString "x"  (p2);;
let p3 = PolI.mul p1 p2;;
PolI.polToString "x"  (p3);;
(* PolI.polToFlatList (PolI.shift (PolI.flatListToPol (cut_list_first 0 (PolI.polToFlatList p3))) 1);; *)

(* a small test *)
let tvar1 = tm_var (0.,1.) one 5;;
PolI.polToList (pol tvar1);;
let tconst2 = tm_const (thin 0.5) 5;;
PolI.polToList (pol tconst2);;
let tmul = tm_mul tvar1 tconst2 (0.,1.) (thin 0.) 5;;
PolI.polToList (pol tmul);;
error tmul;;

flatten [(one,3);(one,15)];;

let tm_zero n = tm_const zero n

let polynomialEvaluation p mf i x0 n =
  let l = flatten (PolI.polToList p) in
  let rec horner_aux (res : taylorModel) = function
    | [] -> res
    | (a,b)::t -> 
      let m1 = tm_mul res mf i x0 n in
      let m2 = tm_add m1 (tm_const a n) n
      in horner_aux m2 t
  in horner_aux (tm_zero n) (List.rev l);;


let polx2 =  (PolI.makePol (flatten [one,18]));;
PolI.polToList polx2;;


(* #trace tm_mul;; *)

let (p,err) = polynomialEvaluation polx2 tvar2 (0.,1.) zero 10;;
PolI.polToList p,err;;

let tm_comp i x0 mf n (g : 'a elemFun) 
    (make_mg : (* x0  *)intervalle -> (* i *) intervalle -> int -> taylorModel) 
    =
  let pf = pol mf 
  and deltaf = error mf in
  let bf = computeBound pf x0 i in
  let lf = (PolI.polToFlatList pf) in
  let (polg,errg) = make_mg (List.hd lf) (iPlus bf deltaf) n in
  let m1 = (PolI.flatListToPol (zero::(List.tl lf)),deltaf) in
  let c = polynomialEvaluation polg m1 i x0 n in
  let m = (c,iPlus (error c) deltaf) in
  m
;;

(* I.add prec (Imul (Isub X X0) (RPA.error Mf)) ((I.add prec (Pol.peval prec R (Isub X0 X0)) ) (Imul (Isub X0 X0) (RPA.error Mf))). *)
let tm_int i x0 mf = 
  let pf = pol mf 
  and errf = error mf in
  let primPf = PolI.primitive pf in
  let intErr = List.fold_right iPlus 
    [
      iMult (iSub i x0) errf;
      PolI.eval primPf (iSub x0 x0);
      iMult (iSub x0 x0) errf
    ]
    zero
  in
  (primPf,intErr);;

let tm_neg mf =
  let (p,err) = mf in
  (PolI.neg p,Basicdefs.iNeg err);;

let get_tm (const : 'a -> intervalle) (models : (string*taylorModel) list) i x0 n f = 
  let rec aux = function
  | Const (a : 'a) -> tm_const (const a) n
  | Var s -> (try
      List.assoc s models with
      | _ -> tm_var i x0 n) (* for now we assume that it must be the time variable *)
  | Plus (f1, f2) -> tm_add (aux f1) (aux f2) n
  | Sub (f1,f2) -> aux (Plus(f1,Neg f2))
  | Pow(f,j) -> polynomialEvaluation (PolI.makePol (flatten [one,j])) (aux f) i x0 n
  | Neg(f) -> tm_neg (aux f)
  | _ -> failwith "not implemented yet"
  in aux f
;;


let (p,e) = get_tm (fun x -> x) []  (0.,1.) zero 10 (Pow(Plus(Const one,Var "x"),5));;
PolI.polToFlatList p;;
e;;

(* let (p,e) = tm_int (0.,1.) zero (tm_var (0.,1.) zero 5);; *)
(* let (p1,e1) = tm_int (0.,1.) zero (p,e);; *)
(* PolI.polToFlatList p;; *)
(* PolI.polToFlatList p1;; *)


type solution = taylorModel list;; (* the type of (candidate) solutions to differential equations *)
type 'a vfield = 'a elemFun list;; (* the type of vector fields from R n to R n *)
type 'a diffeq = intervalle * intervalle * 'a vfield  * string list *intervalle list (* X,X0, phi, [y_0,y_1 ..., y_n-1] , initConds *)

let vfield_to_string (a_to_string : 'a -> string) vf =
  String.concat " " (List.map ( elemFun_to_string a_to_string) vf);;

let diffeq_to_string (a_to_string : 'a -> string) (i,x0,phi,sVars,initConds) =
  let sI = interval_to_string i in
  let sX0 = interval_to_string x0 in
  let sPhi = vfield_to_string a_to_string phi in
  let sInit = List.mapi (fun i interv -> "f^("^(soi i)^") is initially "^(interval_to_string interv)^"\n") initConds in
  let order = List.length initConds in
  String.concat " "(List.concat [[" X = ";sI];[" X0 = ";sX0];["f^(";(soi order);") = ";sPhi;"\n"];sInit]);; 


(* fields for basic functions *)
let (sinField : intervalle vfield) = [Var "x1"; Neg (Var "x0")] (* diff. eq for sin: x'' = - x *)
let (expField : intervalle vfield) = [Var "x"];;

(* diffeqs for basic functions *)
let sinEq = ((0.,0.99),zero,sinField,["x0";"x1"],[zero;one] : 'a diffeq);;
let cosEq = ((0.,1.),zero,sinField,["x0";"x1"],[one;zero] : 'a diffeq);;
let expEq = ((0.,1.),zero,expField,["x"],[one] : 'a diffeq);;

let applyField (yn : solution) (phi : intervalle vfield) (sVars : string list) i x0 n =
  let table = List.map2 (fun s m -> (s,m)) sVars yn in
  let toIntegrate = List.map (get_tm (fun x -> x) table i x0 n) phi in
  (* List.iter (fun x -> psn (taylorModelToString x); pn ()) toIntegrate; psn "breakpoint";pn(); *)
  toIntegrate;;

let picardOp (yn : solution) (initCond : intervalle list) (phi : 'a vfield) (sVars : string list) i x0 n =
  let toIntegrate = applyField yn phi sVars i x0 n in
  List.map2 (fun iC m -> tm_add (tm_const iC (n+1)) (tm_int i x0 m) (n+1)) initCond toIntegrate;;

let solution_to_string (s : solution) =
  String.concat " " (List.map (taylorModelToString) s);;


let computeBoundTM ((p,err) : taylorModel) i x0 =
  let preRes = PolI.eval p (iSub i x0) in
  iPlus preRes err;;
  

(* let n = 20;; *)
(* let i = (0.75,1.5);; *)
(* let x0 = (thin 0.75);; *)
(* let y0 = [tm_const (~-.1.,1.) n;tm_const (~-.1.,1.) n];; *)
(* psn (solution_to_string y0);; *)
(* let initCond = [thin (sin 0.75);thin (cos 0.75)];; *)
(* let y1 = picardOp y0 initCond sinField ["x0";"x1"] i x0 n;; *)
(* psn (solution_to_string y1);; *)
(* let y2 = picardOp y1 initCond sinField ["x0";"x1"] i x0 (n+1);; *)
(* psn (solution_to_string y2);; *)
(* let y3 = picardOp y2 initCond sinField ["x0";"x1"] i x0 (n+2);; *)
(* psn (solution_to_string y3);; *)
(* let y4 = picardOp y3 initCond sinField ["x0";"x1"] i x0 (n+3);; *)
(* psn (solution_to_string y4);; *)
(* let y5 = picardOp y4 initCond sinField ["x0";"x1"] i x0 (n+4);; *)
(* psn (solution_to_string y5);; *)

(* computeBoundTM (List.hd y5) (thin 1.5) x0;; *)
(* sin 1.5;; *)

(* let iter n its y0 = *)
(* let rec aux = function *)
(*   | (y,0) -> y *)
(*   | (y,k) -> let ynew = picardOp y initCond sinField ["x0";"x1"] i x0 (n+(its-k)) in aux (ynew,k-1) *)
(* in let res = aux (y0,its) *)
(*    in ((fst(List.hd res)),snd(List.hd res)) *)
(* ;; *)

(* let (l,e) = iter n 100 y0;; *)

(* computeBoundTM (l,e) (thin 1.5) x0;; *)

(* PolI.eval (PolI.flatListToPol l) (thin (0.5));; *)
(* PolI.polToString "x" (PolI.flatListToPol l);; *)

(* PolI.polToFlatList (fst(List.hd y5));; *)
(* snd(List.hd y5) *)

assert(subset (2.,3.) (1.,4.));;
assert(subset (1.,2.) (1.,2.));;
assert(not(subset(1.,4.) (2.,3.)));;
assert(not(subset(1.,4.) (2.,5.)));;
assert(not(subset(2.,4.) (1.,3.)));;


let solve ((i,x0,phi,sVars,initConds) : 'a diffeq) (y0 : solution) its n epsilon =
  
  (* psn ("in solve: attempting to solve diffeq "^(diffeq_to_string (interval_to_string) (i,x0,phi,sVars,initConds))); *)
  let dim = List.length phi in
  assert(List.length initConds = dim);
  assert(List.for_all2
  	   (fun (t : taylorModel) z ->
  	     let i1 =  (computeBoundTM z i x0) in
  	     let i2 =  (computeBoundTM t i x0) in
  	     subset
  	       i1
  	       i2)
  	   [List.hd y0]
  	   [List.hd (picardOp y0 initConds phi sVars i x0 n)]);
  let iter n its y0 =
    let rec aux = function
      | (y,0) -> psn "reached max iterations, WARNING!!"; y
      | (y,k) -> 
	let ynew = picardOp y initConds phi sVars i x0 (n+(its-k))
	in let width = diam (computeBoundTM (List.hd ynew) (thin (snd i)) x0) in
	   if width < epsilon then ynew else
	     aux (ynew,k-1)
    in let res = aux (y0,its)
       in res
  in iter n its y0;;

let n = 10;;
let epsilon = 1e-10;;
let sinEq = ((0.75,1.3125),thin 0.75,sinField,["x0";"x1"],[thin(sin 0.75);thin(cos 0.75)] : 'a diffeq);;
let tL = solve sinEq [tm_const (~-.2.,2.) n;tm_const (~-.2.,2.) n] 10 n epsilon;;
psn "\n\n\n";;
List.iter (fun (p,e) -> psn (taylorModelToString (p,e))) tL;;

let (p,e) = List.hd tL;;

let value = 1.3125;;
psn (interval_to_string (computeBoundTM (p,e) (thin value) (thin 0.75)));;
psn (sof (sin value));;

(* we assume for now that x0 is at the extreme left of the interval i *)

let get_valid_initial_values
    ((i,x0,phi,sVars,initConds) : 'a diffeq)
    (y0 : solution)
    n
    fuel =
  let rec aux leftOver y0 i fuel = match fuel with
    | 0 -> failwith "couldn't manage to find fitting initial values and interval width"
    | k ->
      let b = (List.for_all2
		 (fun (t : taylorModel) z ->
		   let i1 =  (computeBoundTM z i x0) in
		   let i2 =  (computeBoundTM t i x0) in
		   subset
  		     i1
  		     i2)
		 [List.hd y0]
		 [List.hd (picardOp y0 initConds phi sVars i x0 n)]) in
      if b then ((y0,i),leftOver) else
	let y0_new = List.map (fun (p,x) ->
	  let m = midpoint x
	  and d = diam x in
	  (p,makeIntervalle (m -. d) (m +. d))) y0 in
	let (lx0,ux0) = x0 in
	let (li,ui) = i in
	let d2 = diam (ux0,ui) in
	let i_new =
	  makeIntervalle lx0 (ux0 +. d2 /. 2.) in
	let newLeftOver =
	match leftOver with
	| None -> (Some (makeIntervalle (ux0 +. d2 /. 2.) ui))
	| Some (_,ub) -> (Some (makeIntervalle (ux0 +. d2 /. 2.) (max ub ui))) in
	(aux newLeftOver y0_new i_new (fuel-1))
  in aux None y0 i fuel;;

let rec solve_bisect ((i,x0,phi,sVars,initConds) : 'a diffeq) (y0 : solution) its n maxAttempts epsilon =
  psn ("\n *************************in solve_bisect: attempting to solve diffeq "^(diffeq_to_string (interval_to_string) (i,x0,phi,sVars,initConds)));
    let dim = List.length phi in
    assert(List.length initConds = dim);
    let ((y0,i),optSequel) = get_valid_initial_values (i,x0,phi,sVars,initConds) y0 n maxAttempts in
    (* notice y0 and i may have changed *)
    let diffeq = (i,x0,phi,sVars,initConds) in
      psn ("\n  in solve_bisect: actually attempting to solve diffeq "^(diffeq_to_string (interval_to_string) (i,x0,phi,sVars,initConds)));
    let tL = solve diffeq y0 its n epsilon in (* a list of Taylor models *)
    match optSequel with
    | None -> [tL,i,x0]
    | Some (interv) ->
      psn ("finished solving on "^(interval_to_string i)^". Trying now on "^(interval_to_string interv));
      let new_x0 = thin(fst interv) in
      psn ("new x0 is "^(interval_to_string new_x0));
      let new_initConds = List.map (fun s -> computeBoundTM s new_x0 x0) tL in
      let sInit = List.mapi (fun i interv -> "f^("^(soi i)^") will now be initially "^(interval_to_string interv)^"\n") new_initConds in
      psn (String.concat " " sInit);
      let new_y0 =
	List.map
	  (fun i ->
	    let m = midpoint i in
	    tm_const (makeIntervalle (m -. 1.) (m +. 1.)) n)
	  new_initConds
      in
      psn " ---------------------    new call of solve_bisect";
      (tL,i,x0)::(solve_bisect (interv,new_x0,phi,sVars,new_initConds) new_y0 its n maxAttempts epsilon);;

let new_sinEq = ((0.,10.),zero,sinField,["x0";"x1"],[zero;one] : 'a diffeq);;

let n = 100;;
let its = 200;;
let epsilon = 1e-20;;

let t = solve_bisect new_sinEq [tm_const (~-.1.,1.) n;tm_const (~-.1.,1.) n] its n 500 epsilon;;

List.iter (fun (x,i,x0) -> psn (taylorModelToString (List.hd x)); psn ("i : "^(interval_to_string i)); psn ("x0: "^(interval_to_string x0))) t;;

List.iter (fun (x,i,x0) -> ps (sof (snd i)); ps "  --- "; ps (sof (sin (snd i))); ps " --- "; let value = (computeBoundTM (List.hd x) (thin (snd i)) x0) in ps (interval_to_string value);ps " of diameter "; psn (sof (diam value))) t;;

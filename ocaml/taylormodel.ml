(* attempt to formalize taylor models *)

open Basicdefs;;
open Poly;;
open Error;;
open Printing;;
open Reification;;

let mI = makeIntervalle;;
let zero = IntervalSemiRing.zero;;
let one = IntervalSemiRing.one;;


module PolI = IntervalFlatPoly;;

type taylorModel = PolI.polynomial * intervalle;;

let pol (mf : taylorModel) = fst mf;;
let error (mf : taylorModel) = snd mf;;

let size (tm : taylorModel) = PolI.degree (fst tm);;

(* computes a valid polynomial bound on the polynomial represented by the sequence l on the interval i - x0  *)
let computeBound (l : PolI.polynomial) x0 i =
  let x = (iSub i x0) in
  let rec aux res = function
    | [] -> res
    | h::t -> iPlus (iMult res x) h
  in aux zero (PolI.polToFlatList l);;

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

(* (\* probably incorrect *\) *)
(* let tm_pow i k x0 n = *)
(*   if n=0 then tm_const x0 n *)
(*   else if n=1 then tm_var i x0 n *)
(*   else (\* n>=2 *\) *)
(*     let a0 = (x0,0) in   *)
(*     let rec aux res = function *)
(*       | 0 -> a0::res *)
(*       | l -> let h = if l=k then (one,k) else (zero,l) in  *)
(* 	     aux (h::res) (l-1) *)
(*     in let delta = if n>=k then zero else (iSub (iPow i k) x0) *)
(*     in (PolI.makePol (aux [] n),thin 0.);; *)

(* (\* a small test *\) *)
(* let t3 = tm_pow (thin 1.) 7 (thin 1.) 5;; *)
(* PolI.polToList (fst t3);; *)

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
  if l1 <> l2 then failwith (String.concat " " [soi l1; "and";soi l2; "are not the same sizes"]) else
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

cut_list 5 [1;2;3;4;5;6;7];;

let tm_mul (mf : taylorModel) (mg : taylorModel) i x0 n =
  let pf = pol mf 
  and pg = pol mg in
  let deltaf = error mf in
  let deltag = error mg in
  let res = PolI.mul pf pg in
  let b = computeBound res x0 i in
  let bf = computeBound pf x0 i in
  let bg = computeBound pg x0 i in
  let delta = 
    iPlus
      b (iPlus (iPlus (iMult (deltaf) bg) (iMult (deltag) (bf))) (iMult deltaf deltag)) in
  let m = cut_list (n+1) (PolI.polToFlatList res) in
  ((PolI.flatListToPol m),delta);;

let p1 = PolI.flatListToPol [zero;one];;
PolI.polToString "x"  ( p1);;
let p2 = PolI.flatListToPol [zero;one];;
PolI.polToString "x"  ( p2);;
let p3 = PolI.mul p1 p2;;
PolI.polToString "x"  ( p3);;

(* a small test *)
let tvar1 = tm_var (0.,1.) one 5;;
PolI.polToList (pol tvar1);;
let tvar2 = tm_const (thin 0.5) 5;;
PolI.polToList (pol tvar2);;
let tmul = tm_mul tvar1 tvar2 (0.,1.) (thin 0.) 5;;
PolI.polToList (pol tmul);;

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

(* let tm_sin i x0 n = *)
(*   let rec aux = function *)
(*     | *)


(* let tm_base_div mf mg i x0 n = *)
(*   tm_mul *)

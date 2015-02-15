(* attempt to formalize taylor models *)

open Basicdefs;;
open Poly;;
open Error;;
open Printing;;

let mI = makeIntervalle;;
let zero = IntervalSemiRing.zero;;
let one = IntervalSemiRing.one;;


module PolI = IntervalPoly;;

type taylorModel = PolI.polynomial * intervalle;;

let pol (mf : taylorModel) = fst mf;;
let error (mf : taylorModel) = snd mf;;

let size (tm : taylorModel) = PolI.degree (fst tm);;

(* computes a valid polynomial bound on the polynomial represented by the sequence l on the interval i - x0  *)
let computeBound l x0 i =
  let rec aux res = function
    | [] -> res
    | h::t -> iPlus (iMult res (iSub i x0)) h
  in aux zero l;;

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
  in ((PolI.makePol (aux [] n),thin 0.) : taylorModel);;

(* a small test *)
(* let tvar = tm_var zero zero 5;; *)
(* PolI.polToList (fst tcst);; *)


let tm_add (mf : taylorModel) (mg : taylorModel) n = 
    let rec aux_add res = function
      | ([],[]) -> res
      | ((a,i)::s,(b,j)::t) when i=j -> aux_add ((iPlus a b,i)::res) (s,t)
      | ((a,i)::s,(b,j)::t) when i < j -> aux_add ((a,i)::(b,j)::res) (s,t)
      | ((a,i)::s,(b,j)::t) when i > j -> aux_add ((b,j)::(a,i)::res) (s,t)
      | _ -> raise (IncompatibleSizes "in addition of taylor models")
    in let p = PolI.makePol(aux_add [] (PolI.polToList (fst mf),PolI.polToList (fst mg)))
    and delta = iPlus (error mf) (error mg) in
       (p,delta)
;;

(* a small test *)
(* let tvar1 = tm_var zero zero 5;; *)
(* let tvar2 = tm_const one 5;; *)
(* let tadd = tm_add tvar1 tvar2 5;; *)
(* PolI.polToList (pol tadd);; *)

let cut_list n l = 
  let rec aux res = function
    | (li,0) -> res
    | (h::t,k) -> aux (h::res) (t,k-1)
    | _ -> failwith "this list is too short to be thus shaved"
  in List.rev(aux [] (l,n));;

cut_list 5 [1;2;3;4;5;6;7];;

let tm_mul (mf : taylorModel) (mg : taylorModel) i x0 n =
  let t = Array.make (2*n) (zero) in
  let lpolf = (PolI.polToList (pol mf)) in
  let lpolg = (PolI.polToList (pol mg)) in
  let deltaf = error mf in
  let deltag = error mg in
  let remf = ref lpolf  in
  for i = 0 to (n-1) do
    let (fk,k) = List.hd (!remf) in
    if k=i then
      begin
	let remg = ref lpolg in
	for j = 0 to (n-1) do
	  begin
	    let (gl,l) = List.hd (!remg) in
	    if l=j then
	      begin
		ps "i : "; pi i; psn " and j: "; pi j; ps "and i+j: "; pi (i+j); ps "\n";
		ps (interval_to_string (t.(i+j))); ps (interval_to_string fk); ps " "; ps (interval_to_string gl); ps "\n";
		t.(i+j) <- (iPlus (t.(i+j)) (iPlus fk gl));
		remg := List.tl (!remg)
	      end
	    else ()
	  end;
	done;
      remf := List.tl (!remf)
      end
    else
      ()
  done;
  let tlist = Array.to_list t in
  let b = computeBound tlist x0 i in
  let bf = computeBound (List.map fst lpolf) x0 i in
  let bg = computeBound (List.map fst lpolg) x0 i in
  let delta = 
    iPlus
      b (iPlus (iPlus (iMult (deltaf) bg) (iPlus (deltag) (bf))) (iMult deltaf deltag)) in
  let m = cut_list n tlist in
  (m,delta);;

(* a small test *)
let tvar1 = tm_var zero zero 5;;
PolI.polToList (pol tvar1);;
let tvar2 = tm_const one 5;;
PolI.polToList (pol tvar2);;
let tmul = tm_mul tvar1 tvar2 (0.,1.) (thin 0.) 5;;

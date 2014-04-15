open Basicdefs;;
open Integrals;;
open Reification;;

(* a first attempt made only on the exponential function. This will be in the initial commit but will probably disappear right after *)
let expFixPoint steps intprec init x0 x = 
  let (a0,b0) = x0 in
  let expx0 = (rd (exp a0),ru (exp b0)) in
  let rec aux = function
    | 0 -> fun x -> init
    | k -> 
      print_int k; print_string " ième étape\n";
      let prediExp = aux (k-1) in
      fun x ->iPlus expx0 (integralIntBounds prediExp intprec (x0) (iPlus x0 x))
  in  aux steps x;;



let fixpointNonLin steps intprec (x0 : intervalle) (y0 : intervalle list) (valinit : (intervalle -> intervalle) list) (f : (intervalle -> intervalle) list -> ((intervalle  -> intervalle) list)) =
(* X' = f (X) *)
  let rec aux = function
    | 0 -> valinit
    | k -> let prediF = aux (k-1) in
	   let aIntegrer = f prediF in
	   List.map2 (fun y z -> (fun x1 -> let res = iPlus y (integralIntBounds z intprec (x0) (iPlus x0 x1)) in res)) y0 aIntegrer in aux steps;;



(* Simple enclosure methods *)

let estimateWithConst t0 t1 phi x0 z0 = (* we assume z0 is a constant interval here *)
  iPlus x0 (iMult (t0,t1) (phi t0 t1 z0));;

let estimate t0 t1 phi x0 z0 = (* we assume z0 is an interval extension of our solution *)
  iPlus x0 (iMult (t0,t1) (phi t0 t1 (z0 t0 t1)));;



(* now a method to split an interval into small intervals *)
let rec clean = function
  | [] -> []
  | h1::h2::t -> if h1=h2 then h1::(clean t) else h1::(clean (h2::t))
  | [h] -> [h];;

let rec makeList x y depth = 
  let rec aux x y = function
  | 0 -> [x]
  | k -> let m = midpoint (x,y) in 
	 (makeList x m (k-1))@(makeList m y (k-1))
  in clean( List.rev(y::(List.rev(aux x y depth))))
;;



(* a function to get an enclosure without ta *)

let get_enclosure t0 t1 nb phi x0 z0 =  
  let l = (makeList t0 t1 nb) in
  let rec aux xlow xhigh tt0 = function
    | [] -> (xlow,xhigh)
    | tt1::tail -> 
      let x1 = estimate tt0 tt1 phi (thin xlow) z0 in 
      let x2 = if xlow=xhigh then x1 else estimate tt0 tt1 phi (thin xhigh) z0 in 
      aux (fst x1) (snd x2) tt1 (tail)
  in aux (fst x0) (snd x0) t0 l;;



let applyRec plus mult zero recrel l = 
  let rec head = function
    | ([],[]) -> zero
    | (a::t,fk::frem) -> plus (mult a fk) (head (t,frem))
    | _ -> failwith "Bad recurrence"
  in head (recrel,l);;


let fixpointLin steps intprec x0 y0 valinit recrel =
  (* x0 est le point en lequel on a les conditions initiales y0 sur les dérivées successives (d'ordre 0 jusqu'à (n-1)) *)
  let plus f1 f2 = fun x -> iPlus (f1 x) (f2 x) in
  let mult a f2 = fun x -> iMult (thin a) (f2 x) in
  let zero = fun x -> thin 0. in
  let rec aux = function
    | 0 -> valinit (* une liste de fonctions *)
    | k -> let prediF = aux (k-1) in (* une liste de fonctions *)
	   let aIntegrer = 
	     (match prediF with 
	       | h::t -> let nSub1 = (applyRec plus mult zero recrel prediF) in List.rev (nSub1::(List.rev t))
	       | _ -> failwith "Error in recurrence in fixpointLin")
	   in
	   List.map2 (fun y z -> fun x1 -> iPlus (thin y) (integralIntBounds z intprec (x0) x1)) y0 aIntegrer in  aux steps;; (* ATTENTION, x1 était x0 + x1c *)


let makeIfunFromDiffEq steps intprec x0 y0 valinit recrel x =
  let l = fixpointLin steps intprec x0 y0 valinit recrel in
  match l with
    | h::t -> (h x)
    | _ -> failwith "never happens";;


(* nouvelle tentative de découpage *)
let estimateSolCut t0  steps intprec recrel (y0 : float list) (valinit: (intervalle -> intervalle) list) (f: intervalle -> intervalle) l =   
  let rec aux (x: intervalle) (t0:float) = function
    | [] -> x
    | t2::t -> 
      let f = fun xx ->  makeIfunFromDiffEq steps intprec (thin t0) [(xx : float)] valinit recrel (t0,t2) in
      let low = f ((fst x)) in
      let up = f ( (snd x)) in
      let xnew = (fst low,snd up) in
      aux xnew t2 t
  in aux (thin (List.hd (y0))) t0 (List.tl(l));;

let unListFun  = function | [g] -> fun x -> g x | _ -> failwith "not planned";;

let fixpointNonLinDim1 steps intprec (x0:intervalle) (y0:intervalle) (valinit : intervalle -> intervalle) (f : (intervalle -> intervalle) -> (intervalle -> intervalle)) = unListFun (fixpointNonLin steps intprec x0 [y0] [valinit] (fun l -> [f (List.hd l)]));;

(* ce qui suit à l'air de marcher en toute dimension mais ne marche qu'en dimension 1 *)
let estimateSolCutNonLin t0 steps intprec (y0: intervalle ) (valinit : (intervalle -> intervalle) ) (f : (intervalle -> intervalle) -> ((intervalle  -> intervalle))) l =
  let rec aux (x:intervalle) (t1:float) = function
    | [] -> x
    | t2::t -> 
      let f1 = fun (xx : float) -> fixpointNonLinDim1 steps intprec (thin t1) (thin xx) valinit f in
      let low = f1 (fst x) (t2,t2) in
      let up = f1 (snd x) (t2,t2) in
      let xnew1 =  fst low in
      let xnew2 =  snd up in
      let xnew = (xnew1,xnew2) in
      aux xnew t2 t
  in aux y0 t0 (List.tl l);;


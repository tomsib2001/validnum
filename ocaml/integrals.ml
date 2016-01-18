open Basicdefs;;
open Taylormodel;;
open Reification;;
(* computing an enclosure of the integral of a function f from the intervals to the intervals, with floating bounds *)

(* let rec int_iFun_eps eps iF i = *)
(*   let thin  t = (t,t) in *)
(*   match i with *)
(*     | (x,y) when y < x-> iNeg (int_iFun_eps eps iF (y,x)) *)
(*     | (x,y) -> *)
(*       let temp = (iF i) in *)
(*       let estimInt = iMult (thin (y -. x)) temp in *)
(*       if (diam estimInt) <= eps then estimInt else *)
(* 	let midpoint = ((x +. y)/.2.) in *)
(* 	let i1 = int_iFun_eps (eps/.2.) iF (x, midpoint) in *)
(* 	let i2 = int_iFun_eps (eps /. 2.) iF (midpoint, y) in *)
(* 	iPlus i1 i2;; *)


(* (\* slightly optimised version *\) *)
(* let rec int_iFun_eps2 eps iF  i = *)
(*   let thin  t = (t,t) in *)
(*   match i with *)
(*     | (x, y) when y < x-> int_iFun_eps2 eps iF  (y,x) *)
(*     | (x, y) ->  *)
(*       let temp = (iF i) in *)
(*       let estimInt = iMult (thin (y -. x)) temp in *)
(*       if (diam estimInt) <= eps then estimInt else *)
(* 	let midpoint = ((x +. y)/.2.) in *)
(* 	let i1 = int_iFun_eps2 (eps/.2.) iF (x, midpoint) in *)
(* 	let (l,r) = i1 in *)
(* 	let i2 = int_iFun_eps2 (eps -. (r -. l)) iF (midpoint, y) in *)
(* 	iPlus i1 i2;; *)


(* again, a computation of the integral of an interval to interval function, but this time without a specification of the precision we wish to attain *)
let int_iFun iF f n depth a b =
  let rec aux depth a b res =
    if depth = 0 then 
      iPlus res (iMult (thin (b -. a)) (iF (a,b))) 
    else
      let midpoint = ((a +. b)/.2.) in
      aux (depth-1) midpoint b (aux (depth-1) a midpoint res)
  in aux depth a b (thin 0.);;

(* and now an integral with taylor models at leaves *)
let int_iFun_tm soc iF f n depth a b  =
  let rec aux depth a b res =
    if depth = 0 then
      let i = (makeIntervalle a b) in
      let x0 = (thin (midpoint i)) in
      let tm1 = get_tm (fun c -> makeIntervalle c c) soc [] i (thin (midpoint i)) n f in
      let (pol,errP) = tm_int i x0 tm1 in
      (* Printf.printf "%s" (PolI.polToString "x" pol); *)
      let eval interv = PolI.eval pol (iSub interv x0) in
      iPlus res (iPlus (iSub (eval (thin b)) (eval (thin a))) (iMult (thin (b -. a)) errP))
    else
      let midpoint = ((a +. b)/.2.) in
      aux (depth-1) midpoint b (aux (depth-1) a midpoint res)
  in aux depth a b (thin 0.);;

let int_iFun_tm soc iF f n depth a b  =
  let rec aux depth maa b res =
    if depth = 0 then
      let i = (makeIntervalle a b) in
      let x0 = (thin (midpoint i)) in
      let (pol,err) = get_tm (fun c -> makeIntervalle c c) soc [] i (thin a) n f in
      (* Printf.printf "%s" (PolI.polToString "x" pol); *)
      let pol_prim = PolI.primitive pol in
      let eval interv = PolI.eval (pol_prim) (iSub interv x0) in
      iPlus res (iPlus (iSub (eval (thin b)) (eval (thin a)) ) (iMult (thin (b -. a)) err))
    else
      let midpoint = ((a +. b)/.2.) in
      aux (depth-1) midpoint b (aux (depth-1) a midpoint res)
  in aux depth a b (thin 0.);;



(* now we integrate with interval bounds. For a formal justification of what is done here, see the latex file *)

let integralIntBounds_param int_iFun iF f n depth (a,b) (c,d) =
  (* assert(iLeq (a,b) (c,d)); *)
  (* let sab = (abs_float (b -. a)) *. abs_max (iF (a,b)) and *)
  (*     scd = (abs_float (d -. c)) *. abs_max (iF (c,d)) in *)
  let sab = iMult (thin (abs_float (b -. a))) (convex_hull2 (thin 0.) (iF (a,b))) and
      scd = iMult (thin (abs_float (d -. c))) (convex_hull2 (thin 0.) (iF (c,d))) in
  let res = 
    iPlus sab
      (iPlus (int_iFun iF f n depth b c) scd) in
  (* let overestimation = (iMult (iSub (c,d) (a,b)) (iF (a,d))) in *)
  (* assert(subset res overestimation); *) res (* this assertion is false, left as comment to remind everyone *)
;;

let integralIntBounds iF depth i1 i2 = integralIntBounds_param int_iFun iF (Var "notaFunction") (-1) depth i1 i2;; 

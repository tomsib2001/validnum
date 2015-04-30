open Basicdefs;;

(* computing an enclosure of the integral of a function f from the intervals to the intervals, with floating bounds *)

let rec int_iFun_eps eps iF i =
  let thin  t = (t,t) in
  match i with
    | (x,y) when y < x-> iNeg (int_iFun_eps eps iF (y,x))
    | (x,y) ->
      let temp = (iF i) in
      let estimInt = iMult (thin (y -. x)) temp in
      if (diam estimInt) <= eps then estimInt else
	let midpoint = ((x +. y)/.2.) in
	let i1 = int_iFun_eps (eps/.2.) iF (x, midpoint) in
	let i2 = int_iFun_eps (eps /. 2.) iF (midpoint, y) in
	iPlus i1 i2;;


(* slightly optimised version *)
let rec int_iFun_eps2 eps iF  i =
  let thin  t = (t,t) in
  match i with
    | (x, y) when y < x-> int_iFun_eps2 eps iF  (y,x)
    | (x, y) -> 
      let temp = (iF i) in
      let estimInt = iMult (thin (y -. x)) temp in
      if (diam estimInt) <= eps then estimInt else
	let midpoint = ((x +. y)/.2.) in
	let i1 = int_iFun_eps2 (eps/.2.) iF (x, midpoint) in
	let (l,r) = i1 in
	let i2 = int_iFun_eps2 (eps -. (r -. l)) iF (midpoint, y) in
	iPlus i1 i2;;


(* again, a computation of the integral of an interval to interval function, but this time without a specification of the precision we wish to attain *)
let int_iFun iF depth a b =
  let rec aux depth a b res =
    if depth = 0 then 
      iPlus res (iMult (thin (b -. a)) (iF (a,b))) 
    else
      let midpoint = ((a +. b)/.2.) in
      aux (depth-1) midpoint b (aux (depth-1) a midpoint res)
  in aux depth a b (thin 0.);;


(* now we integrate with interval bounds. For a formal justification of what is done here, see the latex file *)

let integralIntBounds iF depth (a,b) (c,d) =
  (* assert(iLeq (a,b) (c,d)); *)
  let sab = (abs_float (b -. a)) *. abs_max (iF (a,b)) and
      scd = (abs_float (d -. c)) *. abs_max (iF (c,d)) in
  let res = 
    iPlus (neg sab,sab)
      (iPlus (int_iFun iF depth b c) (neg scd,scd)) in
  (* let overestimation = (iMult (iSub (c,d) (a,b)) (iF (a,d))) in *)
  (* assert(subset res overestimation); *) res (* this assertion is false, left as comment to remind everyone *)
;;

open Basicdefs;;
open Printing;;
open Reification;;
open Taylor;; (* TODO: move subs from Taylor to reification *)
open Integrals;;

let const (i : int) = thin(float_of_int i);;


let c1000 = const 1000;;
let c996 = const 996;;
let five = const 5;;
let one = const 1;;
let two = const 2;;
let three = const 3;;
let half = thin 0.5;;
let c998 = const 998;;
 
exception Reject;;
exception NoResult;;
exception Continue;;

let reject () = raise Reject;;
let noresult () = raise NoResult;;

let iSqrt x =
  (* ps "call to iSqrt on "; *)
  (* print_interval x; *)
  let newx = intersection x (0.,infinity) in
  let res = iSqrt newx in
  (* ps  " and result is "; *)
  (* print_interval res; *)
  (* pn (); *)
  res;;

(* square function *)
let iSqr x = iPow x 2;;


(* function Compare from the paper *)

let compare x y (a : intervalle) (b : intervalle) = 
  if lt x y then a else
    if gt x y then b else
      convex_hull2 a b;;

(* function avgwt from the paper *)
let avgwt x y w = 
  assert(lt x y);
  let z =  ((1. -. w) *. (top x)) +. (w *. (bot y)) in 
  z;;

let (dx_sym : intervalle elemFun) =
  let t = Sub(Mult(Var "H",Pow(Var "Y",2)),Var "F") in
  Div(t,Sqrt(Mult(Plus(Mult(Const two,Var "Y"),t),Sub((Mult(Const two,Var "Y"),t)))));;

print_string (elemFun_to_string interval_to_string dx_sym);;

let dx (* y *) h f =
  let pre_dx = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f] dx_sym in
  ((sym2iFunGen (fun x -> x) pre_dx) : intervalle -> intervalle);;

let (dxmin_sym : intervalle elemFun) = 
  let y = Plus(Var "Y_min",Pow(Var "Z",2)) in
  let t = Sub(Mult(Var "H",Pow(Var "y",2)),Var "f") in
  Div(Mult(Const two,t),Sqrt(
    Mult
      (Plus(Mult(Const two,Var "Y"),t),
       Sub(Sub(Const two,Mult(Var "H",Var "Y_min")),Mult(Var "Y",Var "H")))));;

print_string (elemFun_to_string interval_to_string dxmin_sym);;

let dxmin (* z *) h f ymin =   
  let pre_dxmin = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_min",ymin] dxmin_sym in
  sym2iFunGen (fun x -> x) pre_dxmin;;

let (dxmax_sym : intervalle elemFun) = 
  let y = Sub(Var "Y_min",Pow(Var "Z",2)) in
  let t = Sub(Mult(Var "H",Pow(Var "y",2)),Var "f") in
  Div(Mult(Const two,t),Sqrt(
    Mult(
      Plus(Mult(Const two,Var "Y"),t),
      Mult(
	Var "H",
	Plus(Var "Y",Var "Y_outermin")
      )
    )
  )
  );;

print_string (elemFun_to_string interval_to_string dxmax_sym);;

let dxmax (* z *) h f youtermin =   
  let pre_dxmax = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_outermin",youtermin] dxmax_sym in
  sym2iFunGen (fun x -> x) pre_dxmax;;

let dv_sym = Mult(Pow(Var "Y",2),dx_sym);;

print_string (elemFun_to_string interval_to_string dv_sym);;

let dv (* y *) h f = 
  let pre_dv = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f] dv_sym in
  sym2iFunGen (fun x -> x) pre_dv;;

let dvmin_sym = 
    Mult(
      Pow(
	Plus(
	  Var "Y_min",
	  Pow(
	    Var "Z",
	    2
	  )
	)
	  ,2),
    dxmin_sym
  );;

print_string (elemFun_to_string interval_to_string dvmin_sym);;

let dvmin (* z *) h f ymin = 
  let pre_dvmin = 
     List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_min",ymin] dvmin_sym in
  sym2iFunGen (fun x -> x) pre_dvmin;;  

let dvmax_sym = 
    Mult(
      Pow(
	Sub(
	  Var "Y_max",
	  Pow(
	    Var "Z",
	    2
	  )
	)
	  ,2),
      dxmax_sym
  );;

print_string (elemFun_to_string interval_to_string dvmax_sym);;

let dvmax (* z *) h f youtermin = 
  let pre_dvmax = 
     List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_outermin",youtermin] dvmax_sym in
  sym2iFunGen (fun x -> x) pre_dvmax;;


let check_rectangle (c1 : intervalle) (h0 : intervalle) idepth = 
  (* step 1 *)
  if (geq (iMult c1000 c1) c996) && (geq (iMult five h0) (one)) then
    reject ();
  (* step 2 *)
let hi = iSub two h0 in
let y1 = iSqrt (iSub one (iPow c1 2)) in
let fi = iSub
  (iMult (iSub hi one) (iPow y1 2))
  (iMult c1 (iMult y1 (iSqrt three))) in
let f0 = iNeg fi in
let c2 = intersection
  (convex_hull2 (iNeg c1) c1)
  (convex_hull2 (iNeg half) half) in
let t = 
  iSub
    (iDiv 
       (
	 iPlus (iMult (two) (iMult (iSub hi one) (fi))) three
       )
       (
	 iPlus three (iPow (iSub hi one) 2)
       )
    )
    (iSub one (iPow c1 2))
in 
if neq (iPlus (iPow c2 2) t) one then reject();

let y2 = iSqrt(intersection t (makeIntervalle 0. 1.)) in
let c2 = intersection c2 
  (iDiv
      (iSub (iMult (iSub hi one) (y2)) (iDiv fi y2))
      (iSqrt three)) in
if is_empty c2 then reject();
if leq c1 half && leq h0 
  (iSub
     one
     (iMult (iSqrt three) (iDiv c1 y1))
  )
then reject ();
(* psn "c2 : "; *)
(* print_interval c2; *)
(* pn (); *)
if diam c2 > 0.5 then noresult ();
let w_ends = 
  iPlus
    (iMult 
       (iPow (iSub one c1) 2)
       (iDiv
	  (iPlus two c1)
	  (three)
       )
    )
    (iMult 
       (iPow (iSub one c2) 2)
       (iDiv
	  (iPlus two c1)
	  (three)
       )
    ) in
let ymin = iDiv (iNeg fi) (iPlus one (iSqrt (iPlus one (iMult fi hi)))) in 
let ymax = iDiv (iPlus one (iSqrt (iPlus one (iMult f0 h0)))) (h0) in
let y = compare c1 (iDiv (iSqrt three) two) ymin y1 in
if lt (iMult y hi) (iNeg one) then
  (let r = iDiv one (iSub (iNeg hi) (iDiv one y)) in
  let w = iMult 
    (thin 2.5) 
    (iMult 
       (iPlus y (iDiv (iSqrt (three)) (two)))
       (iSqr r)
    ) in
  if lt w w_ends then reject());
let yleft = iSqrt (iDiv f0 h0) in
let yleft = if (lt ymin y2) && (lt yleft ymax) then iMax y1 yleft else raise NoResult in
let y4 = thin (avgwt yleft ymax 0.5) in
let z2 = iSqrt(iSub ymax y2) in
let z4 = iNeg (iSub ymax y4) in
if geq (iMult c1000 c1) (c998) then
  begin
    let t = (avgwt y1 y2 (1. /. 16.)) in
    let delta_i = 
      iPlus
	(iMult 
	   (iSub (thin t) y1) 
	   (thin (33. /. 16.)))
	(integralIntBounds (dx hi fi) idepth (thin t) y2) in
    let delta_0 = iMult (iNeg (iSub yleft y1)) (iSqrt three) in
    let t = avgwt yleft y4 (1. /. 16.) in
    let delta_0 = 
      iPlus 
	delta_0
	(integralIntBounds (dx h0 f0) idepth (thin t) y4) in
    if gt delta_0 delta_i then reject();
    let delta_0 = 
      iPlus
	delta_0
	(integralIntBounds (dxmax h0 f0 youtermin
) z4 z2)
    in
    if gt delta_0 delta_i then reject();
    if contient c1 1 then noresult();
  end;

raise Continue;


(* procedure to finish here *)
;;

let rec divideAndCheckRectangle y1 h0 idepth = 
  psn "entering divideAndCheckRectangle: ";
  ps "y1 : ";
  print_interval y1;
  ps "h0 : ";
  print_interval h0;
  let c1 = iSqrt (iSub one (iSqr y1)) in
  try check_rectangle c1 h0 idepth with
  | Reject -> true
  | _ ->
    let (y1a,y1b) = split y1 in
    let (h0a,h0b) = split h0 in
    (divideAndCheckRectangle y1a h0a idepth) 
    && (divideAndCheckRectangle y1a h0b idepth)
    && (divideAndCheckRectangle y1b h0a idepth)
    && (divideAndCheckRectangle y1b h0b idepth)

let main idepth = 
  let y1 = (0.,1.) in
  let h0 = (0.,10.) in
  if
  divideAndCheckRectangle y1 h0 idepth
  then
    print_string "all rejected"
  else
    print_string "finish writing your program";;

(* main();; *)

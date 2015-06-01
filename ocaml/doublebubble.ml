open Basicdefs;;
open Printing;;
open Reification;;
open Taylor;; (* TODO: move subs from Taylor to reification *)
open Integrals;;

let const (i : int) = thin(float_of_int i);;

let i1000 = const 1000;;
let i996 = const 996;;
let five = const 5;;
let one = const 1;;
let two = const 2;;
let three = const 3;;
let half = thin 0.5;;
let i998 = const 998;;

exception Reject;;
exception NoResult;;
exception Continue;;

let t = Array.make 9 0;;

let reject c1 h0 i = 
  Printf.printf "reject at step %d\n" i;
  t.(i-1) <- t.(i-1) + 1; raise Reject;;

let noresult () = raise NoResult;;

let print_step i = () ;;(* match i with *)
  (* | 1 -> psn "trying step 1.." *)
  (* | k -> psn ("failed at step "^(soi (i-1))^", attempting step "^(soi i)^"...");; *)

let iSqrt x =
  let newx = intersection x (0.,infinity) in
  let res = iSqrt newx in
  res;;

(* square function *)
let iSqr x = iPow x 2;;


(* function Compare from the paper *)

let compare x y (a : intervalle) (b : intervalle) = 
  if iLt x y then a else
    if iGt x y then b else
      convex_hull2 a b;;

(* function avgwt from the paper *)
let avgwt x y w = 
  assert(iLt x y);
  let z =  ((1. -. w) *. (top x)) +. (w *. (bot y)) in 
  z;;

let (dx_sym : intervalle elemFun) =
  let t = Sub(Mult(Var "H",Pow(Var "Y",2)),Var "F") in
  Div(t,Sqrt(Mult(Plus(Mult(Const two,Var "Y"),t),Sub((Mult(Const two,Var "Y"),t)))));;

psn "dx : ";;
psn (elemFun_to_string interval_to_string dx_sym);;

let dx (* y *) h f =
  let pre_dx = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f] dx_sym in
  ((sym2iFunGen (fun x -> x) pre_dx) : intervalle -> intervalle);;

let (dxmin_sym : intervalle elemFun) = 
  let y = Plus(Var "Y_min",Pow(Var "Z",2)) in
  let t = Sub(Mult(Var "H",Pow(y,2)),Var "F") in
  Div(Mult(Const two,t),Sqrt(
    Mult
      (Plus(Mult(Const two,y),t),
       Sub(Sub(Const two,Mult(Var "H",Var "Y_min")),Mult(y,Var "H")))));;

psn "dxmin : ";;
psn (elemFun_to_string interval_to_string dxmin_sym);;

let dxmin (* z *) h f ymin =   
  let pre_dxmin = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_min",ymin] dxmin_sym in
  sym2iFunGen (fun x -> x) pre_dxmin;;

let (dxmax_sym : intervalle elemFun) = 
  let y = Sub(Var "Y_max",Pow(Var "Z",2)) in
  let t = Sub(Mult(Var "H",Pow(y,2)),Var "F") in
  let youtermin = Div(
    Var "F",
    Plus(
      Const one,
      Sqrt(
	Plus(
	  Const one,
	  Mult(Var "F",Var "H")
	)
      )
    )
  ) in
  Div(Mult(Const two,t),Sqrt(
    Mult(
      Plus(Mult(Const two,y),t),
      Mult(
	Var "H",
	Plus(y,youtermin)
      )
    )
  )
  );;

psn "dxmax : ";;
psn (elemFun_to_string interval_to_string dxmax_sym);;

let dxmax (* z *) h f ymax =   
  let pre_dxmax = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_max",ymax] dxmax_sym in
  sym2iFunGen (fun x -> x) pre_dxmax;;

let dv_sym = Mult(Pow(Var "Y",2),dx_sym);;

psn "dv : ";;
psn (elemFun_to_string interval_to_string dv_sym);;

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

psn "dvmin : ";;
psn (elemFun_to_string interval_to_string dvmin_sym);;

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

psn "dvmax : ";;
psn (elemFun_to_string interval_to_string dvmax_sym);;

let dvmax (* z *) h f ymax = 
  let pre_dvmax = 
    List.fold_right (fun (x,y) z -> subs (Var x) (Const y) z) ["H",h;"F",f;"Y_max",ymax] dvmax_sym in
  sym2iFunGen (fun x -> x) pre_dvmax;;

let integralIntBounds dx idepth t y2 =
  let r = integralIntBounds dx idepth t y2 in
  print_interval_bis t; print_string " ";
  print_interval_bis y2; print_string " -> ";
  print_interval_bis r; pn ();
  r

let check_rectangle (c1 : intervalle) (h0 : intervalle) idepth = 
  print_interval_bis c1; pn ();
  print_interval_bis h0; pn ();
  (* step 1 *)

  print_step 1;
  if (iGeq (iMult i1000 c1) i996) && (iLeq (iMult five h0) (one)) then
    begin
      (* psn "reject at step 1"; *)
      (* print_interval_bis c1; pn (); *)
      (* print_interval_bis h0; pn(); *)
      reject c1 h0 1;
    end;
  (* step 2 *)
  
  print_step 2;
  let hi = iSub two h0 in
  let y1 = iSqrt (iSub one (iSqr c1)) in
  let sub_hi_one = (iSub hi one) in (* H-i - 1, reused many times *)
  let fi = iSub
    (iMult sub_hi_one (iPow y1 2))
    (iMult c1 (iMult y1 (iSqrt three))) in
  let f0 = iNeg fi in
  let c2 = intersection
    (convex_hull2 (iNeg c1) c1)
    (convex_hull2 (iNeg half) half) in
  let t = 
    iSub
      (iDiv 
	 (
	   iPlus (iMult (two) (iMult sub_hi_one (fi))) three
	 )
	 (
	   iPlus three (iSqr sub_hi_one)
	 )
      )
      (iSub one (iSqr c1))
  in 
  (* print_interval (iPlus (iPow c2 2) t); pn(); *)
  (* psn "value of t:"; *)
  (* print_interval_bis t; pn (); *)
  (* psn "at step 2 on c1,h0 : "; *)
  (* print_interval_bis c1; pn (); *)
  (* print_interval_bis h0; pn(); *)
  if iNeq (iPlus (iPow c2 2) t) one then
    begin
      (* psn "rejected"; *)
      reject c1 h0 2;
    end;

(* step 3 *)

  print_step 3;
  let y2 = iSqrt(intersection t (makeIntervalle 0. 1.)) in
  let c2 = intersection c2 
    (iDiv
       (iSub (iMult (iSub hi one) (y2)) (iDiv fi y2))
       (iSqrt three)) in
  if is_empty c2 then reject c1 h0 3;

(* step 4 *)

  print_step 4;
  if iLeq c1 half && iLeq h0 
    (iSub
       one
       (iMult (iSqrt three) (iDiv c1 y1))
    )
  then reject c1 h0 4;

(* step 5 *)

  print_step 5;
  if diam c2 > 0.5 then noresult ();

(* step 6 *)

  print_step 6;
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
	    (iPlus two c2)
	    (three)
	 )
      ) in
  psn "w_ends is";
  print_interval_bis w_ends; pn();
  let ymin = iDiv (iNeg fi) (iPlus one (iSqrt (iPlus one (iMult fi hi)))) in 
  let ymax = iDiv (iPlus one (iSqrt (iPlus one (iMult f0 h0)))) (h0) in
  let y = compare c1 (iDiv (iSqrt three) two) ymin y1 in
  if iLt (iMult y hi) (iNeg one) then
    (* (let r = iDiv one (iSub (iNeg hi) (iDiv one y)) in *)
    (let r = iDiv (iDiv (iSqrt (three)) (two)) (iSub (iNeg hi) (iDiv one y)) in
     let w = iMult 
       (thin 2.5) 
       (iMult 
	  (iPlus y (iMult r (iDiv (iSqrt (three)) (two))))
	  (iSqr r)
       ) in
     if iLt w w_ends then reject c1 h0 6);

(* step 7 *)

  print_step 7;
  let yleft = iSqrt (iDiv f0 h0) in
  let yleft = if (iLt ymin y2) && (iLt yleft ymax) then iMax y1 yleft else noresult() in
  let y4 = thin (avgwt yleft ymax (1. /. 16.)) in
  let z2 = iSqrt(iSub ymax y2) in
  let z4 = iNeg (iSqrt(iSub ymax y4)) in
  if iGeq (iMult i1000 c1) (i998) then
    begin
      let t = (avgwt y1 y2 (1. /. 2.)) in
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
      if iGt delta_0 delta_i then reject c1 h0 7;
      let delta_0 = 
	iPlus
	  delta_0
	  (integralIntBounds (dxmax h0 f0 ymax) idepth z4 z2)
      in
      if iGt delta_0 delta_i then reject c1 h0 7;
      if contient c1 1. then noresult();
    end;

(* step 8 *)

  print_step 8;
  assert (iLeq c1 (iDiv (iSqrt(three)) (two)) 
	  ||
	    iLeq y1 y2);  (* verify at step 8 in pseudocode page 43*)
  let t = iSqrt(iSub y1 ymin) in
  let z1 = compare c1 (iDiv (iSqrt(three)) (two)) (iNeg t) t in
  let z3 = iSqrt(iSub y2 ymin) in
  let delta_i = integralIntBounds (dxmin hi fi ymin) idepth z1 z3 in
  let delta_0 = integralIntBounds (dxmax h0 f0 ymax) idepth z4 z2 in
  if iLt delta_i delta_0 then reject c1 h0 8;
  psn "h0 is";
  print_interval_bis h0; pn();
  psn "f0 is";
  print_interval_bis f0; pn();
  psn "t is";
  print_interval_bis t; pn();
  psn "delta_0 is";
  print_interval_bis delta_0; pn();
  let delta_0 = 
    iPlus 
      delta_0 
      (integralIntBounds (dx h0 f0) idepth y1 y4) in
  if iNeq delta_i delta_0 then reject c1 h0 8;

(* step 9 *)

  print_step 9;
  let w_base = integralIntBounds (dvmin hi fi ymin) idepth z1 z3 in
  (* psn "w_base : "; *)
  (* print_interval w_base; pn(); *)
  let w_i = iPlus w_ends w_base in
  let i1 = (integralIntBounds (dv h0 f0) idepth y1 y4) in
  let i2 = (integralIntBounds (dvmax h0 f0 ymax) idepth z4 z2) in
  (* psn "i1 : "; *)
  (* print_interval i1; pn(); *)
  (* psn "i2 : "; *)
  (* print_interval i2; pn(); *)
  let w_0 = 
    iPlus
      (i1)
      (iSub
	 (i2)
	 w_base
      ) in
  psn "w_i is";
  print_interval_bis w_i; pn();
  psn "w_0 is";
  print_interval_bis w_0; pn();
  if iNeq w_i w_0 then reject c1 h0 9 else noresult();;


let rec divideAndCheckRectangle y1 h0 idepth fuel =
  (* psn "entering divideAndCheckRectangle: "; *)
  (* ps "y1 : "; *)
  (* print_interval y1; *)
  (* pn (); *)
  (* ps "h0 : "; *)
  (* print_interval h0; *)
  (* pn(); *)
  match fuel with
  | 0 -> failwith "reached max fuel. stopping"
  | k ->
    let c1 = iSqrt (iSub one (iSqr y1)) in
    (* psn "c1 : "; print_interval c1; pn(); *)
    (try check_rectangle c1 h0 idepth with
    | Reject -> true
    | NoResult ->
      let (y1a,y1b) = split y1 in
      let (h0a,h0b) = split h0 in
      (divideAndCheckRectangle y1a h0a idepth (k-1))
      && (divideAndCheckRectangle y1a h0b idepth (k-1))
      && (divideAndCheckRectangle y1b h0a idepth (k-1))
      && (divideAndCheckRectangle y1b h0b idepth (k-1))
    | e -> raise e)

let main idepth =
  let y1 = (0.,1.) in
  let h0 = (0.,10.) in
  if
    divideAndCheckRectangle y1 h0 idepth 15
  then
    let count = ref 0 in
    begin
      for i =1 to 9 do
	psn ((soi (t.(i-1)))^" rejected at step "^(soi i));
	count := !count + t.(i-1);
      done;
      psn ("total number of rectangles with integrals at depth "^(soi idepth)^": "^(soi !count));
      psn "all rejected"
    end
  else
    psn "we have a problem here";;

main 5;;


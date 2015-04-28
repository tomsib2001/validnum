open Basicdefs;;
open Printing;;

let const (i : int) = thin(float_of_int i);;


let c1000 = const 1000;;
let c996 = const 996;;
let five = const 5;;
let one = const 1;;
let two = const 2;;
let three = const 3;;
let half = thin 0.5;;
 
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


(* function from the paper *)

let compare x y (a : intervalle) (b : intervalle) = 
  if lt x y then a else
    if gt x y then b else
      convex_hull2 a b;;

let check_rectangle (c1 : intervalle) (h0 : intervalle) = 
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

  raise Continue
(* procedure to finish here *)
;;

let rec divideAndCheckRectangle y1 h0 = 
  psn "entering divideAndCheckRectangle: ";
  ps "y1 : ";
  print_interval y1;
  ps "h0 : ";
  print_interval h0;
  let c1 = iSqrt (iSub one (iSqr y1)) in
  try check_rectangle c1 h0 with
  | Reject -> true
  | _ ->
    let (y1a,y1b) = split y1 in
    let (h0a,h0b) = split h0 in
    (divideAndCheckRectangle y1a h0a) 
    && (divideAndCheckRectangle y1a h0b)
    && (divideAndCheckRectangle y1b h0a)
    && (divideAndCheckRectangle y1b h0b)

let main () = 
  let y1 = (0.,1.) in
  let h0 = (0.,10.) in
  if
  divideAndCheckRectangle y1 h0
  then
    print_string "all rejected"
  else
    print_string "finish writing your program";;

main();;

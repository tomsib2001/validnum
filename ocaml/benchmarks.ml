open Basicdefs;;
open Bisection;;
open Newton;;
open Integrals;;

let soi = string_of_int;;

let time f x repeat =
  let time = ref 0. in
  let res = ref (0.,0.) in
  for i = 0 to repeat-1 do
    let t1 = Sys.time() in
    res := iPlus !res (f x);
    let t2 = Sys.time() in
    time := !time +. (t2 -. t1)
  done;
  res := iDiv !res (thin (foi repeat));
print_interval !res;
print_string " in ";
print_float (!time /. (float_of_int (repeat)));
print_string "s";
print_newline()
;;

List.iter (fun i -> print_string ("depth="^(soi i)^"\n") ; time (fun () -> (integralIntBounds iExp i (thin 0.) (thin 1.))) () 10; print_newline()) [3;6;10;11;12;13;14;15];;

 time (fun () -> (integralIntBounds (fun x -> iSin (iPlus x (iExp x))) 13  (thin 0.) (thin 8.))) () 2;;

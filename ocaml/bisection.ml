open Basicdefs;;

(* the following function finds a list of intervals of diameter < eps which contain all the zeros of f *)
let rec bisect eps f fI x y =
  let i = (x,y) in
  if not(contientZero (fI i)) then [] else
    if  eps <= (diam i) then
      let midpoint = ((x +. y)/. 2.) in
      if f midpoint = 0. then 
	(bisect eps f fI x (rd (midpoint)))@[midpoint,midpoint]@(bisect eps f fI (ru midpoint) y)
      else
	(bisect eps f fI x midpoint)@(bisect eps f fI midpoint y)
    else
      [i]
;;

open Basicdefs;;

(*  Newton method for intervals *)

(* function implementing Newton method for intervals *)
let rec newton xk f iF dF steps eps = 
  if steps = 0 || ((diam (xk)) <= eps) then xk else (* added condition on epsilon to take into account that under a certain precision, the operations made here don't make sense *)
    let m = midpoint xk in
    let xk1 = iSub (m,m)  (iDiv (f m,f m) (dF xk)) in
    if contientZero (iF xk1) then
      let xk2 = intersection xk1 xk in
      newton xk2 f iF dF (steps-1) eps
    else
      failwith "pas de zéros ici"
;;


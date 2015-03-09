open Printing
open Quasiring


module IntRing =
struct
  type element = int
  let normal x = x
  let zero = 0
  let one = 1
  let eq x y = (x = y)
  let eqZero x = (x = 0)
  let eqOne x = (x = 1)
  let add = ( + ) 
  let mul = ( * )
  let exp = makeExp one mul
  let divides p n = (p=0 && n=0) || (p<> 0 && n = (n / p) * n)
  let div = ( / )
  let sub = ( - )
  let neg = fun x -> (-x)
  let intmul = ( * )
  let injection x = x
  let soe = soi
end;;

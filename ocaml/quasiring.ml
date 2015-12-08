let makeExp one mul =
  let rec aux x n = match n with
    | 0 -> one
    | n when (n mod 2 = 0) -> let value = (aux x (n/2)) in mul value value
    | n (* n odd *) -> let value = (aux x (n/2)) in mul (mul value value) x
  in aux

module type QUASIRING =
sig
  type element
  val normal : element -> element
  val zero : element
  val one : element
  val eq : element -> element -> bool
  val eqZero : element -> bool
  val eqOne : element -> bool
  val add : element -> element -> element
  val sub : element -> element -> element
  val neg : element -> element
  val mul : element -> element -> element
  val exp : element -> int -> element
  val div : element -> element -> element (* this only needs a proper definition when it is pertinent *)
  val divides : element -> element -> bool (* this is to better assess whether one can use the above function *)
  val intmul : int -> element -> element
  val injection : int -> element
  val floatInj : float -> element (* may not be pertinent in some cases *)
  val soe : element -> string
  (* val eos : string -> element *) (* unnecessary for now*)
end;;

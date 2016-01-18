let assoc3 l a = 
  let rec aux = function
    | [] -> raise Not_found
    | (x,y,z)::t -> if x = a then (y,z) else aux t
  in aux l;;

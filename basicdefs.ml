(* intervals and rounding *)


type intervalle = float*float (* essentiellement pour décorer et savoir de quoi on parle *)

let print_interval (a,b) =
  print_string "(" ; print_float a; print_string ","; print_float b; print_string ")";;

let minf = neg_infinity
let pinf = infinity

let diam = function (x,y) -> if x <= y then 
    abs_float (y -. x) else
    pinf;;

let midpoint (x,y) = (x +. y) /. 2.;;

(* a thin interval, containing only one (float) number0 *)
let thin (c:float) = (c,c)

(* convex hull TODO: rename functions *)
let unionConvexe x y = match (x,y) with
  | (None,y) -> y
  | (x,None) -> x
  | (Some (a,b), Some (c,d)) -> Some (min a c,max b d);;

let unoption = function
  | Some i -> i
  | _ -> failwith "None";;

let convex_hull x y = unoption(unionConvexe x y);;

(* maximum element in absolute value of an interval *)
let abs_max (a,b) = max (abs_float a) (abs_float b);;


let iof = int_of_float
let foi = float_of_int
let sof = string_of_float

let interval_to_string (x,y) = "("^(sof x)^","^(sof y)^")";;

let contientZero (a,b) =
  ((a <= 0.) && (0. <= b)) || ((b < a) && (0. <= b || 0.>= a));;


exception Ensemblevide;;
let intersection (a,b) (c,d) =
  if (b < c) ||(d < a) then 
    raise Ensemblevide 
  else
    let l = max a c and u = min b d in (l,u);; 


let neg x = ~-.x;;

let epsilon = epsilon_float
let eta = min_float

(* Round down *)
let rd x = if x < 0. then (x *. (1. +. epsilon) -. eta) else (x *. (1. -. epsilon) -. eta);;
(* Round up *)
let ru x = if x <= 0. then (x *. (1. -. epsilon) +. eta) else (x *. (1. +. epsilon) +. eta);;

(* basic operations on intervals *)

let iPlus (a,b) (c,d) =  (rd (a +. c), ru (b +. d));;
let iSub (a,b) (c,d) =  (rd (a -. d), ru (b -. c));;
let iNeg (a,b) = ((neg b),(neg a));;

let rec minList  = function
  | [] -> raise Not_found
  | [a] -> a
  | h::t -> min h (minList t);;

let rec maxList  = function
  | [] -> raise Not_found
  | [a] -> a
  | h::t -> max h (maxList  t);;

let rec tousMult l1 l2 = match l1 with
  | [] -> []
  | h::t -> (List.map (fun x -> h *. x) l2)@(tousMult t l2);;

let iMult (a,b) (c,d) = 
  let l = minList  (tousMult [a;b] [c;d]) in
  let u = maxList  (tousMult [a;b] [c;d]) in
  (rd l,ru u);;

let make_interval x y = (x,y);;

let inv x = 1. /. x;;

let iDiv (a,b) (c,d) =
  match (contientZero (c,d)) with
    | false -> iMult (a,b) (make_interval (rd (inv d)) (ru (inv c)))
    | true -> 
      (
	match (contientZero (a,b)) with
	  | true -> (minf,pinf)
	  | false -> if (c,d) = (0.,0.) then make_interval pinf minf (* l'ensemble vide *) else 
	      (
		match (0.0 <= b) with (* abar < 0 *)
		| false -> (* abar < 0 *)
		  if d = (0.) then
		    make_interval (b /. c) pinf
		  else 
		    if (c < 0.)&&(0. < d) then
		      make_interval (b /. c) (b /. d)
		    else
		      if c = 0. then
			make_interval minf (b /. d)
		      else
			failwith "n'arrive jamais" (* car 0 est dans l'intervalle [c,d] *)
		| true -> (* abar >= 0 *) if a = 0. then
		    failwith "n'arrive jamais" (*car ce cas a déjà été traité, 0 dans les deux intervalles *)
		  else
		    if d = 0. then
		      make_interval (minf) (a /. c)
		    else
		      if (c < 0.0)&&(0.0 < d) then (* c < 0 < d *)
			make_interval (a /. d) (a /. c)
		      else 
			if c = 0. then
			  make_interval (a /. d) pinf
			else
			  failwith "n'arrive jamais"
	    )
      )
    ;;


(* now we can say what it means for an interval to contain a float : *)
let contient i x = contientZero (iSub i (x,x));;


(* usual functions *)
(* takes a monotonous function (true means increasing, false means decreasing) and returns an interval extension using *)
let monfun2iFun (croiss : bool) (f : float -> float) (a,b) = if croiss then (rd(f a),ru (f b)) else (rd (f b),ru (f a));;
(* this allows us to define the exponential function: *)
let iExp = monfun2iFun true exp;;

(* float and interval power functions *)

let rec pow x = function
  | 0 -> 1.
  | k -> x *. (pow x (k-1))

let iPow (a,b) n = match (n mod 2) with
  | 1 -> (pow a n,pow b n)
  | _ (* 0 *) -> if n = 0 then (1.,1.) else
      let u = min (abs_float a) (abs_float b) and
	  v = max (abs_float a) (abs_float b) in
      ((pow u n),pow v n);;

(* definition of an extension of the sin *)

let pi = 4.0 *. atan 1.0;;

let quo2pi x = float_of_int(int_of_float (x /. (2. *. pi)));;

let mod2kpi (a,b) = 
  let k = quo2pi (if abs_float a >= abs_float b then a else b) in 
  (rd (a -. 2. *. pi *. k),ru (b -. 2. *. pi *. k));;


let interSmoins (a,b) = 
  if not((2. *. ~-.pi <= a)&&(a <= b)&&(b <= 2. *. pi)) then failwith "interSmoins prend un intervalle contenu dans [-2 pi, 2 pi]" else
    contient (a,b) (~-. (pi /. 2.)) || contient (a,b) (3. *. (pi /. 2.));;
    
let interSplus (a,b) = 
  if not((2. *. ~-.pi <= a)&&(a <= b)&&(b <= 2. *. pi)) then failwith "interSplus prend un intervalle contenu dans [-2 pi, 2 pi]" else
    contient (a,b) ((pi /. 2.)) || contient (a,b) (~-.3. *. (pi /. 2.));;

let iSin i = 
  if (diam i) >= pi then (neg 1., 1.) else
  let (a1,b1) = mod2kpi i in match
    (interSmoins (a1,b1),interSplus (a1,b1)) with
      | (true,true) -> (~-.1.,1.)
      | (true,false) -> (~-.1.,max (sin a1) (sin b1))
      | (false,true) -> (min (sin a1) (sin b1), 1.)
      | (false,false) -> (min (sin a1) (sin b1),max (sin a1) (sin b1));;

let iCos i = iSin (iPlus i (thin (pi /. 2.)));;

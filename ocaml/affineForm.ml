open Basicdefs;;
open Poly;;
open Error;;
open Printing;;
open Reification;;
open Utils;;
open Quasiring;;

let mI = makeIntervalle;;
let zero = IntervalQuasiRing.zero;;
let one = IntervalQuasiRing.one;;

module PolI = IntervalFlatPoly;;

(* module AffineForm (R : QUASIRING) = struct *)

let availableVar = ref 0;;
let freshVar () = 
  let res = !availableVar in
  availableVar := !availableVar + 1; res ;;

type variable = int
type center = intervalle
type coefficient = float

(* an affine form is a sum(gamma_i * epsilon_i) where epsilon_i \in [-1,1] *)
type varList = (variable * coefficient) list
type affineForm = center * varList

let getCenter (f : affineForm) : center = fst f
let getVarList (aF : affineForm) : varList = snd aF

let getCoefficientVarList (vL : varList) (v : variable) : coefficient option =
  try Some (List.assoc v (vL)) with
  | Not_found -> None

let getCoefficient (f : affineForm) (v : variable) : coefficient option =
  getCoefficientVarList (getVarList f) v

let mulCoeff (vL : varList) (coeff : coefficient) : varList =
  List.map (fun (v1,coeff1) -> (v1,coeff *. coeff1)) vL

let v0 = freshVar();;
let v1 = freshVar();;
let v2 = freshVar();;
let v3 = freshVar();;

let (ex1 : affineForm) = makeIntervalle 0.5 0.5,[v0,1.0;v2,0.5];;
let (ex2 : affineForm) = makeIntervalle 0.5 0.5,[v1,1.5];;
let (ex3 : affineForm) = makeIntervalle 0.5 0.5,[v0,1.0;v3,0.5];;

let _ = () in getCoefficient ex1 2;;

let addVarList vL1 vL2 =
  List.map
    (fun (v,coeff1) ->
      match getCoefficientVarList vL2 v with
      | Some(coeff2) -> (v,coeff1 +. coeff2)
      | None -> (v,coeff1)
      )
    vL1
  @
    (List.fold_right (fun (v2,coeff2) y -> match getCoefficientVarList vL1 v2 with
    | None ->  (v2,coeff2)::y
    | Some _ -> y) vL2 []);;

let add a1 a2 =
  (iPlus (getCenter a1) (getCenter a2),addVarList (getVarList a1) (getVarList a2));;

add ex1 ex2;;
add ex1 ex2;;
add ex2 ex3;;

let mul (a1 : affineForm) (a2 : affineForm) : affineForm =
  let (c1,c2) = (getCenter a1,getCenter a2) in
  let c = iMult c1 c2 in
  let varList = addVarList (mulCoeff (getVarList a2) (abs_max c1)) (mulCoeff (getVarList a1) (abs_max c2)) in
  let vNoise = freshVar() in
  let noiseTerm = 
    List.fold_right 
      (fun (v1,r1) y -> (List.fold_right (fun (v2,r2) z -> ((abs_float r1) *. abs_float r2) +. z) (getVarList a2) y) +. y) (getVarList a1) 0.
  in
  (c,(vNoise,noiseTerm)::varList)
;;

let neg a = (iNeg (getCenter a), mulCoeff (getVarList a) (~-.1.));;

let applyFun f df (a : affineForm) =
  let c = getCenter a in
  (f c, mulCoeff (getVarList a) (df c));;

let eval (a : affineForm) : intervalle =
  iPlus
    (getCenter a)
    (List.fold_right (fun (v,coeff) y -> iPlus y (iMult (thin coeff) (makeIntervalle ~-.1. 1.))) (getVarList a) (makeIntervalle 0. 0.));;

eval ex1 (* (makeIntervalle 0. 1.) *);;
mul ex1 ex2;;
(* end;; *)

(* module InstAF = Affineform (FloatQuasiRing);; *)

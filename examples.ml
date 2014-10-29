open Basicdefs;;
open Reification;;
open Integrals;;
open Diffeq;;
open Bisection;;
open Newton;;
open Taylor;;

let heavy = false;;



(* comparing the two ways of computing the power of an interval *)

iPow (~-.3.,3.) 3;;

let rec naiveiPow i = function   
  | 0 -> (1.,1.) 
  | k -> iMult i (naiveiPow i (k-1));;

naiveiPow (~-.3.,3.) 3;;

(* test of the functions which help us compute the sin *)


quo2pi 68.;;

mod2kpi (pi +. 1., 2. *. pi +. 1.);;
mod2kpi (67.,68.);;


(* test of the sin *)
iSin (~-.1.5,1.5);;
iSin (~-.3., ~-.2.);;
iSin (3., 7.);;



(* we test the bisection function using a Warwick Tucker's Validated Numerics example *)
let sI x = iMult (iSin x) (iSub x (iCos x));;
let s x = (sin x) *. (x -. (cos x));;

if heavy then bisect 0.00000000000001 s sI 0. 10. else [];;

(* examples for the Newton method *)
let s x = iMult (iSin x) (iSub x (iCos x));; (* rappel *)
let dS x = iMult (iCos x) (iPlus (iSub (x) (iCos x)) (iMult (iSin x) (iPlus (1.,1.) (iSin x))));; (* sa dérivée étendue par intervalles *)
let sReelle x = (sin x) *. (x -. (cos x));;

newton (6., 7.) sReelle s (dS) 10 1e-9;;


(* examples for integrals *)
(* let iF x = iSin (iPlus (iExp x) x);; *)
let iF x = iMult (iPow x 2) (iMult (iExp (iNeg (iDiv (x) ((2.,2.))))) (iLog x))
(* the following computation is heavy *)

let (u,v) = int_iFun_eps2 0.001 iF (0.,1.);;
print_interval (u,v);;
print_string "coucou";;


(* examples of specializing an elemFUn to a float -> float function *)
let fSym = Sin(Plus(Var "x", Exp (Var "x")));;
let iF = sym2iFunFloat fSym;;
(* iF (0.01,0.02);; *)
let f = sym2floatFun fSym;;
(* f 0.01;; *)


(* example of sym2floatFun *)
let fSym = Sin(Plus(Var "x", Exp (Var "x")));;
let iF = sym2iFunFloat fSym;;
iF (0.01,0.02);;
let f = sym2floatFun fSym;;
f 0.01;;

(* example of automatic differentiation *)
let fDif = sym2ad1 fSym;;
fDif (0.01,0.01);;
(1. +. exp(0.01)) *. cos (0.01 +. exp(0.01));;

(* example of formal derivation *)
let fSec = formalDer float_of_int 0. 1. "x" fSym;;

let fY = subs (Exp(Var "x")) (Var "y") fSym;;

let gSym = Mult(Var "x", Mult(Var "x",Var "x"));;
let gDiff = sym2ad1 gSym;;
gDiff (9.,10.);;

let gSym1 = Pow(Var "x",3);;
let gDiff1 = sym2ad1 gSym1;;
gDiff1 (9.,10.);;

(* example of use of int_iFun *)
diam (int_iFun iF 5 0. 0.001);;

let fSym = Sin(Exp (Var "x"));;
let iF = sym2iFunFloat fSym;;
if heavy then int_iFun iF 22 0. 8. else thin pinf;;

(* test of the integral with interval bounds *)
if heavy then integralIntBounds iExp 15 (thin 0.) (thin 1.) else (thin pinf);;



(* test of fixpointNonLin *)(* exemples de Warwick Tucker, pas forcément linéaires *)

     

(* for the cosine, f(x1,x2) = (x2,-x1) *)
let fCos neg l = match l with
  | [a;b] -> [b;neg a]
  | _ -> failwith "wrong argument, cos has an equation of order 2";;

let makeIfunFromDiffEq2 steps intprec x0 y0 valinit f x1  = 
  match (fixpointNonLin steps intprec x0 y0 valinit f) with
  | [] -> failwith "Yet another empty list error"
  | h::t -> h x1;;

let newICos = makeIfunFromDiffEq2 5 3 (thin 0.) [thin 1.;thin 0.] [(fun x -> (neg 1.,1.));(fun x -> (neg 1.,1.))] (fCos (fun f -> (fun x -> iNeg (f x))));;

(* à décommenter pour les tests
On constate que sur le cosinus, cette méthode n'est pas géniale loin de 0
 *)
newICos (0.01,1.5);;
newICos (0.1,0.2);;
iCos (0.1,0.2);;

(* Exemple de W.T. 183,3 *)
(* x' = sin(x + cos(x)) *)

let fEx1 l = match l with
  | [f] -> [fun (x: intervalle) ->  (iSin(iPlus x (iCos (f x))))]
  | _ -> failwith "Wrong size for Example 1";;

(* On prend les conditions initiales suivantes: y(0) = 0.
On donne comme encadrement de départ de la fonction [-10.,10.]
 *)
let fEx1eff = makeIfunFromDiffEq2 4 2 (thin 0.) [thin 0.] [fun x -> (neg 1.,1.)] fEx1;;

fEx1eff (0.,0.001);;

(* Exemple de W.T. 186,5 *)
(* x'(t) = -t * x(t) *)
(* curieux, ça a l'air de ne pas marcher. Je ne vois pas spécialement pourquoi *)

let fEx2 l = match l with
  | [f] -> [fun (t:intervalle) -> (iMult (iNeg t) (f t))]
  | _ -> failwith "Wrong size for Example 2";;

let fEx2eff = makeIfunFromDiffEq2 4 3 (thin 0.) [0.8,0.8] [fun x -> (0.,0.8)] fEx2;;
let i = fEx2eff (0.,0.2);;
let fEx2eff = makeIfunFromDiffEq2 4 3 (thin 0.2) [snd i,snd i] [fun x -> (0.,snd i)] fEx2;;
let i = fEx2eff (0.,0.2);;

print_interval i;;
(* gros problème ici... *)



(* test of estimateSolCutNonLin *)
(* estimateSolCutNonLin 0. 5 3 (thin 0.5) (fun x -> thin (neg 1.,1.)) (fun f -> ) *)


(* test of simple enclosure methods *)
let z0ExpConst = (0.,10.) (* approximation grossière de l'exponentielle sur [0,1] *)
let phiExp t0 t1 z0 = z0;;
let x1 = estimateWithConst 0. 0.1 phiExp (thin 1.) z0ExpConst;;
let x2 = estimateWithConst 0. 0.1 phiExp (thin 1.) x1;;
let x3 = estimateWithConst 0. 0.1 phiExp (thin 1.) x2;;
let x3 = estimateWithConst 0. 0.1 phiExp (thin 1.) x3;;
let x4 = estimateWithConst 0.1 0.2 phiExp (thin (fst x3)) z0ExpConst;;
let x5 = estimateWithConst 0.1 0.2 phiExp (thin (fst x3)) x4;;
let x6 = estimateWithConst 0.1 0.2 phiExp (thin (fst x3)) x5;;


(* test of makeInterval and clean *)
let l = makeList 0. 1. 3 in
clean(l);;


(* let x0=  (0.5,0.5) in *)
(* get_enclosure 0. 0.1 14  phiExp x0 (fun x y -> (0.,3.));; *)

(* let l = (makeList 0. 1. 1);; *)

estimateSolCut 0. 3 0 [1.] [1.] [fun x -> (0.,10.)] (fun x -> x) l;;

(* examples from taylor.ml *)

let t1 = getTaylorApproxSymbolic foi "x" 4 (Cos (Var "x")) (Var "x0") (Var "x");;

elemFun_to_string string_of_float t1;;

let t2 = getTaylorApproxSymbolic foi "x" 4 (Exp (Var "x")) (Var "x0") (Var "x");;

elemFun_to_string string_of_float t2;;

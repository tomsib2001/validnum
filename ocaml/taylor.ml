open Basicdefs;;
open Reification;;
open Integrals;;
open Diffeq;;


(* Taylor  *)

let fact n = 
  let rec aux res = function
    | 0 -> res
    | n -> aux (res*n) (n-1)
  in aux 1 n;;

let taylorCos order x1 = 
let rec taylorCosAux = function
  | 0 -> [1]
  | 1 -> [0;1]
  | n -> let l = taylorCosAux (n-1) in 
	 match l with
	   | a::b::t -> ((-1) * n * (n+1) * b)::l
	   |_ -> failwith "n'arrive jamais"
in let temp = (taylorCosAux order) in
   let temp2 = List.map (fun x -> if x = 0 then (thin 0.) else iDiv (thin 1.) (thin (foi(x)))) temp in 
   let temp3 = List.rev temp2 in
   List.fold_left (fun  (res,order) x -> (iPlus res (iMult x (iPow x1 order)),order+1) )  (thin 0., 0) temp3;;

(* #trace iPow;; *)
(* #trace iPlus;; *)
(* #trace iMult;; *)
let t = taylorCos 2 (0.5,1.6);;
cos 1.6;;
(* le résultat n'est pas correct parce que dans la formule de Taylor Lagrange, le reste doit être majoré par l'image de l'intervalle par la dérivée n-ième, ce qu'on ne peut pas obtenir sans programmer la dérivation symbolique. *)


let rec formalDer int2Const zero one var = 
  let mult = function
    | (Const z, _) when z = zero-> Const zero
    | (_, Const z) when z = zero -> Const zero
    | (Const o,x) when o = one -> x
    | (x, Const o) when o=one -> x
    | (x,y) -> Mult(x,y) in
  function
    | Const c -> Const zero
    | Var s -> if s = var then Const one else Var s
    | Plus(f1,f2) -> Plus(formalDer int2Const zero one var f1,formalDer int2Const zero one var f2)
    | Sub(f1,f2) -> Sub(formalDer int2Const zero one var f1,formalDer int2Const zero one var f2)
    | Mult(f1,f2) -> Plus(mult(f1,formalDer int2Const zero one var f2),mult(formalDer int2Const zero one var f1, f2))
    | Div(f1,f2) -> Div(Sub(mult(formalDer int2Const zero one var f1,f2),mult(f1,formalDer int2Const zero one var f2)),mult(f2,f2))
    | Neg f1 -> Neg (formalDer int2Const zero one var f1)
    | Sqrt f1 -> 
      Div (formalDer int2Const zero one var f1,
	(mult (Const (int2Const 2),(Sqrt f1))))
    | Cos f1 -> Neg (mult(formalDer int2Const zero one var f1, Sin f1))
    | Sin f1 -> mult(formalDer int2Const zero one var f1, Cos f1)
    | Exp f1 -> mult(formalDer int2Const zero one var f1, Exp f1)
    | Log f1 -> Div(formalDer int2Const zero one var f1, f1)
    | Pow(f1,i) -> mult(Const (int2Const i), mult(formalDer int2Const zero one var f1,Pow(f1,i-1)))
    | VarFun(f1,k,x) -> let xp = formalDer int2Const zero one var  x in mult(xp,VarFun(f1,k+1,x))
;;

let zero = 0.;;
let one = 1.;;

let f = Sin(Plus(Var "x", Exp (Var "x")));;
formalDer foi zero one "x" f;;

let g = Cos(VarFun("f",0,Var "x"));;
formalDer foi zero one "x" g;;
print_string (elemFun_to_string sof (formalDer foi zero one "x" g));;

print_string (elemFun_to_string sof (formalDer foi zero one "x" f));;

let rec kDer int2Const (zero: 'a) (one:'a) (var:string ) k (f: 'a elemFun) = match k with
  | 0 -> f
  | k -> kDer int2Const zero one var (k-1) (formalDer int2Const zero one var f);;

(* subs x0 x1 expr replaces x0 by x1 in the expression expr *)
let rec subs x0 x1 = function
  | x when x=x0 -> x1
  | Const c -> Const c
  | Var s -> Var s
  | Plus(f1,f2) -> Plus(subs x0 x1 f1,subs x0 x1 f2) 
  | Mult(f1,f2) -> Mult(subs x0 x1 f1,subs x0 x1 f2)
  | Sub(f1,f2) -> Sub(subs x0 x1 f1,subs x0 x1 f2)
  | Div(f1,f2) -> Div(subs x0 x1 f1,subs x0 x1 f2)
  | Neg f1 -> Neg (subs x0 x1 f1)
  | Sqrt f1 -> Sqrt (subs x0 x1 f1)
  | Cos f1 -> Cos (subs x0 x1 f1)
  | Sin f1 -> Sin (subs x0 x1 f1)
  | Exp f1 -> Exp (subs x0 x1 f1)
  | Log f1 -> Log (subs x0 x1 f1)
  | Pow(f1,i) -> Pow(subs x0 x1 f1,i)
  | VarFun(s,k,f) -> VarFun(s,k,subs x0 x1 f)
;;

let convUnion x y = unoption (unionConvexe (Some x) (Some y));;

(* this function computes (an enclosure of) the taylor remainder between x0 and x *)
let remainder kder toiFun toiConst  k (t0 : float) (ts : intervalle) f = 
  (iMult
     (iDiv
	(toiFun (kder (k+1) f) (convUnion (thin t0) ts))
	(toiConst (foi (fact (k+1))))
     )
     (
       iPow (iSub (ts) (thin t0)) (k+1)
     )
  )
;;

let getTaylorApproxGen div kder tofun toconst plus sub mult pow zero  k f x0 x =
  let getCoeff k = div (tofun (kder k f) x0) (toconst (foi(fact k))) in
  let rec aux res = function
    | -1 -> res
    | l -> let coeff = getCoeff l in
	   aux (plus (mult res ( (sub x x0) )) coeff) (l-1)
  in (aux  (getCoeff k) (k-1));;

let getTaylorApproxSymbolic int2Const (var:string) k f x0 x =
  getTaylorApproxGen 
    (fun x y -> if y = Const 1. then x else Div(x,y))
    (kDer int2Const 0. 1. var)
    (fun x y -> subs (Var "x") (Var "x0") x)
    (fun x -> Const x)
    (fun x y -> Plus(x,y))
    (fun x y -> Sub(x,y))
    (fun x y -> if x = Const 1. then y else if y = Const 1. then x else Mult(x,y))
    (fun x i -> if i=0 then Const 1. else Pow(x,i))
    (Const 0.)
    k f x0 x;;

let t1 = getTaylorApproxSymbolic foi "x" 4 (Cos (Var "x")) (Var "x0") (Var "x");;
let t2 = getTaylorApproxSymbolic foi "x" 4 (Sin (Var "x")) (Var "x0") (Var "x");;

print_string (elemFun_to_string sof t1);;

let getTaylorApproxInterval (var:string) k f (t0: float) (ts: intervalle) =
  let (zero,one) = (0.,1.) in
  let int2Const x = (foi x) in
  let 
      tayl = 
    getTaylorApproxGen
      iDiv
      (fun k f -> (kDer int2Const zero one var k f))
      (fun f -> sym2iFunFloat f)
      (fun x -> thin x)
      iPlus
      iSub
      iMult
      iPow
      (thin 0.)
      k f (thin t0) (ts)
  and
      rem = 
    remainder
      (kDer int2Const zero one var)
      (fun f i -> sym2iFunFloat f i)
      (fun x -> (thin x))
      k
      t0
      ts
      f
  in (tayl,rem)
;;

(* let (i,j) = getTaylorApproxInterval "x" 3 (Exp (Pow(Var "x",1))) (0.) (1.,1.);; *)
(* iPlus i j;; *)

(* let int2Const = foi;; *)
(* remainder (kDer int2Const 0. 1. "x") sym2iFun thin 4 0. (thin 1.) (Exp (Var "x"));;  *)

(* let i = getTaylorApproxInterval "x" 3 (Cos (Var "x")) (0.) (0.3,0.5);; *)
(* diam (iPlus (fst i) (snd i));; *)
(* (cos 0.3, cos 0.5);; *)

let i = getTaylorApproxInterval "x" 6 (Exp (Var "x")) (0.) (1.,1.);;
diam (iPlus (fst i) (snd i));;

sym2floatFun f (0.03);;



(* Maintenant qu'on a Taylor, on peut retenter de définir iSin au moins au voisinage de 0: *)
let iSinBis x = let (a,b) = getTaylorApproxInterval "x" 8 (Sin (Var "x")) (0.) x in
	     iPlus a b;;

let iCosBis x = let (a,b) = getTaylorApproxInterval "x" 8 (Cos (Var "x")) (0.) x in
	     iPlus a b;;

(* iCos (thin 3.14159);; *)

(* let fEx1 l = match l with *)
(*   | [a] -> [fun (x: intervalle) ->  (iSin(iPlus x (iCos (a x))))] *)
(*   | _ -> failwith "Wrong size for Example 1";; *)

(* let fEx1eff = makeIfunFromDiffEq2 3 4 (0.,0.) [thin 0.] [fun x -> (0.,1.)] fEx1;; *)

(* (\* fEx1eff (0.,0.001);; *\) *)


(* Essayons d'utiliser tout ça pour résoudre des équa-diffs *)

(* We start with a differential equation f' = phi(f(t))
   we write f(t) = sum(a_k (t - t0)^k
   and g(t)= phi(f(t)) = sum(b_k (t - t0)^k
   then we have a_(k+1) = b_k / (k+1)
   and a_0 = f(t_0)
   and b_0 = phi(a_0)
 *)
(* only in dimension 1 *)

let rec isConstantFunction f = 
  let id = fun x -> x in
  makeF (fun x -> true) (fun x -> false) (&&) (&&) id (&&) (&&) id id id id id (fun (x,y) -> x) (fun f i x -> false) f ();;

isConstantFunction f;;
isConstantFunction (subs (Var "x") (Const 3.) f);;

let rec fold_righti (f : int -> 'a -> 'b -> 'b) (l : 'a list) (def : 'b) =
  let rec aux res = function
    | (_,[]) -> res
    | (i,h::t) -> aux (f i h res) (i+1,t)
  in aux def (0,l);;

(* Example *)
fold_righti (fun i a (b,c) -> (i+b,a+c)) [1;2;3] (0,0);;



let iZero = thin 0.;;
let iOne = thin 1.;;

let getCoeffsSol (k : int) (f: string) (t0 : float) (x0 : intervalle) (var : string) (phi : intervalle elemFun) = 
  let int2Const = fun x -> thin (foi x) in
  let rec aux = function
    | (k1,l) when k1=k -> l
    | (k1,l) -> 
      let fSymDerk = kDer int2Const iZero iOne "t" k1 (subs (Var var) (VarFun(f,0,Var "t")) phi)  in
      let pre_pre_ak = fold_righti (fun i x y -> subs (VarFun("f",i,Var "t")) (Const (List.nth l i)) y) l fSymDerk in
      let pre_ak = subs (Var "t") (Const (thin t0)) pre_pre_ak in
      let ak = sym2iFunGen (fun x -> x) pre_ak (thin pinf) in (* giving pinf as an argument is because pre_ak should be a constant function *)
      aux (k1+1,List.rev(ak::(List.rev l))) in aux (0,[x0])
;;

let rec toSeries div int2Const l = List.mapi (fun i x -> div x (int2Const (fact i))) l;;

subs (VarFun("f",0,Var "x")) (Const (thin 1.)) (VarFun("f",0,Var "x"));;

getCoeffsSol 2 "f" 0. (thin 1.) "x" (Mult(Const (thin 1.),(Var "x")));;
let l1 = getCoeffsSol 5 "f" 0. (thin 1.) "x" (Sin(Plus(Var"x",Exp (Var "x"))));;


toSeries iDiv (fun i -> thin (foi i)) l1;; (* CORRECT ACCORDING TO MAPLE!!!! *)
(* MAPLE: 1.+.8414709848*x+.2273243567*x^2-0.5836258140e-1*x^3-0.6153747075e-1*x^4-0.791429540e-2*x^5+O(x^6) *)


(* to use W Tucker's terminology, we computed the "thin" coefficients, but the remainder remains to be computed. For this, we will use essentially the same function but a first order enclosure on the interval we are looking at. *)

let horner_eval mult add zero x l =
  let rec aux res = function
    | [] -> res
    | h::t -> aux (add (mult res x) h) t
  in aux zero l;;

(* test *)
(* horner_eval (fun x y -> x*y) (+) 0 2 [1;1];; *)

let check_enclosure t0 x0 t phi var valinit depth =
  let iFun = function (x:intervalle) -> sym2iFunGen (fun x -> x) (subs (Var var) (Const (valinit x)) phi) in
  let check_int = iPlus (x0) (integralIntBounds (iFun (thin pinf)) depth (thin t0) (t0,t)) in
  (* print_interval check_int; *)
  (* print_interval (iFun (thin pinf) (t0,t) ); *)
  subset check_int (iFun (thin pinf) (t0,t) );;

let iFun = sym2iFunGen (fun x -> x) (Const (0.,2.)) ;;

iPlus (thin 1.) (integralIntBounds iFun 2 (thin 0.) (0.,1.));; 

check_enclosure 0. (thin 1.) 0.1 (Var "x") "x" (fun x -> (neg 1.,10.)) 2;;

let high_order_enclosure (f:string) (var:string) phi order t0 x0 t1 (valinit : intervalle)  = 
  let valid_approx = check_enclosure t0 x0 t1 phi var (fun x -> valinit) 5  in
  if valid_approx then
    let thincoeffs = toSeries iDiv (fun i -> thin (foi i)) (getCoeffsSol order f t0 x0 var phi) in 
    let firstOrderEnc = getCoeffsSol (order+1) f t0 valinit var phi in
    let akS1 = (List.nth firstOrderEnc (order+1)) in
    let errorTerm = 
      iMult (iDiv akS1 (thin (foi (fact(order+1))))) (iPow (thin (t1 -. t0)) (order+1)) in
    Some (horner_eval iMult iPlus (thin 0.) (thin (t1 -. t0)) (List.rev thincoeffs),errorTerm)
  else
    begin print_string "Invalid approximation, try something wider or reduce the interval"; None end
;;

let Some(a,b) = high_order_enclosure "f" "x" ((Var "x")) 15 0. (thin 1.) 0.5 (neg 100.,100.);;

let c = iPlus a b;;

3;;

(* let i = (high_order_enclosure "f" "x" ((Var "x")) 20 0. (thin 1.) 1. (neg 10.,10.));; *)
(* diam (iPlus (fst i) (snd i));; *)


(* let us now implement Tucker's method using separate orbits for enclosing solutions to a differential equation *)


let high_order_enclosure_final f var phi order t0 x0 t1 (valinit : intervalle) =
  let (res,error) = match high_order_enclosure f var phi order t0 x0 t1 valinit with
    | Some(a,b) -> (a,b)
    | _ -> ((minf,pinf),(0.,0.))
 in
  iPlus res error;;

high_order_enclosure "f" "x" (Neg(Mult(Var "t",Var "x"))) 10 0. (neg 1.,1.) 0.5 (neg 20.,20.);;

let estimateSolCutTaylor (t0 : float)  order  (x0: intervalle) var f phi (valinit : intervalle) l =
  let rec aux (x:intervalle) (t1:float) = function
    | [] -> x
    | t2::t -> let f1 = fun (xx: float) t2 -> high_order_enclosure_final f var phi order t1 (thin xx) t2 valinit in
	       let low = f1 (fst x) (t2) in
	       let up = f1 (snd x) (t2) in
	       let xnew1 = fst low in
	       let xnew2 = snd up in
	       let xnew = (xnew1,xnew2) in
	       aux xnew t2 t
  in aux x0 t0 (List.tl l);;

let l = makeList 0. 2. 4;;

estimateSolCutTaylor 0. 7 (neg 1.,1.) "x" "f" (Neg(Mult(Var "t",Var "x"))) (neg 200.,200.) l;;
(* Ocaml says: (-0.135339507501562373, 0.135339507501562373) *)
(* Maple says: f(0.2) = 0.135335205774654. Not bad :-)  *)

(* How about in dimension n? f : R -> R^n *)

let soi = string_of_int;;

let cutList k l =
  let rec aux res = function
    | (0,_) -> res
    | (m,[]) -> failwith ("your list only has "^(soi (k-m))^" elements. Please learn how to count.")
    | (m,h::t) -> aux (h::res) (m-1,t)
  in List.rev (aux [] (k,l));;

(* cutList 10 [1;2;3;4;5;6];; *)

(* let replaceAccordingTo phi eqOrder maxDer f var  (expr : 'a elemFun) =  *)
(*   let rec aux = function *)
(*     | (0,e) -> e *)
(*     | (m,e) when m<=k -> e *)
(*     | (m,e) when m = k+1 -> subs (VarFun(f,m,Var var)) (List.nth phi k) e *)
(*     | _ -> failwith "I'm not comfortable substituting such high orders yet, if you don't mind." *)
(*   in aux (eqOrder,expr);; *)

(* let phi = [VarFun("f",1,Var "t"); Neg(VarFun("f",0,Var "t"))] in *)
(* replaceAccordingTo phi 3 1 "f" "t"  (VarFun("f",3,Var "t"));; *)

let getCoeffsSol_dim_n (k : int) (f : string) (t0 : float) (x0 : intervalle list) (var : string) (phi : intervalle elemFun list) =
  let int2Const = fun x -> thin (foi x) in
  let eqOrder = (List.length x0) in
  if (k+1) <= eqOrder then cutList (k+1) x0 else
    let rec aux = function
      | (k1,_,l) when k1 = k -> l
      | (k1,fderk1,l) -> (* it is implicit that k1 >= eqOrder *)
	(* first a function which will get rid of derivatives of too high order by applying the diffrential equation *)
	let fSymDerk = List.map (fun phi_i -> kDer int2Const iZero iOne "t" 1  phi_i) fderk1 in
	print_string "fSymDerk:  ";
	List.iter (fun x -> print_string ((elemFun_to_string interval_to_string x)^"\n")) fSymDerk;
	let rec aux2 res = function
	  | -1 -> res
	  | m -> aux2 (List.map (fun y -> (subs (VarFun(f,m,Var var)) (Const (List.nth l m)) y)) res) (m-1) in

	let pre_pre_pre_ak = List.map (fun e -> subs (VarFun(f,eqOrder,Var var)) (List.nth phi (eqOrder-1)) e) fSymDerk in
	let pre_pre_ak = aux2 (pre_pre_pre_ak) (eqOrder-1) in
	print_string "pre_pre_ak:  ";
	List.iter (fun x -> print_string ((elemFun_to_string interval_to_string x)^"\n")) pre_pre_ak;
	let pre_ak = List.map (fun x -> subs (Var "t") (Const (thin t0)) x) pre_pre_ak in  
	let ak = List.map (fun x -> sym2iFunGen (fun x -> x) x (thin pinf)) pre_ak in 
	aux(k1+1,pre_pre_pre_ak,List.rev ((List.hd ak)::(List.rev l)))
    in aux(eqOrder,phi,x0)
;;

let phiCos = [VarFun("f",1,Var "t"); Neg(VarFun("f",0,Var "t"))];;
getCoeffsSol_dim_n 7 "f" 0. [thin 1.;thin 0.] "t" phiCos;;


(* verification for the polynomial 2*x^2 - 3*x + 1 with the diff eqn: x'' = 4 *)
let lpol = getCoeffsSol_dim_n 7 "f" 0. [thin 1.;thin (neg 3.)] "t" [VarFun("f",1,Var "t"); Const (thin 4.)];;

toSeries iDiv (fun i -> thin (foi i)) lpol;;

let check_enclosure_dim_n (t0 : float) (x0 : intervalle list) (t : float) (phi : intervalle elemFun list) f var (valinit : (intervalle -> intervalle) list) depth =
  let rec aux res = function
    | -1 -> res
    | m -> aux (List.map (fun y -> (fun x -> (subs (VarFun(f,m,Var var)) (Const ((List.nth valinit m) x))) (y x))) res) (m-1) in
  let phi_init = aux (List.map (fun x -> fun y -> x) phi) (List.length x0 - 1) in
  let iFun = List.map (fun phi_i -> fun y -> sym2iFunGen (fun x -> x) (phi_i y)) phi_init in
  let check_int = 
    List.map2 
      (
	fun iFun_i x0_i -> 
	    iPlus 
	      (x0_i) 
	      (integralIntBounds (iFun_i (thin pinf)) depth (thin t0) (t0,t))
      )
	iFun x0 in
  List.for_all2 (fun x y -> subset x (y (thin pinf) (t0,t))) check_int iFun;;

(* this check is not thorough enough, find something better and print out the intervals whose inclusion we are checking. *)
check_enclosure_dim_n (0.) [thin 1.;thin 0.] (0.1) phiCos "f" "t" [(fun x -> (neg 10.,10.));fun x -> (neg 10.,10.)] 10;;


let high_order_enclosure_dim_n (f: string) (var : string) phi order t0 x0 t1 (valinit : intervalle list) =
  let abs_valinit = (List.map (fun x -> fun y -> x) valinit) in
  let valid_approx = check_enclosure_dim_n t0 x0 t1 phi f var abs_valinit 5 in
  if valid_approx then
    let thincoeffs = toSeries iDiv (fun i -> thin (foi i)) (getCoeffsSol_dim_n order f t0 x0 var phi) in
    let firstOrderEnc = getCoeffsSol_dim_n (order + 1) f t0 (valinit) var phi in
    let akS1 = (List.nth firstOrderEnc (order)) in
    let errorTerm =
      iMult (iDiv akS1 (thin (foi (fact (order))))) (iPow (thin (t1 -. t0)) (order+1)) in
    (horner_eval iMult iPlus (thin 0.) (thin (t1 -. t0)) (List.rev thincoeffs),errorTerm)
  else
    failwith "I'm afraid your approximation is a bit too tight for me, please try something wider or reduce the interval";;

high_order_enclosure_dim_n "f" "t" phiCos 7 0. [thin 1.;thin 0.] 0.5 [(neg 10.,10.);(neg 10.,10.)];;

let high_order_enclosure_final_dim_n f var phi order t0 x0 t1 valinit = 
  let res,error = high_order_enclosure_dim_n f var phi order t0 x0 t1 valinit in
  iPlus res error;;

high_order_enclosure_final_dim_n "f" "t" phiCos 7 0. [thin 1.;thin 0.] 0.5 [(neg 10.,10.);(neg 10.,10.)];;

(* let estimateSolCutTaylor_dim_n (t0 : float)  order  (x0: intervalle list) var f (phi : intervalle elemFun list) (valinit : intervalle list) l = *)
(*   let rec aux (x:intervalle list) (t1:float) = function *)
(*     | [] -> x *)
(*     | t2::t -> let f1 = fun (xx: float) t2 -> high_order_enclosure_final_dim_n f var phi order t1 ((thin xx)::(List.tl x)) t2 valinit in *)
(* 	       let low = f1 (fst (List.hd x)) (t2) in *)
(* 	       let up = f1 (snd (List.hd x)) (t2) in *)
(* 	       let xnew1 = fst low in *)
(* 	       let xnew2 = snd up in *)
(* 	       let xnew = (xnew1,xnew2) in *)
(* 	       aux (xnew) t2 t *)
(*   in aux x0 t0 (List.tl l);; *)

open Basicdefs;;

type 'a elemFun =
  | Const of 'a
  | Var of string
  | Plus of 'a elemFun * 'a elemFun
  | Mult of 'a elemFun * 'a elemFun
  | Sub of 'a elemFun * 'a elemFun
  | Pow of 'a elemFun * int
  | Neg of 'a elemFun
  | Div of 'a elemFun * 'a elemFun
  | Sin of 'a elemFun
  | Cos of 'a elemFun
  | Exp of 'a elemFun
  | VarFun of string*int*'a elemFun (* f(x) *)
;;

let rec elemFun_to_string soc = function
  | Const f -> soc f
  | Var x -> x
  | Plus (x,y) -> (("(")^(elemFun_to_string soc x)^" + "^(elemFun_to_string soc y)^")")
  | Mult (x,y) -> "("^(elemFun_to_string soc x)^" * "^(elemFun_to_string soc y)^")"
  | Sub (x,y) -> "("^(elemFun_to_string soc x)^" - "^(elemFun_to_string soc y)^")"
  | Div (x,y) -> "("^(elemFun_to_string soc x)^" / "^(elemFun_to_string soc y)^")"
  | Pow(x,n) -> "("^((elemFun_to_string soc x)^" ^ "^(string_of_int n))^")"
  | Neg x -> "( - ("^(elemFun_to_string soc x)^"))"
  | Sin x -> " sin ("^(elemFun_to_string soc x)^")"
  | Cos x -> " cos ("^(elemFun_to_string soc x)^")"
  | Exp x -> " exp ("^(elemFun_to_string soc x)^")"
  | VarFun(f,k,x) -> f^"^"^(string_of_int k)^"("^(elemFun_to_string soc x)^")"
  (* | _ -> "not implemented in elemFun_to_string";; (\* for future additions*\) *)

(* a generic function which interprets a symbolic elementary function into a desired model: it could be float -> float functions, interval -> interval functions, symbolic functions again (this would be desirable for derivation or taylor models) *)
let makeF const var plus mult neg sub div cos sin exp pow varfun f = 
  let rec aux = function
    | Const c -> (fun (x) -> const c)
    | Var s -> (fun x -> var x)
    | Plus (f1,f2) -> let if1 = aux f1 and if2 = aux f2 in 
		      (fun x -> plus (if1 x) (if2 x))
    | Sub  (f1,f2) -> let if1 = aux f1 and if2 = aux f2 in 
		      (fun x -> sub (if1 x) (if2 x))
    | Pow(f1,i) -> let if1 = aux f1 in (fun x -> pow(if1 x,i))
    | Mult  (f1,f2) -> let if1 = aux f1 and if2 = aux f2 in 
		       (fun x -> mult (if1 x) (if2 x))
    | Div  (f1,f2) -> let if1 = aux f1 and if2 = aux f2 in 
		      (fun x -> div (if1 x) (if2 x))
    | Neg  f1 -> let if1 = aux f1 in (fun x -> neg (if1 x))
    | Cos  f1 -> let if1 = aux f1 in (fun x -> cos (if1 x))
    | Sin  f1 -> let if1 = aux f1 in (fun x -> sin (if1 x))
    | Exp f1 -> let if1 = aux f1 in (fun x -> exp (if1 x))
    | VarFun(f,k,f1) -> let if1 = aux f1 in (fun x -> varfun f k (if1 x))
  in aux f;;


(* we can specialize to intervals: *)
let iVar x = x
let iVarFun f k x = failwith ("trying to apply a function variable ("^f^") to a concrete interval : "^(interval_to_string x));;

(* when the original function was of type float elemFun: *)
let sym2iFunFloat = makeF thin iVar iPlus iMult iNeg iSub iDiv iCos iSin iExp (fun (x,y) -> iPow x y) iVarFun;;

(* or more generally when it was of type 'a elemFun *)
let sym2iFunGen (aToIntervalle : 'a -> intervalle) = makeF aToIntervalle iVar iPlus iMult iNeg iSub iDiv iCos iSin iExp (fun (x,y) -> iPow x y) iVarFun;;

(* we can specialize to float -> float functions: *)
let const c = c;;
let var x = x;;
let floatVarFun f k x = raise Not_found;;

let sym2floatFun = makeF const var (+.) (fun x y -> x *. y ) (fun x -> ~-.x) (-.) (/.) cos sin exp (fun (x,y) -> pow x y) floatVarFun;;


(* and now we specialize for automatic differentiation *)
(* we specialize makeF for automatic differentiation of order 1 *)
let constAD c = ((c,c),(0.,0.));;
let varAD x = (x,(1.,1.));;
let plusAD (a0,a1) (b0,b1) = (iPlus a0 b0, iPlus a1 b1)
let multAD (a0,a1) (b0,b1) = (iMult a0 b0, iPlus (iMult a0 b1) (iMult a1 b0))
let divAD (a0,a1) (b0,b1) = (iDiv a0 b0, iDiv (iSub (iMult (a0) (b1)) (iMult (a1) (b0))) (iPow (b0) 2));;
let negAD (a0,a1) = (iNeg a0, iNeg a1);;
let subAD a b = plusAD a (negAD b);;
let cosAD (a,b) = (iCos a, iNeg (iMult b (iSin a)));;
let sinAD (a,b) = (iSin a, iMult b (iCos a));;
let expAD (a,b) = (iExp a, iMult b (iExp a));;
let powAD ((a,b),n) = (iPow a n,iMult (thin (foi n)) (iMult b (iPow a (n-1))));;
let varFunAD f k (a,b) = raise Not_found;;

(* symbolic functions to automatic differentiation of order 1 functions *)
let sym2ad1= makeF constAD varAD plusAD multAD negAD subAD divAD cosAD sinAD expAD powAD varFunAD;;



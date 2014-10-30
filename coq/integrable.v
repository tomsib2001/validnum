(* This file aims to build tools to prove in  the most automatic manner 
possible the integrability of functions *)
Require Import List.
Require Import Reals.
Require Import Interval_xreal.
Require Import Interval_bisect.
(* Require Import Interval_interval. *)
(* Require Import Interval_definitions. *)
Require Import Interval_interval_float.
Require Import Interval_float_sig.
Require Import Interval_interval_float_full.
Require Import Coquelicot.

Require Import ssreflect ssrfun ssrbool.

Module ExIntegral (F : FloatOps with Definition even_radix := true).

Module FInt := FloatIntervalFull F.
Module IntA := IntervalAlgos FInt.

Import FInt.

Definition toReal_Xfun f := (fun x => match f(Xreal x) with | Xreal r => r
                                     | Xnan => R0 end).

Definition ex_RInt_Xreal (f : ExtendedR -> ExtendedR) (a b : R) := let g := toReal_Xfun f in(* (fun x => match f(Xreal x) with | Xreal r => r *)
                                     (* | Xnan => R0 end) *)  
ex_RInt g a b.
(* is_RInt (fun x => match f(Xreal x) with | Xreal r => r *)
(*                                      | Xnan => R0 end)  a b If. *)


Lemma UnaryNai : forall (o : unary_op) pow b0,
 unary (IntA.BndValuator.operations pow) o b0 <> I.nai ->
 b0 <> I.nai.
apply: unary_op_rec; intros pow;
try by case => /=.
intros prec0 i => /=.
induction pow.
- by rewrite /power_int; case: i => //=.
- rewrite /power_int /=; induction p.
    +  rewrite /I.power_pos; move: IHp; by case : i.
    +  rewrite /I.power_pos; move: IHp; by case : i.
    +  rewrite /I.power_pos; by case : i.
- by rewrite /power_int; case: i => //=.
Qed.

Lemma InvEpsilon a0 a b :
  (forall x0, T.toR a <= x0 <= T.toR b ->  unary ext_operations Inv (a0 (Xreal x0)) <> Xnan) -> 
exists epsilon, epsilon > 0 /\ forall x0, T.toR a <= x0 <= T.toR b -> match a0 (Xreal x0) with Xreal r0 => Rabs r0 >= epsilon | Xnan => True end.
Proof.
Admitted.



Lemma IntOpUnary a b a0 o : ex_RInt_Xreal a0 (T.toR a) (T.toR b) ->
(forall x0, T.toR a <= x0 <= T.toR b ->  unary ext_operations o (a0 (Xreal x0)) <> Xnan) -> 
  ex_RInt_Xreal (fun x : ExtendedR => unary ext_operations o (a0 x))
     (T.toR a) (T.toR b).
Proof.
intros HInta0.
case: o => z /=; rewrite /ex_RInt_Xreal .
apply: (ex_RInt_ext (fun x => (-1) * ((toReal_Xfun a0) x))).
intros x _; rewrite /toReal_Xfun; case: (a0 (Xreal x)) => //=; first by ring.
 intros r; ring.
apply: ex_RInt_scal; exact: HInta0.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
(* intros HnXnan. *)
admit.
admit.
Qed.

(* the following statement is false at least because of the forall n: it becomes fatally false when n > length of the list *)
Lemma notNaiInt :
  forall prec formula bounds a b,
    (forall n, nth n (IntA.BndValuator.eval prec formula ((I.bnd a b)::map IntA.interval_from_bp bounds)) I.nai <> I.nai) -> 
    ex_RInt_Xreal (fun x => nth 0 (eval_ext formula (x::map IntA.xreal_from_bp bounds)) Xnan) (T.toR a) (T.toR b).
Proof.
intros prec formula bounds a b Hnnai.
unfold eval_real, eval_generic.
About eval_inductive_prop_fun.
apply: (eval_inductive_prop_fun _ _ (fun f yi => (yi <> I.nai) -> ex_RInt_Xreal f (T.toR a) (T.toR b)) Xnan I.nai ext_operations (IntA.BndValuator.operations prec)).
intros a1 a2 Ha12 b0 Hb0.
intros Hbnai.
rewrite /ex_RInt_Xreal.
have HIf :=  (Hb0 Hbnai).
apply (ex_RInt_ext (toReal_Xfun a1)) => //.
intros x _; by rewrite /toReal_Xfun; rewrite Ha12.
by [].
intros o a0 b0 H1 H2.
have Ha0Int := (H1 (UnaryNai o prec b0 H2)).
apply: IntOpUnary => // .
intros x0 Hx0 Habs.
apply: H2.
rewrite /I.nai.
Admitted.
(* (* have -> :  I.nai = Interval_interval.Inan by []. *) *)
(* About xreal_ssr_compat.contains_Xnan. *)
(* Check (@xreal_ssr_compat.contains_Xnan  (unary (IntA.BndValuator.operations prec) o b0)) . *)

(* case => a0 i Hinnai HNegnai. *)
(* SearchAbout Neg. *)

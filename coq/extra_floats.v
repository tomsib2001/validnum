Require Import Reals Coquelicot.
Require Import Fcore.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.

Require Import extra_interval.

Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ExtraFloatInterval (F : FloatOps with Definition even_radix := true).

Module FInt := FloatIntervalFull F.

Import FInt.

Lemma F_realP (f : F.type) : 
 reflect (I.convert_bound f = Xreal (T.toR f)) (F.real f).
Proof.
have := (F.real_correct f); rewrite /I.convert_bound /T.toR.
by case: (F.toF f)=> [||y z t] ->; constructor. 
Qed.

Lemma contains_convert_bnd_l (a b : F.type) :  (F.real a) -> (F.real b) -> 
  (T.toR a) <= (T.toR b) -> contains (I.convert (I.bnd a b)) (I.convert_bound a).
Proof.
case/F_realP => hra /F_realP [hrb] hleab; rewrite hra; apply: le_contains.
  by rewrite hra; apply: le_lower_refl.
by rewrite hrb.
Qed.

Lemma contains_convert_bnd_r (a b : F.type) :  (F.real a) -> (F.real b) -> 
  (T.toR a) <= (T.toR b) -> contains (I.convert (I.bnd a b)) (I.convert_bound b).
Proof.
case/F_realP => hra /F_realP [hrb] hleab; rewrite hrb; apply: le_contains.
  rewrite hra /le_lower /=; exact: Ropp_le_contravar.
rewrite hrb; exact: le_upper_refl.
Qed.

Lemma contains_convert_bnd (a b : F.type) r :  (F.real a) -> (F.real b) -> 
  (T.toR a) <= r <= (T.toR b) -> contains (I.convert (I.bnd a b)) (Xreal r).
Proof.
case/F_realP => hra /F_realP [hrb] hleab; apply: le_contains.
  by rewrite hra /le_lower /=; apply: Ropp_le_contravar; case: hleab.
by rewrite hrb /le_lower /=; case: hleab.
Qed.

(* Remember : T.toR = fun x : F.type => proj_val (FtoX (F.toF x)) *)
(* The statement of I.midpoint_correct is really clumsy *)
(* contains_le is also difficult to use... *)
(* I.midpoint_correct should be stated using T.toR *)
(* le_lower should either be a notation over le_upper or a new def *)
(* so that it simplifies to <= or else provide suitable lemmas *)
Lemma midpoint_bnd_in (a b : F.type) :
  F.real a -> F.real b -> T.toR a <= T.toR b-> 
  T.toR a <= T.toR (I.midpoint (I.bnd a b)) <= T.toR b.
Proof.
move => hra hrb hleab; set iab := I.bnd a b; set m := I.midpoint iab.
pose xa := I.convert_bound a; pose xb := I.convert_bound b.
have non_empty_iab : exists x : ExtendedR, contains (I.convert iab) x.
  by exists xa; apply: contains_convert_bnd_l.  
have [isr_xm xm_in_iab {non_empty_iab}] := I.midpoint_correct iab non_empty_iab.
rewrite -/(T.toR m) in isr_xm. (* I.midpoint_correct is ill stated *)
have [le_xa_xm le_xm_xb {xm_in_iab}] := contains_le xa xb _ xm_in_iab.
split; last by move: le_xm_xb; rewrite isr_xm /xb (F_realP _ hrb).
move: le_xa_xm.
by rewrite isr_xm /xa (F_realP _ hra) /le_lower /=; exact: Ropp_le_cancel. 
Qed.

Definition thin (f : F.type) : FInt.type := 
  if F.real f then I.bnd f f else I.nai.

(* Remember: (I.convert_bound x) is (FtoX (F.toF x)) *)
Lemma thin_correct (f : F.type) : 
 contains (I.convert (thin f)) (I.convert_bound f).
Proof.
rewrite /thin I.real_correct.
case ex: (I.convert_bound f) => [|r] //=.
rewrite ex; split; exact: Rle_refl.
Qed.

Lemma thin_correct_toR (f : F.type) : 
  (F.real f) -> contains (I.convert (thin f)) (Xreal (T.toR f)).
Proof. move/F_realP<-; exact: thin_correct. Qed.

End ExtraFloatInterval.
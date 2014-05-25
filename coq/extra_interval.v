Require Import Reals.
Require Import Coquelicot.
Require Import extra_coquelicot.

Require Import Interval_xreal.

Require Import Interval_interval.

Require Import ssreflect.

Section Integral.

Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.
Hypothesis fint : ex_RInt f ra rb.

Lemma XRInt1_correct (i : interval) : 
  (forall x, ra <= x <= rb -> contains i (Xreal (f x))) ->
  contains i (Xreal ((RInt f ra rb) / (rb - ra))).
Proof.
move=> hif.
have sbapos : rb - ra > 0 by apply: Rgt_minus.
case: i hif => [|[|?] [|?]] //= hif; split => //.
- by apply: RInt_le_r => // x /hif [].
- by apply: RInt_le_l => // x /hif [].
- by apply: RInt_le_l => // x /hif [].
- by apply: RInt_le_r => // x /hif [].
Qed.

End Integral.

Section ExtensionOfFunctionsToXreal.

Variable (f : R -> R).

Definition toXreal_fun : ExtendedR -> ExtendedR := 
  fun x => match x with Xnan => Xnan | Xreal r => Xreal (f r) end.

(* Interval_xreal.extension should be boolean *)
Lemma xreal_extension_toXreal_fun : Interval_xreal.extension f toXreal_fun.
Proof. by case. Qed.

 
End ExtensionOfFunctionsToXreal.

Section XReals.

(* There are probably more instances missing. *)
Lemma le_lower_refl (r : R) : le_lower (Xreal r) (Xreal r).
Proof. by rewrite /=; apply: Rle_refl. Qed.

Lemma le_upper_refl (r : R) : le_upper (Xreal r) (Xreal r).
Proof. by rewrite /=; apply: Rle_refl. Qed.

End XReals.




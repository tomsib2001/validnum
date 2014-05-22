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

Require Import Reals.
Require Import List.
Require Import Interval_missing.
Require Import ZArith.
Require Import Fcore.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Interval_bisect.

Require Import Coquelicot.

Require Import ssreflect.

Section ExtensionOfLoadedLibraries.

Section Integral.

Variable (V : CompleteNormedModule R_AbsRing).
Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.

Hypothesis fint : ex_RInt f ra rb.

(* Below : a couple of helper lemmas about maj/min of integrals *)
Lemma RInt_le_r (u : R) : (forall x : R, ra <= x <= rb -> f x <= u) ->
                          RInt f ra rb / (rb - ra) <= u.
Proof.
move=> hfu; apply/Rle_div_l;first by apply: Rgt_minus.
have -> : u * (rb - ra) = RInt (fun _ => u) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

Lemma RInt_le_l (l : R) : (forall x : R, ra <= x <= rb -> l <= f x) ->
                  l <= RInt f ra rb / (rb - ra).
Proof.
move=> hfl; apply/Rle_div_r; first by apply: Rgt_minus.
have -> : l * (rb - ra) = RInt (fun _ => l) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

Lemma ex_RInt_Chasles_sub (g : R -> V) (a b c d : R) :
 a <= b -> b <= c -> c <= d -> ex_RInt g a d -> ex_RInt g b c.
Proof.
move=> leab lebc lecd hiad; apply: (ex_RInt_Chasles_1 _ _ _ d) => //. 
by apply: (ex_RInt_Chasles_2 _ a) => //; split=> //; apply: (Rle_trans _ c).
Qed.

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

End ExtensionOfLoadedLibraries.

Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module Int := FloatIntervalFull F.
Module IntA := IntervalAlgos Int.

Import Int.

Definition thin (x : F.type) : Int.type := if F.real x then I.bnd x x else I.nai.

(* (I.convert_bound x) is (FtoX (F.toF x)) *)
Lemma thin_correct (x : F.type) : 
  contains (I.convert (thin x)) (I.convert_bound x).
Proof.
rewrite /thin I.real_correct.
case ex: (I.convert_bound x) => [|r] //=.
rewrite ex; split; exact: Rle_refl.
Qed.

Require Import ssrfun ssrbool.

Lemma F_realP (x : F.type) : 
  reflect (exists r, I.convert_bound x = Xreal r) (F.real x).
Proof.
have := (F.real_correct x); rewrite /I.convert_bound. 
case: (F.toF x)=> [||y z t] -> /=; constructor. 
- by case.
- by exists 0.
- by exists (FtoR F.radix y z t).
Qed.

SearchAbout Xcmp.

(* Lemma thin_consistent (a b : F.type) : F.real a = true -> F.real b = true -> *)
(*    T.toR a = T.toR b -> thin a = thin b. *)
(* Proof. *)
(* rewrite /thin => ha hb; rewrite ha hb.   *)
(* case/F_realP:ha => ra hra; case/F_realP: hb => rb hrb. *)
(* rewrite /T.toR /= -/(I.convert_bound a) -/(I.convert_bound b) hra hrb /=. *)
(* rewrite /I.bnd. *)
(* Search _ I.bnd. *)
(* Admitted. *)

Notation xreal_extension := Interval_xreal.extension.

Section IntervalIntegral.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

(* This is a std monadic operation. Does it exist somewhere in the libs? *)
Let g : ExtendedR -> ExtendedR := 
  fun x => match x with Xnan => Xnan | Xreal r => Xreal (f r) end.

(* g is a restriction of f as an extendedR function. *)
Hypothesis Hfgext : xreal_extension f g.

(* iF is an interval extension of g *)
Hypothesis HiFIntExt : I.extension g iF.

(* patch for Guillaume *)
Lemma le_lower_refl (ra : R) : le_lower (Xreal ra) (Xreal ra).
Proof.
rewrite /le_lower => /= . apply: Rle_refl.
Qed.

Lemma int_not_empty (a b : F.type) :  (F.real a) -> (F.real b) -> (T.toR a) <= (T.toR b) -> contains (I.convert (I.bnd a b)) (I.convert_bound a). 
Proof.
intros ha hb hleab.
case/F_realP : ha => ra hra. rewrite hra.
apply: le_contains.
  by rewrite hra; apply: le_lower_refl.
case/F_realP: hb => rb hrb. rewrite hrb /=.
move: hleab.
rewrite /T.toR. 
by rewrite -![(FtoX (F.toF _))]/(I.convert_bound _) hra hrb.
Qed.


Section OrderOne.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b).

(* a <= b *)
Hypothesis  Hleab : T.toR a <= T.toR b.



(* The conversion of a and b to ExtendedR avoids Nan *)
Hypothesis ha : F.real a.
Hypothesis hb : F.real b.
(* Hypothesis ha : I.convert_bound a = Xreal (T.toR a). *)
(* Hypothesis hb : I.convert_bound b = Xreal (T.toR b). *)



(* Guillaume says that operations on F.type like (F.cmp a b = Xlt)
  should not occur in hypotheses or proofs, unless we prove a spec on 
  a functions (like below in the conclusion. We should specify these 
  properties wrt to their behaviour in ExtendedR: 
 (F.cmp a b = Xlt) is replaced by (T.toR a <= T.toR b).
  Warning, as we saw in the def of thin, we should exclude the possibility 
  of a I.nai value, hence the extra hypotheses that I.convert gives a 'real
  real'. Note,  (I.convert_bound a) = Xreal (T.toR a) is the most convenient
  phrasing since it allows for rewriting in later steps of the proofs. *)

(* Why the name xreal_ssr_compat.Xmul_Xreal ? *)

(* we should better tune the order of the arguments of 
  I.extension2. In the current state, at line (* 1 *)
   we cannot apply I.sub_correct in the 
  present case because we need either a first conversion step to make Xsub
  explicit, or providing explicitely the arguments, which come after prec and
  interval arguments:  apply: (I.sub_correct _ _ _ (Xreal rb) (Xreal ra)) *)


Lemma toR_is_conv_bound (b0 : F.type) : (F.real b0) -> Xreal (T.toR b0) = I.convert_bound b0.
move => hb0.
case/F_realP: hb0 => rb1 hrb1. 
    by rewrite hrb1  /T.toR  -[(FtoX (F.toF _))]/(I.convert_bound _) hrb1.
Qed.

Lemma thin_correct_toR (b0 : F.type) : (F.real b0) -> contains (I.convert (thin b0)) (Xreal (T.toR b0)).
Proof.
by move => hb0; rewrite toR_is_conv_bound //; exact: thin_correct.
Qed.    

Lemma integral_order_one_correct :
  contains
    (I.convert ((I.mul prec (iF (I.bnd a b)) (I.sub prec (thin b) (thin a)))))
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
case elu: (iF (I.bnd a b)) => // [l u].
set ra := T.toR a; set rb := T.toR b; fold ra rb in Hintegrable, ha, hb, Hleab.
set Iab := RInt _ _ _.
case: (Rle_lt_or_eq_dec _ _ Hleab) => [Hleab1 | Heqab].
  + have -> : Xreal Iab = Xmul (Xreal (Iab / (rb - ra))) (Xreal (rb - ra)).
       rewrite xreal_ssr_compat.Xmul_Xreal; congr Xreal; field.
       by apply: Rminus_eq_contra; apply: Rlt_dichotomy_converse; right.
    apply: I.mul_correct.
    - apply: XRInt1_correct => // x hx. rewrite -elu -[Xreal (f x)]/(g (Xreal x)).
      have iFab := HiFIntExt (I.bnd a b) (Xreal x).
      by apply: iFab; rewrite /=; case/F_realP: ha => ra1 hra; 
         case/F_realP: hb => rb1 hrb; rewrite hra hrb; move: hx; 
         rewrite /ra /rb /T.toR -![(FtoX (F.toF _))]/(I.convert_bound _) hra hrb.
    - rewrite -[Xreal (rb - ra)]/(Xsub (Xreal rb) (Xreal ra)). (* 1 *)
      apply: I.sub_correct.
        exact: thin_correct_toR.
      (*   have -> : Xreal rb = I.convert_bound b. case/F_realP: hb => rb1 hrb1.  *)
      (*     by rewrite hrb1 /rb /T.toR  -[(FtoX (F.toF _))]/(I.convert_bound _) hrb1. *)
      (* exact: thin_correct. *)
      exact: thin_correct_toR.
  (* + rewrite (why_isnt_this_already_proved a b Heqab). *)
    have -> : Iab = 0; first by unfold Iab; rewrite Heqab RInt_point // .
    have ->: Xreal 0 =Xmul(g (Xreal (T.toR a))) (Xreal 0).
    rewrite /= Rmult_0_r // .
    apply: I.mul_correct. 
      -  by rewrite -elu; apply: HiFIntExt; rewrite toR_is_conv_bound //;  apply: int_not_empty.     
         have <- :  Xsub (Xreal rb) (Xreal rb) = Xreal 0 by congr Xreal; ring.
      -  by apply: I.sub_correct; try (exact: thin_correct_toR); try (rewrite -?Heqab; exact: thin_correct_toR).
Qed.

End OrderOne.

Fixpoint integral (depth : nat) (a b : F.type) := 
  let int := I.bnd a b in
  match depth with
    | O => I.mul prec (iF (int)) (I.sub prec (thin b) (thin a))
    | S n => let m := I.midpoint int in
             let i1 := integral n a m in
             let i2 := integral n m b in
             I.add prec i1 i2 
  end
.

Section integral.

(* Variables (a b : F.type). *)

(* Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b). *)


(* Hypothesis  Hltab : T.toR a < T.toR b. *)


Lemma midpoint_in_int (a b : F.type) : (F.real a) -> (F.real b) -> (T.toR a) <= (T.toR b)-> T.toR a <= T.toR (I.midpoint (I.bnd a b)) <= T.toR b.
Proof.
move => hra hrb hleab.
have := contains_le (I.convert_bound a) (I.convert_bound b) (I.convert_bound (I.midpoint (I.bnd a b))) => h1.
have h2 : exists x : ExtendedR, contains (I.convert (I.bnd a b)) x.
  by exists (I.convert_bound a); apply: int_not_empty => //.  
have h3: contains (Interval_interval.Ibnd (I.convert_bound a) (I.convert_bound b))
         (I.convert_bound (I.midpoint (I.bnd a b))).
rewrite  -I.bnd_correct.  admit.
have := (I.midpoint_correct (I.bnd a b) h2) => h4.
elim : h4 => h5 h6.
have h7 := (h1 h6) .
elim: h7 => h8 h9.
split.
  - move : h8; case /F_realP: hra => ra hra;
    by rewrite /le_lower /le_upper h5 hra /Xneg /T.toR -![(FtoX (F.toF _))]/(I.convert_bound _) hra; exact: Ropp_le_cancel.
  - move: h9; case /F_realP: hrb => rb hrb;
    by rewrite  /le_upper h5 hrb /Xneg /T.toR -![(FtoX (F.toF _))]/(I.convert_bound _) hrb. 
Qed.


Lemma convboundisxReal (a b : F.type) :  (F.real a) -> (F.real b) -> I.convert_bound (I.midpoint (I.bnd a b)) = Xreal (T.toR (I.midpoint (I.bnd a b))).
intros ha hb.
have := (I.midpoint_correct (I.bnd a b)) => h.
have hnempty: exists x, contains (I.convert (I.bnd a b)) (x).
admit.
elim : (h hnempty) => h1 h2.
apply: h1.
Qed.


(* Hypothesis ha : I.convert_bound a = Xreal (T.toR a). *)
(* Hypothesis hb : I.convert_bound b = Xreal (T.toR b). *)



Lemma integral_correct (depth : nat) (a b : F.type) :
  ex_RInt f (T.toR a) (T.toR b) -> T.toR a <= T.toR b ->
  (F.real a) ->
  (F.real b) ->
  contains (I.convert (integral depth a b)) 
           (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
elim: depth a b => [ | k Hk]; move => a b Hintegrable Hleab ha hb.
(* case: (Rle_lt_or_eq_dec _ _ Hleab) => [Hleab1 | Hleab]. *)
  admit. (* rewrite /integral. case/F_realP: ha => ra hra; case/F_realP: hb => rb hrb; apply: integral_order_one_correct => // . *)
  rewrite /T.toR -![(FtoX (F.toF _))]/(I.convert_bound _).

rewrite /integral -/integral.
set midpoint := I.midpoint (I.bnd a b).
have hIl : ex_RInt f (T.toR a) (T.toR midpoint).
  by apply:  (ex_RInt_Chasles_1 _ _ _ (T.toR b)) => //; apply: midpoint_in_int.
have hIr : ex_RInt f (T.toR midpoint) (T.toR b).
  by apply:  (ex_RInt_Chasles_2 f (T.toR a))=> //; apply: midpoint_in_int.
have -> : RInt f (T.toR a) (T.toR b) =
  RInt f (T.toR a) (T.toR midpoint) + RInt f (T.toR midpoint) (T.toR b). 
  by rewrite RInt_Chasles.
set I1 := RInt _ _ _. set I2 := RInt _ _ _.
have hm : I.convert_bound midpoint = Xreal (T.toR midpoint).
  move=> {k Hk Hintegrable hIl hIr I1 I2}.
  rewrite /T.toR.
  rewrite -![(FtoX (F.toF _))]/(I.convert_bound _).
  suff /I.midpoint_correct []: 
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by [].
  by exists (I.convert_bound a); apply: int_not_empty => //; apply/F_realP.
  have hrmidpoint : F.real midpoint.
  case -> : F_realP => // habs .
    rewrite hm in habs.
    elim : habs. by exists (T.toR midpoint).
    by rewrite -[Xreal (_ + _)]/(Xadd (Xreal I1) (Xreal I2)); apply: I.add_correct; apply: Hk => // ;have := midpoint_in_int a b ha hb Hleab => hineqs; elim: hineqs => in1 in2.
Qed.
 
About I.midpoint_correct.
Search _ (Xreal (proj_val _)).

Search _ I.midpoint.


(* rewrite /I.convert_bound /midpoint /I.midpoint. *)

(* have -> : I.bnd a b = Ibnd a b by rewrite /I.bnd. *)
(* Search _ F.cmp. *)

End integral.

End IntervalIntegral.

End IntegralTactic.

(* Module Test := IntegralTactic  *)

(* End Test. *)
Require Import List.
Require Import Reals.
Require Import Fourier.
Require Import Interval_missing.
(* Require Import ZArith. *) (* seems unnecessary?*)
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

Require Import extra_coquelicot.
Require Import extra_interval.
Require Import extra_floats.

Require Import ssreflect ssrfun ssrbool.

Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module Extras := ExtraFloatInterval F.

Module FInt := FloatIntervalFull F.
Module IntA := IntervalAlgos FInt.

Import FInt.
Import Extras.

Export FInt.

Section IntervalIntegral.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

(* This is a std monadic operation. Does it exist somewhere in the libs? *)
Let g := toXreal_fun f. 

(* g is a restriction of f as an extendedR function. *)
Let Hfgext := xreal_extension_toXreal_fun f. 

(* iF is an interval extension of g *)
Hypothesis HiFIntExt : I.extension g iF.

Section OrderOne.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b).

(* a <= b *)
Hypothesis  Hleab : T.toR a <= T.toR b.

(* a and b are no Nan. This cannot be deduced from Hleab *)
Hypothesis ha : F.real a.
Hypothesis hb : F.real b.

(* we should better tune the order of the arguments of 
  I.extension2. In the current state, at line (* 1 *)
   we cannot apply I.sub_correct in the 
  present case because we need either a first conversion step to make Xsub
  explicit, or providing explicitely the arguments, which come after prec and
  interval arguments:  apply: (I.sub_correct _ _ _ (Xreal rb) (Xreal ra)) *)

Lemma integral_order_one_correct :
  contains
    (I.convert ((I.mul prec (iF (I.bnd a b)) (I.sub prec (thin b) (thin a)))))
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
case elu: (iF (I.bnd a b)) => // [l u].
set ra := T.toR a; set rb := T.toR b; fold ra rb in Hintegrable, ha, hb, Hleab.
set Iab := RInt _ _ _.
case: (Rle_lt_or_eq_dec _ _ Hleab) => [Hleab1 | Heqab]; last first.
  + have -> : Xreal Iab = Xmul (g (Xreal ra)) (Xsub (Xreal rb) (Xreal ra)).
      rewrite /Iab Heqab /= RInt_point; congr Xreal; ring.
    apply: I.mul_correct; last by apply: I.sub_correct; exact: thin_correct_toR.
    rewrite -elu; apply: HiFIntExt;  move/F_realP: ha<-.
    by apply: contains_convert_bnd_l.
  + have -> : Xreal Iab = Xmul (Xreal (Iab / (rb - ra))) (Xreal (rb - ra)).
       rewrite xreal_ssr_compat.Xmul_Xreal; congr Xreal; field.
       by apply: Rminus_eq_contra; apply: Rlt_dichotomy_converse; right.
    apply: I.mul_correct; last first.
    - rewrite -[Xreal (rb - ra)]/(Xsub (Xreal rb) (Xreal ra)). (* 1 *)
      apply: I.sub_correct; exact: thin_correct_toR.
    - apply: XRInt1_correct => // x hx; rewrite -elu -[Xreal _]/(g (Xreal x)).
      apply: HiFIntExt; exact: contains_convert_bnd.
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

(* Definition round_down := round radix2 rnd_DN (F.prec prec). *)
(* Definition round_up := round radix2 rnd_UP (F.prec prec). *)


Section integral.

Lemma integral_correct (depth : nat) (a b : F.type) :
  ex_RInt f (T.toR a) (T.toR b) -> 
  T.toR a <= T.toR b ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral depth a b)) (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
elim: depth a b => [ | k Hk] a b Hintegrable Hleab ha hb.
  by apply: integral_order_one_correct => //.
set midpoint := I.midpoint (I.bnd a b).
have hIl : ex_RInt f (T.toR a) (T.toR midpoint).
  by apply:  (ex_RInt_Chasles_1 _ _ _ (T.toR b)) => //; apply: midpoint_bnd_in.
have hIr : ex_RInt f (T.toR midpoint) (T.toR b).
  by apply:  (ex_RInt_Chasles_2 f (T.toR a))=> //; apply: midpoint_bnd_in.
have -> : RInt f (T.toR a) (T.toR b) =
  RInt f (T.toR a) (T.toR midpoint) + RInt f (T.toR midpoint) (T.toR b). 
  by rewrite RInt_Chasles.
set I1 := RInt _ _ _; set I2 := RInt _ _ _.
rewrite /integral -/integral -[Xreal (_ + _)]/(Xadd (Xreal I1) (Xreal I2)). 
have [in1 in2] := midpoint_bnd_in ha hb Hleab.
suff hm : F.real (I.midpoint (I.bnd a b)) by apply: I.add_correct; apply: Hk.
  suff /I.midpoint_correct []: 
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by move/F_realP.
  exists (I.convert_bound a); apply: contains_convert_bnd_l => //; exact/F_realP.
Qed.

End integral.

End IntervalIntegral.

End IntegralTactic.

Require Import Interval_tactic.
Require Import Interval_generic_ops.
Require Import Interval_transcend.

Module F :=  GenericFloat Radix2.
Module FInt := FloatIntervalFull F.

Import FInt.

Module FIntervalTactic := IntervalTactic F.
Import FIntervalTactic.


Module TestIntegral := IntegralTactic F.

Import TestIntegral.FInt.
Import TestIntegral.

Ltac interval_inclusion_by_computation :=
  rewrite /= /le_lower /=; split; fourier.

Ltac proves_interval_extention := idtac. 

Ltac proves_RInt := idtac.

(* this one should be an application of an implication which reduces the problem
    to computation. *)
Ltac proves_bound_order := rewrite /T.toR /=; fourier.
 
Ltac apply_interval_correct :=
(* // kills the subgoals F.real b with b a bound of the integral. *)
(* these are obtained by Private.get_float in thebody of intergal_tac,
   hopefully it is always automatically discharged. *)
  apply: integral_correct => //;
  [proves_interval_extention | proves_RInt | proves_bound_order].

Ltac integral_tac_test g prec depth :=
match goal with
| |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c => 
  let v := Private.get_float a in
  let w := Private.get_float c in
  let lb := Private.get_float ra in
  let ub := Private.get_float rb in
  change (contains (I.convert (I.bnd v w)) (Xreal (RInt f ra rb)));
  apply: (subset_contains (I.convert (integral prec g depth lb ub))) end.

Ltac integral_tac g prec depth :=
match goal with
| |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c => 
  let v := Private.get_float a in
  let w := Private.get_float c in
  let lb := Private.get_float ra in
  let ub := Private.get_float rb in
  change (contains (I.convert (I.bnd v w)) (Xreal (RInt f ra rb)));
  apply: (subset_contains (I.convert (integral prec g depth lb ub)));
 (* at this point we generate two subgoals: *)
 (*- the first one succeeds by computation if the interval computed by integral *)
 (*     is sharp enough wrt to the user's problem *)
 (*   - the second one is always provable by application of interval_correct *) 
 [interval_inclusion_by_computation | apply_interval_correct]
 | _ => fail 100 "rate" end.
 

(* For tests and benchmarks *)
Definition prec10 := (10%positive) : F.precision.

Lemma test (f := fun x : R => x) : (0 <= RInt f 0 1 <= 7/8)%R.
Proof.
pose g (x : I.type) := x.
pose prec : F.precision := prec10.
pose depth : nat := 1%nat. 
integral_tac g prec depth.
  - intros b x; by case : x.
  (* - admit. (* sera fourni par la tactique *) *)
  - admit. (* pour l'instant on laisse à l'utilisateur *)
Admitted.

Lemma test2 (f := fun x : R => Rtrigo_def.exp x) : (0 <= RInt f 0 1 <= 7/8)%R.
Proof.
pose g (x : I.type) := FInt.exp prec10 x.
pose prec : F.precision := prec10.
pose depth : nat := 0%nat.
integral_tac_test g prec depth.
rewrite /g. rewrite /integral. rewrite /exp.
rewrite /=.

Definition foo f n a b := 
  Eval vm_compute in (integral (prec10) f n a b).

(* Definition exp10 := Eval lazy in (Int.exp prec10). long... *)

Time Eval vm_compute in (foo (Int.exp prec10) 10 F.zero (F.fromZ 1)).

Time Eval vm_compute in integral (prec10) (Int.exp prec10) 10 F.zero (F.fromZ 1).

Time Eval vm_compute in integral (prec10) (Int.exp prec10) 3 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 824 (-9)) (Float F.radix false 938 (-9)) *)
(* [1.609375,1.83203125]*)
(* Finished transaction in 0. secs (0.064004u,0.s) *)

Time Eval vm_compute in integral (prec10) (Int.exp prec10) 6 F.zero (F.fromZ 1).
(*  Ibnd (Float F.radix false 870 (-9)) (Float F.radix false 890 (-9)) *)
(* [1.69921875,1.73828125]*)
(* Finished transaction in 1. secs (0.552034u,0.s) *)

Time Eval vm_compute in integral (prec10) (Int.exp prec10) 10 F.zero (F.fromZ 1).
(* (Float F.radix false 875 (-9)) (Float F.radix false 885 (-9))*)
(* [1.708984375,1.728515625] *)
(* Finished transaction in 8. secs (8.400525u,0.004s)*)


Definition prec30 := (30%positive) : F.precision.

Time Eval vm_compute in integral (prec30) (Int.exp prec30) 12 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 922382922 (-29)) *)
(*          (Float F.radix false 922608152 (-29)) *)
(*      : f_interval F.type *)
(* Finished transaction in 119. secs (118.387399u,0.008001s) *)

Time Eval vm_compute in integral (prec30) (Int.exp prec30) 15 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 922481451 (-29)) *)
(*          (Float F.radix false 922509615 (-29)) *)
(*      : f_interval F.type *)
(* [1.7182555999606848,1.7183080594986677] *)
(* Finished transaction in 1119. secs (1114.773669u,0.288018s) *)

Time Eval vm_compute in integral (prec30) (Int.exp prec30) 3 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 866040413 (-29)) *)
(*          (Float F.radix false 981352359 (-29)) *)
(*      : f_interval F.type *)
(* [1.6131259743124247,1.8279112111777067] *)
(* Finished transaction in 0. secs (0.232014u,0.s) *)

Time Eval vm_compute in integral (prec30) (Int.exp prec30) 6 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 915307301 (-29)) *)
(*          (Float F.radix false 929721300 (-29)) *)
(*      : f_interval F.type *)
(* [1.7048927042633295,1.7317408695816994] *)
(* Finished transaction in 2. secs (1.744109u,0.s) *)

Time Eval vm_compute in integral (prec30) (Int.exp prec30) 10 F.zero (F.fromZ 1).
 (*  Ibnd (Float F.radix false 922045164 (-29))
         (Float F.radix false 922946047 (-29))
     : f_interval F.type *)
(* [1.7174429520964622,1.7191209774464369] *)
(*Finished transaction in 28. secs (28.685793u,0.060004s) *)


Definition prec100 := (100%positive) : F.precision.

Time Eval vm_compute in integral (prec100) (Int.exp prec100) 3 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 1022440057055222484579125177733 (-99)) *)
(*          (Float F.radix false 1158576369005682997163092575753 (-99)) *)
(*      : f_interval F.type *)
(* [1.6131259778856115,1.827911206442992]  *)
(* Finished transaction in 1. secs (1.584099u,0.s) *)


Time Eval vm_compute in integral (prec100) (Int.exp prec100) 6 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 1080604133619477846151951543090 (-99)) *)
(*          (Float F.radix false 1097621172613285410224947467848 (-99)) *)
(*      : f_interval F.type *)
(* [1.7048927100652569,1.7317408636349296] *)
(* Finished transaction in 14. secs (13.356834u,0.016001s) *)

Time Eval vm_compute in integral (prec100) (Int.exp prec100) 10 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 1088558799688262396851727958906 (-99)) *)
(*          (Float F.radix false 1089622364625375369606290204212 (-99)) *)
(*      : f_interval F.type *)
(* [1.7174429602167616,1.719120969814866] *)
(* Finished transaction in 229. secs (228.658291u,0.012001s) *)



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

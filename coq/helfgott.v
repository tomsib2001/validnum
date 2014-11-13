Require Import List.
Require Import Reals.

Require Import extra_coquelicot.
Require Import extra_interval.
Require Import extra_floats.

Require Import Interval_tactic.
Require Import Interval_generic_ops.
Require Import Interval_transcend.
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.

Require Import Coquelicot.
Require Import BigZ. (* for precision *)

Require Import ssreflect ssrfun ssrbool.
Require Import integrals.

Module F := SpecificFloat BigIntRadix2.

Module TestExtrasFloats := ExtraFloatInterval F.

Import TestExtrasFloats.

Definition one := F.fromZ 1%Z.
Definition two := F.fromZ 2%Z.
Definition zero := F.fromZ 0%Z.
Definition half := Float 1%bigZ (-1)%bigZ.

Definition prec30 := (30%bigZ) : F.precision.
Definition prec := prec30.

Require Import poly_datatypes.
Require Import poly_inst_seq.
Require Import taylor_model_int_sharp.
Require Import taylor_model_float_sharp.
Require Import coeff_inst.
Require Import rpa_inst.
Require Import poly_bound.
Require Import Interval_interval_float_full.
Module I := FloatIntervalFull F.

Module PolX := ExactSeqPolyMonomUp FullXR.
Module Link := LinkSeqPolyMonomUp I.
Module PolI := SeqPolyMonomUpInt I.
Module PolF := SeqPolyMonomUpFloat F.
Module Bnd := PolyBoundHorner I PolI PolX Link.

Module Import TMF := TaylorModelFloat F PolF I PolI PolX Link Bnd.

Print TM.

Definition X0 := (thin one).
Definition epsilon := (Float 1%bigZ (-10)%bigZ).
Definition X := (I.bnd epsilon (one)).
Definition deg := 10%nat.
Definition tm_x2 := TM.TM_power_int prec 2%Z (thin one) (X) deg. (* (x - x0) pow 2 *)
Eval vm_compute in i_eval prec (TM.RPA.approx tm_x2)  (thin two).
Definition negx2div2 := TM.TM_div_mixed_r prec tm_x2 (I.neg (thin (Float 1%bigZ (1)%bigZ))). (* - ((x - x0) pow 2) / 2 *)
Definition expterm := TM.TM_comp prec (TM.TM_exp prec) negx2div2 X0 (I.sub prec X (thin one)) deg. (* exp (- ((x - x0) pow 2) / 2) *)
Eval vm_compute in i_eval prec (TM.RPA.approx expterm)  (I.sub prec (thin half) (thin one)).
Definition logterm := TM.TM_ln prec X0 X deg. (* ln (x - x0) *)
Definition integrand := TM.TM_mul prec (expterm) (TM.TM_mul prec tm_x2 logterm X0 X deg) X0 X deg. (* exp (- ((x - x0) pow 2) / 2) (ln (x - x0) ) *)
Definition integrated_term := TM.TM_integral prec X0 X integrand .
Eval vm_compute in i_eval prec (TM.RPA.approx integrated_term)  (I.sub prec (thin one)(thin one)).
Check integrated_term.
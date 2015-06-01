Require Import List.
Require Import Reals.
Require Import Fourier.
Require Import Interval_missing.
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

Require Import extra_interval.
Require Import extra_floats.

Require Import ssreflect ssrfun ssrbool.


Module Examples (F : FloatOps with Definition even_radix := true).

Module Extras := ExtraFloatInterval F.

Import Extras.


(* Module FInt := FloatIntervalFull F. *)
(* Module IntA := IntervalAlgos FInt. *)

(* Import FInt. *)

Locate "~~".

(* our type of intervals is this with A := F.type *)
(* Inductive f_interval (A : Type) : Type := *)
(*     Inan : f_interval A | Ibnd : A -> A -> f_interval A *)

Definition I0 := Ibnd F.zero F.zero. 

Definition Flt (x y : F.type) :=
  match F.cmp x y with
    | Xlt => true
    | _ => false
  end.

(* etc. *)

About FInt.Flt.
Print FInt.I.type.
Print f_interval.
SearchAbout (f_interval _ -> f_interval _ -> bool).
Print FInt.I.subset.

Definition iLt (i1 i2 : FInt.I.type) := 
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Flt r1 l2) && (Flt l1 r2)
       else false
  else false.

Definition iGt (i1 i2 : FInt.I.type) :=
  iLt i2 i1.
 
Print pair.
Definition foo (n m : nat) :=
  match (n, m) with
  | pair (S O) l => l
  | _ => O
end.

Notation intervalle := FInt.I.type.

Search "join".

Definition compare (x y a b : intervalle) := 
  if iLt x y then a else 
    if iGt x y then b else
      FInt.I.join a b.

Search "nan" in F.
SearchAbout F.type.

Variable prec : F.precision.
Variable rd : rounding_mode.
Print F.
Definition Fone := F.fromZ 1.

(* pasted comment from C++ code: *)
(* returns a point between x and y.  Rounding is not material here. *)
Definition avgwt (x y : intervalle) (w : F.type) : F.type :=
  match x,y with
    | Inan,_ => F.nan
    | _,Inan => F.nan
    | Ibnd x1 x2,Ibnd y1 y2 => 
      F.add rd prec (F.mul rd prec (F.sub rd prec Fone w) x2) (F.mul rd prec w y1)
  end.


Definition step1 (y1 h0 : intervalle) : bool := true.

End Examples.
(* Require Import Interval_tactic. *)
(* Require Import Interval_generic_ops. *)
(* Require Import Interval_transcend. *)
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
Module Test := Examples F.
Import Test.

(* battery of tests *)
Eval vm_compute in Test.compare I0 I0 I0 I0.

End Test.
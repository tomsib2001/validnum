Require Import Interval_tactic.
Require Import Interval_generic_ops.
Require Import Interval_transcend.
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Require Import integrals.

Module F := SpecificFloat BigIntRadix2.

Module FIntervalTactic := IntervalTactic F.
Import FIntervalTactic.


Module TestIntegral := IntegralTactic F.

Import TestIntegral.FInt.
Import TestIntegral.


Time Eval vm_compute in integral (prec10) (FInt.exp prec10) 10 F.zero (F.fromZ 1).

Time Eval vm_compute in integral (prec10) (FInt.exp prec10) 3 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 824 (-9)) (Float F.radix false 938 (-9)) *)
(* [1.609375,1.83203125]*)
(* Finished transaction in 0. secs (0.064004u,0.s) *)

Time Eval vm_compute in integral (prec10) (FInt.exp prec10) 6 F.zero (F.fromZ 1).
(*  Ibnd (Float F.radix false 870 (-9)) (Float F.radix false 890 (-9)) *)
(* [1.69921875,1.73828125]*)
(* Finished transaction in 1. secs (0.552034u,0.s) *)

Time Eval vm_compute in integral (prec10) (FInt.exp prec10) 10 F.zero (F.fromZ 1).
(* (Float F.radix false 875 (-9)) (Float F.radix false 885 (-9))*)
(* [1.708984375,1.728515625] *)
(* Finished transaction in 8. secs (8.400525u,0.004s)*)


(* Definition prec30 := (30%bigZ) : F.precision. *)

Time Eval vm_compute in integral (prec30) (FInt.exp prec30) 12 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 922382922 (-29)) *)
(*          (Float F.radix false 922608152 (-29)) *)
(*      : f_interval F.type *)
(* Finished transaction in 119. secs (118.387399u,0.008001s) *)

(* Time Eval vm_compute in integral (prec30) (FInt.exp prec30) 15 F.zero (F.fromZ 1). *)
(* Ibnd (Float F.radix false 922481451 (-29)) *)
(*          (Float F.radix false 922509615 (-29)) *)
(*      : f_interval F.type *)
(* [1.7182555999606848,1.7183080594986677] *)
(* Finished transaction in 1119. secs (1114.773669u,0.288018s) *)

Time Eval vm_compute in integral (prec30) (FInt.exp prec30) 3 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 866040413 (-29)) *)
(*          (Float F.radix false 981352359 (-29)) *)
(*      : f_interval F.type *)
(* [1.6131259743124247,1.8279112111777067] *)
(* Finished transaction in 0. secs (0.232014u,0.s) *)

Time Eval vm_compute in integral (prec30) (FInt.exp prec30) 6 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 915307301 (-29)) *)
(*          (Float F.radix false 929721300 (-29)) *)
(*      : f_interval F.type *)
(* [1.7048927042633295,1.7317408695816994] *)
(* Finished transaction in 2. secs (1.744109u,0.s) *)

Time Eval vm_compute in integral (prec30) (FInt.exp prec30) 10 F.zero (F.fromZ 1).
 (*  Ibnd (Float F.radix false 922045164 (-29))
         (Float F.radix false 922946047 (-29))
     : f_interval F.type *)
(* [1.7174429520964622,1.7191209774464369] *)
(*Finished transaction in 28. secs (28.685793u,0.060004s) *)

Require Import BigZ.

Definition prec64 := (100%bigZ) : F.precision.
Time Eval vm_compute in integral (prec64) (FInt.exp prec64) 3 F.zero (F.fromZ 1).
(*      = Ibnd (Float 1022440057055222484579125177733%bigZ (-99)%bigZ) *)
(*          (Float 1158576369005682997163092575753%bigZ (-99)%bigZ) *)
(*      : f_interval F.type *)
(* Finished transaction in 0. secs (0.036002u,0.s) *)

Time Eval vm_compute in integral (prec64) (FInt.exp prec64) 6 F.zero (F.fromZ 1).
(*     = Ibnd (Float 1080604133619477846151951543090%bigZ (-99)%bigZ) *)
(*          (Float 1097621172613285410224947467848%bigZ (-99)%bigZ) *)
(*      : f_interval F.type *)
(* Finished transaction in 0. secs (0.284018u,0.s) *)

Time Eval vm_compute in integral (prec64) (FInt.exp prec64) 9 F.zero (F.fromZ 1).
(*      = Ibnd (Float 1088027276879093749447539091601%bigZ (-99)%bigZ) *)
(*          (Float 1090154406753319694956663582203%bigZ (-99)%bigZ) *)
(*      : f_interval F.type *)
(* Finished transaction in 2. secs (2.168135u,0.004s) *)

Definition prec100 := (100%bigZ) : F.precision.

Time Eval vm_compute in integral (prec100) (FInt.exp prec100) 3 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 1022440057055222484579125177733 (-99)) *)
(*          (Float F.radix false 1158576369005682997163092575753 (-99)) *)
(*      : f_interval F.type *)

(* [1.6131259778856115,1.827911206442992]  *)
(* Finished transaction in 1. secs (1.584099u,0.s) *)


Time Eval vm_compute in integral (prec100) (FInt.exp prec100) 6 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 1080604133619477846151951543090 (-99)) *)
(*          (Float F.radix false 1097621172613285410224947467848 (-99)) *)
(*      : f_interval F.type *)
(* [1.7048927100652569,1.7317408636349296] *)
(* Finished transaction in 14. secs (13.356834u,0.016001s) *)

Time Eval vm_compute in integral (prec100) (FInt.exp prec100) 10 F.zero (F.fromZ 1).
(* Ibnd (Float F.radix false 1088558799688262396851727958906 (-99)) *)
(*          (Float F.radix false 1089622364625375369606290204212 (-99)) *)
(*      : f_interval F.type *)
(* [1.7174429602167616,1.719120969814866] *)
(* Finished transaction in 229. secs (228.658291u,0.012001s) *)

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

(* Variables (add : f_interval F.type -> f_interval F.type -> f_interval F.type). *)
(* Variables (mul : f_interval F.type -> f_interval F.type -> f_interval F.type). *)
(* Variables (div : f_interval F.type -> f_interval F.type -> f_interval F.type). *)

(* Fixpoint IP_thin_horner_n_aux n i res  :=  *)
(*   match n with *)
(*     | 0 => res *)
(*     | S m => IP_thin_horner_n_aux m i (add (mul res i) (div (thin one) (thin (F.fromZ (Z_of_nat' (fact m))))))   *)
(*   end.  *)

(* Definition IP_thin_horner_n n i := *)
(*   IP_thin_horner_n_aux n i (thin (F.fromZ 0%Z)). *)

(* Eval compute in (IP_thin_horner_n 1). *)
 (***)

Definition one := F.fromZ 1%Z.
Definition zero := F.fromZ 0%Z.

Definition P (x : R) := 1 + x + x*x / 2.

(* Print F. *)

Import Private.

Definition prec30 := (30%bigZ) : F.precision.
Definition prec := prec30.




Definition IP_thin i := (I.add prec (I.add prec (thin (F.fromZ 1%Z)) i) (I.div prec (I.mul prec i i) (thin (F.fromZ 2%Z)))).

Definition IP_thin_horner i := 
  I.add prec (thin one)
        (I.mul prec i 
               (I.add prec
                      (thin one)
                      (I.div prec i (thin (F.fromZ 2%Z)))
               )               
        ).
        

Definition IP_thin_horner_3 i := 
  I.add prec (thin one)
        (I.mul prec i 
               (I.add prec
                      (thin one)
                      (I.mul prec
                             i
                             (
                        I.add prec
                              (I.div prec (thin one) (thin (F.fromZ 2%Z)))
                              (I.div prec i (thin (F.fromZ 6%Z)))
                             ) 
                      )
                      
        )
        ).

Fixpoint IP_thin_horner_n_aux n i res  := 
  match n with
    | 0 => res
    | S m => IP_thin_horner_n_aux m i (I.add prec (I.mul prec res i) (I.div prec (thin one) (thin (F.fromZ (Z_of_nat' (fact m))))))  
  end. 

Definition IP_thin_horner_n n i :=
  IP_thin_horner_n_aux n i (thin (F.fromZ 0%Z)).

Variable i: I.type.


(* Eval vm_compute in IP_thin_horner_n 1 . *) (* needs something like "lazy"? *)

Eval vm_compute in IP_thin_horner_n 10 (thin (Float 1%bigZ (0)%bigZ)). 
(* Eval vm_compute in I.add prec (thin (Float 1%bigZ (-1)%bigZ)) (thin (Float 1%bigZ (-1)%bigZ)).  *)

Definition b := Float 1%bigZ (-2)%bigZ . 
Definition a := F.neg b.

Definition IP_horner_n i n := 
I.add prec (IP_thin_horner_n i n) (I.bnd a b).

Definition lb := Float 0%bigZ (-10)%bigZ.
Definition ub :=  Float 1%bigZ (0)%bigZ.

Definition order := 5%nat.

Definition reste := (I.bnd a b).

Lemma test3 : I.subset
                (I.add prec (IP_thin_horner_n order (I.bnd lb ub) ) reste)
                (I.add prec 
                       ((IP_thin_horner_n) (S order) (I.bnd lb ub) ) 
                       (I.mul prec reste (I.bnd lb ub))) .
  set s2 := (X in I.subset _ X).
  move: {-2}s2 (eq_refl s2) => s3 es23.
  set s1 := (X in I.subset X _).
  rewrite es23.
  vm_compute.
 Eval vm_compute in (s1, s2).
 Eval compute in (I.subset (I.bnd a b) (I.bnd a one)).
(* Eval vm_compute in s2. *)
 vm_compute.
 done.
Qed.

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
Definition tm_exp_lb_ub := (TMF.TM.TM_exp prec (thin zero) (I.bnd lb ub) 10).
Definition exp_poly := (TM.RPA.approx tm_exp_lb_ub) .
Definition reste_fin :=  (TM.RPA.error tm_exp_lb_ub) .
Eval vm_compute in reste_fin.
(* SearchAbout i_poly. *)
(* About i_eval. *)
(* About PolI.teval. *)

Eval vm_compute in (i_eval prec exp_poly (I.bnd lb ub)).
(* In Python: *)
(* >>> 729683215 * ( 2 ** -28) *)
(* 2.718281801789999 *)

(* Print TMF. *)
(* Print TM. *)
(* About TM.TM_integral. *)
Definition X0 := thin zero. 
Definition X := I.bnd lb ub. (* [0,1], bientot périmé *)
(* watch out: the followig is actually a primitive of exp which cancels at 0, 
that is exp(x) - 1 *)
Definition exp_integrated := TM.TM_integral prec X0 X (TM.TM_exp prec X0 X 10).
Definition exp_integrated_poly :=  TM.RPA.approx exp_integrated.
Definition exp_integrated_error := TM.RPA.error exp_integrated.
Eval vm_compute in i_eval prec exp_integrated_poly X.
Eval vm_compute in exp_integrated_error.
Eval vm_compute in exp_poly.
Eval vm_compute in exp_integrated_poly.

Eval vm_compute in I.add prec (i_eval prec exp_integrated_poly X) (I.mul prec (I.sub prec X X0) (TM.RPA.error (exp_integrated))).

(* let's try with a more complicated phi, for example with phi(t,x) = t sin(x), y(0) = 1 *)
Definition initial_guess := TM.RPA.RPA (I.bnd one one::Datatypes.nil) (I.bnd (F.neg one) one).

Definition comp_rpa := TM.TM_comp prec (TM.TM_sin prec) initial_guess X0 X order.
(* Eval vm_compute in TM.TI.T_var X0 6. *)
Definition phi_to_integrate := TM.TM_mul prec (TM.TM_var prec X0 X order) comp_rpa.
Definition initial_guess_integrated := TM.TM_integral prec X0 X (phi_to_integrate X0 X order).
Eval vm_compute in TM.RPA.approx initial_guess_integrated.

Lemma test4 : I.subset 
                (I.add prec (i_eval prec (TM.RPA.approx initial_guess) X) (TM.RPA.error initial_guess)) 
                (I.add prec (thin one) (I.add prec (i_eval prec (TM.RPA.approx initial_guess_integrated) X) (TM.RPA.error initial_guess_integrated))).
Proof.
set m1 := (X in I.subset X _).
set m2 := (X in I.subset _ X ).
Eval vm_compute in m1.
Eval vm_compute in m2.
vm_compute. (* it works! *)
done.
Qed.

Module TestIntegral := IntegralTactic F.

Import TestIntegral.FInt.
Import TestIntegral.

Lemma test5 : I.subset 
                ((IP_horner_n ) order (I.bnd lb ub) ) 
                (I.add prec 
                       (thin lb) 
                       (integral prec (IP_horner_n  order) 5 lb ub)).
(*   set s1 := (X in I.subset X _). *)
(*   set s2 := (X in I.subset _ X). *)
(* Eval vm_compute in s1. *)
(* Eval vm_compute in s2. *)
vm_compute.
Admitted.
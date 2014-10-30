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
(* Hypothesis HiFIntExt : I.extension g iF. *)
Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Section OrderOne.

Variables (a b : F.type).

About RInt.

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
    (* admit. *)
       rewrite xreal_ssr_compat.Xmul_Xreal; congr Xreal; field.
       by apply: Rminus_eq_contra; apply: Rlt_dichotomy_converse; right.
    apply: I.mul_correct; last first.
    - rewrite -[Xreal (rb - ra)]/(Xsub (Xreal rb) (Xreal ra)). (* 1 *)
      apply: I.sub_correct; exact: thin_correct_toR.
      (* try and show l * (b - a) <= int <= u * (b - a) instead *)
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

Lemma integral_correct_bis (depth : nat) (a b : F.type) (i : I.type) :
  ex_RInt f (T.toR a) (T.toR b) -> 
  match (F.cmp a b) with | Xlt => true | Xeq => true | _ => false end = true ->
  I.subset (integral depth a b) i = true -> 
  contains (I.convert i) (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
intros Hint Hcmp Hsub.
About subset_contains.
apply: (subset_contains (I.convert (integral depth a b))).
apply: I.subset_correct Hsub.
apply: integral_correct => //.
move : Hcmp.
rewrite F.cmp_correct.
rewrite Fcmp_correct.
rewrite /Xcmp /T.toR.
case: (FtoX (F.toF a)) => //.
intros r.
case: (FtoX (F.toF b)) => //.
intros r0.
case: (Rcompare_spec) => //= H _.
exact: Rlt_le.
exact: Req_le.
move : Hcmp (F.real_correct a).
rewrite F.cmp_correct.
rewrite Fcmp_correct.
case: ( (F.toF a)) => //.
move : Hcmp (F.real_correct b).
rewrite F.cmp_correct.
rewrite Fcmp_correct.
case: ( (F.toF a)) => //;
case: ( (F.toF b)) => //.
Qed.

End integral.

End IntervalIntegral.




(* this lemma is intended for the tactic, so that it allows for an easy proof of  *)
Lemma integral_correct_ter prec (depth : nat) (a b : F.type) (i : I.type) formula bounds :
  ex_RInt (fun x => nth 0 (eval_real formula (x::map IntA.real_from_bp bounds)) R0) (T.toR a) (T.toR b) -> 
  match (F.cmp a b) with | Xlt => true | Xeq => true | _ => false end = true ->
  I.subset (integral prec (fun xi => nth 0 (IntA.BndValuator.eval prec formula (xi::map IntA.interval_from_bp bounds)) I.nai) depth a b) i = true -> 
  contains (I.convert i) (Xreal (RInt (fun x => nth 0 (eval_real formula (x::map IntA.real_from_bp bounds)) R0) (T.toR a) (T.toR b))).
Proof.
apply: integral_correct_bis.
rewrite /toXreal_fun.
intros xi x Hcontains.
set toto := (I.convert
        (nth 0
           (IntA.BndValuator.eval prec formula
              (xi :: map IntA.interval_from_bp bounds)) I.nai)).
apply  (xreal_to_real (fun x => contains toto x) (fun x => contains toto (Xreal x))) => //.
case: toto => //.
Search IntA.xreal_from_bp. rewrite /toto.
Print IntA.real_from_bp.
Print IntA.xreal_from_bp.
pose bounds' := IntA.Bproof x xi Hcontains::bounds.
have -> : (map Xreal (x :: map IntA.real_from_bp bounds)) = map IntA.xreal_from_bp bounds'.
simpl. congr (_::_).
rewrite map_map.
apply: map_ext.
by case.
change (xi :: map IntA.interval_from_bp bounds) with (map IntA.interval_from_bp bounds').
by apply IntA.BndValuator.eval_correct.
Qed.

End IntegralTactic.


Require Import Interval_tactic.
Require Import Interval_generic_ops.
Require Import Interval_transcend.
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Print BigIntRadix2.

Module F := SpecificFloat BigIntRadix2.
(* Module F :=  GenericFloat Radix2. *)
(* Module FInt := FloatIntervalFull F. *)

(* Import FInt. *)

Module FIntervalTactic := IntervalTactic F.
Import FIntervalTactic.


Module TestIntegral := IntegralTactic F.

Import TestIntegral.FInt.
Import TestIntegral.

Ltac interval_inclusion_by_computation :=
  vm_compute; split; rewrite -/(Rle _ _); fourier.

Ltac proves_interval_extention := idtac. 

Ltac proves_RInt := idtac.

(* this one should be an application of an implication which reduces the problem
    to computation. *)
Ltac proves_bound_order := rewrite /T.toR /=; fourier.
 
Ltac apply_interval_correct :=
(* // kills the subgoals F.real b with b a bound of the integral. *)
(* these are obtained by Private.get_float in thebody of intergal_tac,
   hopefully it is always automatically discharged. *)
(* WARNING : do not use "apply:" instead of "apply" : it computes too much*)
  apply integral_correct => //;
  [proves_interval_extention | proves_RInt | proves_bound_order].
Definition reify_var : R.
exact: 0.
Qed.


Ltac get_bounds l :=
  let rec aux l :=
    match l with
    | Datatypes.nil => constr:(@Datatypes.nil IntA.bound_proof)
    | Datatypes.cons ?x ?l =>
      let i :=
        match goal with
        | _ =>
          let v := Private.get_float x in
          constr:(let f := v in IntA.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)))
        | _ => fail 100 "Atom" x "is neither a floating-point value nor bounded by floating-point values."
        end in
      let m := aux l in
      constr:(Datatypes.cons i m)
    end in
  aux l.


Ltac integral_tac_test g prec depth :=
match goal with
| |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c => 
  let v := Private.get_float a in
  let w := Private.get_float c in
  let lb := Private.get_float ra in
  let ub := Private.get_float rb in
  change (contains (I.convert (I.bnd v w)) (Xreal (RInt f ra rb)));
  apply: (subset_contains (I.convert (integral prec g depth lb ub))) end.

Ltac integral_tac prec depth :=
  match goal with
    | |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c => 
      let v := Private.get_float a in
      let w := Private.get_float c in
      let lb := Private.get_float ra in
      let ub := Private.get_float rb in
      let f' := (eval cbv beta in (f reify_var))
      in 
      match Private.extract_algorithm f' (reify_var::List.nil) with
        | (?formul,_::?const) => 
          let formula := fresh "formula" in
          pose (formula := formul);
            let bounds := fresh "bounds" in
            let toto1 := get_bounds const in 
            pose (bounds := toto1);
                          apply (integral_correct_ter prec depth lb ub (I.bnd v w) formula bounds) end
           
  end; [rewrite /=; idtac | abstract (vm_cast_no_check (eq_refl true)) | abstract (vm_cast_no_check (eq_refl true)) ].
 (* at this point we generate two subgoals: *)
 (*- the first one succeeds by computation if the interval computed by integral *)
 (*     is sharp enough wrt to the user's problem *)
 (*   - the second one is always provable by application of interval_correct *) 
 (* [interval_inclusion_by_computation | apply_interval_correct] *)
 (* | _ => fail 100 "rate" end. *)


Require Import BigZ.
Definition prec10 := (10%bigZ) : F.precision.


Lemma test_reification  : (0 <= RInt (fun x => x + 2) 0 1 <= 1000/8)%R.
Proof.
integral_tac prec10 (0%nat).

(* [idtac | abstract (vm_cast_no_check (eq_refl true)) | abstract (vm_cast_no_check (eq_refl true)) ]. *)
(* match goal with *)
(*     | |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c =>  *)
(*       let v := Private.get_float a in *)
(*       let w := Private.get_float c in *)
(*       let lb := Private.get_float ra in *)
(*       let ub := Private.get_float rb in *)
(* apply (integral_correct_ter prec10 0 lb ub (I.bnd v w) formula bounds) end  . *)

(* match goal with  *)
(* | |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c => *)
(*   let f' := (eval cbv beta in (f reify_var)) *)
(*   in match Private.extract_algorithm f' (reify_var::List.nil) with *)
(*        | (?formul,_::?const) =>  *)
(*          let formula := fresh "formula" in *)
(*          pose (formula := formul); *)
(*            let v := Private.get_float a in *)
(*            let w := Private.get_float c in *)
(*            let lb := Private.get_float ra in *)
(*            let ub := Private.get_float rb in *)
(*            (* change (contains (I.convert (I.bnd v w)) (Xreal (RInt (fun x => nth 0 (eval_real formula (x::consts)) R0) (T.toR lb) (T.toR ub)))); *) *)
(*            let bounds := fresh "bounds" in *)
(*            let toto1 := get_bounds const in  *)
(*            pose bounds := toto1; *)
(*                          apply (integral_correct_ter prec10 0 lb ub (I.bnd v w) formula bounds) *)
(*      end  *)
(* end. *)
simpl.
admit.
Qed.

About IntA.bound_proof.

(* have toto := (notNaiInt prec10 formula bounds F.zero (Float 1%bigZ 0%bigZ)). *)
(* have toto1 :  (forall n : nat, *)
(*           nth n *)
(*             (IntA.BndValuator.eval prec10 formula *)
(*                (I.bnd F.zero (Float 1%bigZ 0%bigZ) *)
(*                 :: map IntA.interval_from_bp bounds)) I.nai <> I.nai). *)
(* intros n. *)
(* simpl. *)
(* do 4 (case: n => [|n]//) => //. (* it's false.. x*) *)
(* About notNaiInt. *)
(* Admitted. *)

Locate exp.

Notation exp := Rtrigo_def.exp.
Notation cos := Rtrigo_def.cos.

Definition prec30 := (30%bigZ) : F.precision.

(* apply (integral_correct_ter prec10 0 (F.zero)  (Float 1%bigZ 0%bigZ) (I.bnd F.zero (Float 7%bigZ (-3)%bigZ)) formula bounds). *)

Lemma test  : 
(0<= RInt (fun x => (x + 1 )*(cos x)) 0 1<=2).
Proof.
integral_tac prec30 (11%nat).
admit.
Qed.


(* For tests and benchmarks *)
(* Print 3. *)

Require Import BigZ.
(* Definition prec10 := (10%bigZ) : F.precision. *)

(* Lemma test (f := fun x : R => x) : (0 <= RInt f 0 1 <= 7/8)%R. *)
(* Proof. *)
(* pose g (x : I.type) := x. *)
(* pose prec : F.precision := prec10. *)
(* pose depth : nat := 1%nat.  *)
(* rewrite /f. *)
(* integral_tac prec depth. *)
(* admit. *)
(* Qed. *)




(* Lemma test : (0 <= RInt (fun x : R => x + 1) 0 1 <= 23/8)%R. *)
(* Proof. *)
(* integral_tac prec10 (0%nat). *)
(* admit. *)
(* Qed. *)



Lemma testSinExp : (-200 <= RInt (fun x => Rtrigo_def.sin ((Rtrigo_def.exp x) + x)) 0 8 <= 200).
Proof.
integral_tac prec10 (5%nat).
Admitted.

(* let depth := constr:(15%nat) in *)
(*   match goal with *)
(*     | |- Rle ?a (RInt ?f ?ra ?rb) /\ Rle (RInt ?f ?ra ?rb) ?c =>  *)
(*       let v := Private.get_float a in *)
(*       let w := Private.get_float c in *)
(*       let lb := Private.get_float ra in *)
(*       let ub := Private.get_float rb in *)
(*       let f' := (eval cbv beta in (f reify_var)) in *)
(*       pose f'1 := f'; *)
(*       pose lb1 := lb; *)
(*       pose ub1 := ub; *)
(*       pose v1 := v; *)
(*       pose w1 :=w; *)
(*       pose depth1 := depth; *)
(*       match Private.extract_algorithm f' (reify_var::List.nil) with *)
(*         | (?formul,_::?const) =>  *)
(*           let formula := fresh "formula" in *)
(*           pose (formula := formul); *)
(*             let bounds := fresh "bounds" in *)
(*             let toto1 := get_bounds const in  *)
(*             pose (bounds := toto1) end *)
(* end. *)
(* Eval vm_compute in (integral prec30 (fun x => FInt.sin prec10 (FInt.add prec10 (FInt.exp prec10 x) x)) 10 lb1 ub1). *)

(* apply (integral_correct_ter prec10 depth1 lb1 ub1 (I.bnd v1 w1) formula bounds). *)
(* admit. *)
(* abstract (vm_cast_no_check (eq_refl true)). *)
(* vm_compute. *)
(* abstract (vm_cast_no_check (eq_refl true)). *)

(* [idtac | abstract (vm_cast_no_check (eq_refl true)) | abstract (vm_cast_no_check (eq_refl true)) ]. *)

(* integral_tac prec10 (10%nat). *)

(* Print exp_correct. *)
(* About exp_correct. *)
(* SearchAbout I.extension. *)



Lemma extension_comp f g h k : I.extension f g -> I.extension h k -> I.extension (fun x => f ( h x)) (fun x => g ( k x)).
Proof.
intros extfg extfhk.
intros i x Hcontains.
by apply: extfg; apply: extfhk.
Qed.

Lemma extension_comp_xreal f g h k : I.extension (toXreal_fun f) g -> I.extension (toXreal_fun h) k -> I.extension (toXreal_fun (fun x => f (h x))) (fun x => g ( k x)).
Proof.
intros extfg exthk.
intros i x.
have triv  : toXreal_fun f Xnan = Xnan by [].
have triv2 : toXreal_fun h Xnan = Xnan by [].
have triv3 (r: R) : toXreal_fun f (Xreal r) = Xreal (f r) by [].
have triv4 (r: R) : toXreal_fun h (Xreal r) = Xreal (h r) by [].
case: x => //.
 - have foo :=  extfg (k i) Xnan.
   rewrite triv in foo.
   intros ciXnan.
   apply: foo.
   have foo2 := exthk i Xnan.
   rewrite triv2 in foo2.
   by apply: foo2 => // .
 - intros r Hir.
   have foo := extfg (k i) (Xreal (h r)).
   rewrite triv3 in foo.
   apply: foo.
   have foo2 := exthk (i) (Xreal (r)).
   rewrite triv4 in foo2.
   by apply: foo2 => //.
Qed.


Definition f (x : R) := Rtrigo_def.exp (Rtrigo_def.cos x).
Definition g (x : I.type) := FInt.exp prec10 (FInt.cos prec10 x).

Ltac extension_tac t := match t with
 | (fun (x : I.type) => exp prec10 (cos prec10 x)) => idtac 
 (* | FInt.exp _ ?e => idtac (* apply: exp_correct *)(* ; extension_tac e  *) *)
end.


Lemma test_extension : I.extension (toXreal_fun f) g.
Proof.
rewrite /g.
(* extension_tac (fun (x : I.type) => exp prec10 (cos prec10 x)). *)
(* rewrite /f /g. *)
(* apply: (extension_comp_xreal Rtrigo_def.exp (FInt.exp prec10) Rtrigo_def.cos (FInt.cos prec10)). *)
(* - exact: FInt.exp_correct. *)
(* - exact: FInt.cos_correct. *)
admit.
Qed.



Lemma test2 (f := fun x : R => Rtrigo_def.exp x) : (0 <= RInt f 0 1 <= 23/8)%R.
Proof.
pose g (x : I.type) := FInt.exp prec10 x.
pose prec : F.precision := prec10.
pose depth : nat := 1%nat.
rewrite /f.
integral_tac prec depth.
admit.
Qed.

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

Print F.

Import Private.

(* Definition prec30 := (30%bigZ) : F.precision. *)
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
SearchAbout i_poly.
About i_eval.
About PolI.teval.

Eval vm_compute in (i_eval prec exp_poly (I.bnd lb ub)).
(* In Python: *)
(* >>> 729683215 * ( 2 ** -28) *)
(* 2.718281801789999 *)

(* Print TMF. *)
(* Print TM. *)
About TM.TM_integral.
Definition X0 := thin zero. 
Definition X := I.bnd lb ub. (* [0,1], bientot périmé *)
Definition exp_integrated := TM.TM_integral prec X0 X (TM.TM_exp prec X0 X 3).
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
                ((IP_horner_n ) order (I.bnd lb ub) ) 
                (I.add prec 
                       (thin lb) 
                       (integral prec (IP_horner_n  order) 5 lb ub)).
(*   set s1 := (X in I.subset X _). *)
(*   set s2 := (X in I.subset _ X). *)
(* Eval vm_compute in s1. *)
(* Eval vm_compute in s2. *)
vm_compute.
 
(* Lemma test4 (f := fun x : R => x * x * Rtrigo_def.exp ( - (x / 2)) * Rtrigo_def.log x) : (0 <= RInt f 0 1 <= 23/8)%R. *)

(* Definition foo f n a b :=  *)
(*   Eval vm_compute in (integral (prec10) f n a b). *)

(* Print foo. *)

(* Definition exp10 := Eval lazy in (Int.exp prec10). long... *)

(* Time Eval vm_compute in (foo (FInt.exp prec10) 10 F.zero (F.fromZ 1)). *)

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


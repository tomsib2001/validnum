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
rewrite /toto.
(* Print IntA.real_from_bp. *)
(* Print IntA.xreal_from_bp. *)
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
(* Print BigIntRadix2. *)

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


Ltac get_trivial_bounds l prec :=
  let rec aux l prec :=
    match l with
    | nil => constr:(@nil IntA.bound_proof)
    | cons ?x ?l =>
      let i :=
      match x with
      | PI => constr:(IntA.Bproof x (FInt.pi prec) (FInt.pi_correct prec))
      | Private.toR ?v =>
        constr:(let f := v in IntA.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)))
      end in
      match aux l prec with
      | ?m => constr:(cons i m)
      end
    end in
  aux l prec.

Ltac generate_machine l :=
  let rec aux l q :=
    match l with
    | nil => q
    | cons ?t ?l =>
      let m :=
        match t with
        | Eunary ?o ?a =>
          let u := list_find2 a l in
          constr:(Unary o u)
        | Ebinary ?o ?a ?b =>
          let u := list_find2 a l in
          let v := list_find2 b l in
          constr:(Binary o u v)
        end in
      aux l (cons m q)
    end in
  aux l (@nil term).

Ltac extract_algorithm t l :=
  match reify t l with
  | (?t, ?lc) =>
    let lm := generate_machine ltac:(get_non_constants t) in
    constr:(lm, lc)
  end.


Ltac get_bounds_aux x prec :=
  match goal with
  | H: Rle ?a x /\ Rle x ?b |- _ =>
    let v := get_float a in
    let w := get_float b in
    constr:(IntA.Bproof x (I.bnd v w) H)
  | H: Rle ?a x /\ Rle x ?b |- _ =>
    let va := extract_algorithm a (@nil R) in
    let vb := extract_algorithm b (@nil R) in
    match va with
    | (?pa, ?la) =>
      let lca := get_trivial_bounds la prec in
      match vb with
      | (?pb, ?lb) =>
        let lcb := get_trivial_bounds lb prec in
        constr:(let proga := pa in let boundsa := lca in let progb := pb in let boundsb := lcb in
          IntA.Bproof x _ (contains_bound_lr x prec proga boundsa 0 progb boundsb 0 H))
      end
    end
  | H: Rle ?a x |- _ =>
    let v := get_float a in
    constr:(IntA.Bproof x (I.bnd v F.nan) (conj H I))
  | H: Rle ?a x |- _ =>
    let v := extract_algorithm a (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      constr:(let prog := p in let bounds := lc in IntA.Bproof x _ (contains_bound_l x prec prog bounds 0 H))
    end
  | H: Rle x ?b |- _ =>
    let v := get_float b in
    constr:(IntA.Bproof x (I.bnd F.nan v) (conj I H))
  | H: Rle x ?b |- _ =>
    let v := extract_algorithm b (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      constr:(let prog := p in let bounds := lc in IntA.Bproof x _ (contains_bound_r x prec prog bounds 0 H))
    end
  | H: Rle (Rabs x) ?b |- _ =>
    let v := get_float b in
    constr:(IntA.Bproof x (I.bnd (F.neg v) v) (Rabs_contains_rev v x H))
  | H: Rle (Rabs x) ?b |- _ =>
    let v := extract_algorithm b (@nil R) in
    match v with
    | (?p, ?l) =>
      let lc := get_trivial_bounds l prec in
      constr:(let prog := p in let bounds := lc in IntA.Bproof x _ (contains_bound_ar x prec prog bounds 0 H))
    end
  end.


Ltac get_bounds l prec :=
  let rec aux l prec lw :=
    match l with
    | nil => constr:(@nil IntA.bound_proof, @nil R)
    | cons ?x ?l =>
      let i :=
      match x with
      | PI => constr:(IntIntA.Bproof x (FInt.pi prec) (FInt.pi_correct prec), @None R)
      | Private.toR ?v =>
        constr:(let f := v in IntIntA.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)), @None R)
      | _ =>
        match goal with
        (* | _ => *)
        (*   let v := Interval_tactic.Private.get_bounds_aux x prec in *)
        (*   constr:(v, @None R) *)
        | _ =>
          match goal with
          | H: Rle ?a x /\ Rle x ?b |- _ => idtac
          | H: Rle ?a x |- _ => idtac
          | H: Rle x ?b |- _ => idtac
          | H: Rle (Rabs x) ?b |- _ => idtac
          end ;
          fail 100 "Atom" x "is neither a floating-point value nor bounded by floating-point values."
        | _ =>
          constr:(IntIntA.Bproof x (I.bnd F.nan F.nan) (conj I I), @Some R x)
        end
      end in
      match aux l prec lw with
      | (?m, ?lw) =>
        match i with
        | (?i, @None R) => constr:(cons i m, lw)
        | (?i, @Some R ?aw) => constr:(cons i m, cons aw lw)
        end
      end
    end in
  aux l prec (@nil R).


(* Ltac get_bounds l := *)
(*   let rec aux l := *)
(*     match l with *)
(*     | Datatypes.nil => constr:(@Datatypes.nil IntA.bound_proof) *)
(*     | Datatypes.cons ?x ?l => *)
(*       let i := *)
(*         match goal with *)
(*         | _ => *)
(*           let v := Private.get_float x in *)
(*           constr:(let f := v in IntIntA.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x))) *)
(*         | _ =>  *)
(*           match goal with *)
(*             | H: Rle ?a x /\ Rle x ?b |- _ => idtac *)
(*             | H: Rle ?a x |- _ => idtac *)
(*             | H: Rle x ?b |- _ => idtac *)
(*             | H: Rle (Rabs x) ?b |- _ => idtac *)
(*           end ; fail 100 "Atom" x "is neither a floating-point value nor bounded by floating-point values." *)
(*         end in *)
(*       let m := aux l in *)
(*       constr:(Datatypes.cons i m) *)
(*     end in *)
(*   aux l. *)


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
    (* TODO: fix next line and then add similar ones *)
    (* | |- Rge _ _ => *)
    (*   apply Rle_ge; integral_tac prec depth *)
    | |- Rle ?a (RInt ?f ?ra ?rb) =>
      let v := Private.get_float a in
      let w := F.nan in
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

    | |- Rle (RInt ?f ?ra ?rb) ?c => 
      let v := F.nan in
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

Notation exp := Rtrigo_def.exp.
Notation cos := Rtrigo_def.cos.

Definition prec30 := (30%bigZ) : F.precision.

(* Goal forall x, 0 <= x <= 1 -> (x + 1) * cos x <= 2. *)
(* move => x Hx. *)
(* interval_intro x.  *)
(* interval. *)

Lemma test  :
(0<= RInt (fun x => (x )*(cos (x + 1))) 0 1<=2).
Proof.
integral_tac prec30 (11%nat).
admit.
Qed.

Ltac toto := (let w := Private.get_float 1%R in (fail "coucou" w)).

Goal True.
toto.

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



(* Lemma testSinExp : (-200 <= RInt (fun x => Rtrigo_def.sin ((Rtrigo_def.exp x) + x)) 0 8 <= 200). *)
(* Proof. *)
(* integral_tac prec10 (5%nat). *)
(* Admitted. *)

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


(* Lemma test_extension : I.extension (toXreal_fun f) g. *)
(* Proof. *)
(* rewrite /g. *)
(* (* extension_tac (fun (x : I.type) => exp prec10 (cos prec10 x)). *) *)
(* (* rewrite /f /g. *) *)
(* (* apply: (extension_comp_xreal Rtrigo_def.exp (FInt.exp prec10) Rtrigo_def.cos (FInt.cos prec10)). *) *)
(* (* - exact: FInt.exp_correct. *) *)
(* (* - exact: FInt.cos_correct. *) *)
(* admit. *)
(* Qed. *)



Lemma test_bothsides (f := fun x : R => Rtrigo_def.exp x) : (0 <= RInt f 0 1 <= 23/8)%R.
Proof.
pose g (x : I.type) := FInt.exp prec10 x.
pose prec : F.precision := prec10.
pose depth : nat := 1%nat.
rewrite /f.
integral_tac prec depth.
admit.
Qed.


Lemma test_left (f := fun x : R => Rtrigo_def.exp x) : (0 <= RInt f 0 1)%R.
Proof.
pose g (x : I.type) := FInt.exp prec10 x.
pose prec : F.precision := prec10.
pose depth : nat := 1%nat.
rewrite /f.
integral_tac prec depth.
admit.
Qed.


Lemma test_right (f := fun x : R => Rtrigo_def.exp x) : (RInt f 0 1 <= 23 / 8)%R.
Proof.
pose g (x : I.type) := FInt.exp prec10 x.
pose prec : F.precision := prec10.
pose depth : nat := 1%nat.
rewrite /f.
integral_tac prec depth.
admit.
Qed.

Lemma test_right_ge (f := fun x : R => Rtrigo_def.exp x) : (RInt f 0 1 >= 0)%R.
Proof.
pose g (x : I.type) := FInt.exp prec10 x.
pose prec : F.precision := prec10.
pose depth : nat := 1%nat.
rewrite /f.
integral_tac prec depth.
admit.
Qed.


 
(* Lemma test4 (f := fun x : R => x * x * Rtrigo_def.exp ( - (x / 2)) * Rtrigo_def.log x) : (0 <= RInt f 0 1 <= 23/8)%R. *)

(* Definition foo f n a b :=  *)
(*   Eval vm_compute in (integral (prec10) f n a b). *)

(* Print foo. *)

(* Definition exp10 := Eval lazy in (Int.exp prec10). long... *)

(* Time Eval vm_compute in (foo (FInt.exp prec10) 10 F.zero (F.fromZ 1)). *)




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


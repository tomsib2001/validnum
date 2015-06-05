Require Import List.
(* Require Import Reals. *)
(* Require Import Fourier. *)
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

Require Import ssreflect ssrfun ssrbool seq.
Require Import integrals.


Module Examples (F : FloatOps with Definition even_radix := true).
Module IT := IntegralTactic F.
Module Extras := ExtraFloatInterval F.

Import Extras.

Notation float := F.type.
Notation intervalle := FInt.I.type.

Definition I0 := Ibnd F.zero F.zero.

(* Boolean compaisons on float floats: return false
   when the comparison is either false or not defined (Nans) *)
Definition Flt (x y : float) :=
  match F.cmp x y with
    | Xlt => true
    | _ => false
  end.

Definition Feq (x y : float) :=
  match F.cmp x y with
    | Xeq => true
    | _ => false
  end.

Definition Fle (x y : float) :=
  (Flt x y) || (Feq x y).

Definition Fgt (x y : float) := Flt y x.

Definition Fge (x y : float) := Fle y x.

(*Fmax a b is equal to
- b when a <= b
- a when b < a
- Fnan if the comparison is undefined. *)
Definition Fmax a b :=
  match F.cmp a b with
    | Xlt => b
    | Xeq => b
    | Xgt => a
    | Xund => F.nan
  end.

Definition FtoXR (f : float) : ExtendedR := FtoX (F.toF f).

Notation iFtoiXR := FInt.I.convert.
(* Tests whether i is an empty interval or not,
   according to the semantics prescribed by the
   "contains" predicate *)
Definition not_empty (i : intervalle) : bool :=
  match i with
    | Inan => true
    | Ibnd a b =>
      if (F.real a) && (F.real b) then Fle a b
       else true
  end.

Definition is_empty (i : intervalle) : bool :=
  ~~ (not_empty i).


Definition is_nan (f : float) := ~~ F.real f.

(* Boolean version of contains *)
Definition containsB (i : intervalle) (f : float) :=
  F.real f &&
  (match i with
      | Inan => true
      | Ibnd a b =>
         if F.real a then (Fle a f && ((is_nan b) || Fle f b))
         else (Fle f b || is_nan b)
   end).

Lemma containsBP i f : containsB i f -> contains (iFtoiXR i) (FtoXR f).
Proof.
rewrite /containsB; case Rf : (F.real f) => //=.
case: i => [| a b] //.
case Ra : (F.real a) => //=.
Admitted.

(* Boolean test for the intervals; *)

(*  iLt i1 i2 := forall x \in i1, forall y \in i2, x < y,
   where \in corresponds to the semantics of contains
    *)
Definition iLt (i1 i2 : intervalle) :=
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Flt r1 l2) (* && (Flt l1 r2) *)
       else false
  else false.

Lemma iLTP i1 i2 x1 x2 : iLt i1 i2 -> containsB i1 x1 -> containsB i2 x2 -> Flt x1 x2.
Admitted.

(*  iGt i1 i2 := forall x \in i1, forall y \in i2, y < x,
   where \in corresponds to the semantics of contains
    *)
Definition iGt (i1 i2 : intervalle) :=
  iLt i2 i1.

(*  iLe i1 i2 := forall x \in i1, forall y \in i2, x <= y,
   where \in corresponds to the semantics of contains
    *)
Definition iLeq (i1 i2 : intervalle) :=
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Fle r1 l2) (* && (Fle l1 r2) *)
       else false
  else false.

Definition iGeq (i1 i2 : intervalle) :=
  iLeq i2 i1.

(* iMax [a, b] [c d] is [max a b, max c d] and iMax Inan i = iMax i Inan = Inan *)
Definition iMax x y :=
  match x,y with
    | Inan, _ => Inan
    | _, Inan => Inan
    | Ibnd a b, Ibnd c d => Ibnd (Fmax a c) (Fmax b d)
end.

(* For any x, y, a, b in X Y A B respectively, if x <= y then a \in compare X Y A B
   and if x >= y then b \in compare X Y A B *)
Definition compare (x y a b : intervalle) :=
  if iLt x y then a else
    if iGt x y then b else
      FInt.I.join a b.


Section Doubbub.

Local Open Scope Z_scope.

Delimit Scope intervalle_scope with i.

Notation "[| a , b |]"  := (Ibnd (F.fromZ a) (F.fromZ b)) : intervalle_scope.

Notation "[| a |]"  := (thin a) : intervalle_scope.


Open Scope intervalle_scope.

Variable prec : F.precision.
Variable rd : rounding_mode.

Local Coercion F.fromZ : Z >-> F.type.

Definition Fone : float := 1.

(* We keep the names used in the OCaml code, at least for now. *)
Definition iPlus := FInt.add prec.
Definition iSub := FInt.sub prec.
Definition iMult := FInt.mul prec.
Definition iDiv := FInt.div prec.
Definition iSqrt := FInt.sqrt prec.
Definition iSqr := fun i => FInt.power_int prec i 2.
Definition iPow x n := FInt.power_int prec x n.
Definition iNeg := FInt.neg.
(* Definition iNeq x y := (iLt x y) || (iLt y x). *)
Definition iNeq x y := is_empty (FInt.meet x y).

Definition Fdiv := F.div rd prec.
Definition Fmul := F.mul rd prec.
Definition Fsub := F.sub rd prec.
Definition Fadd := F.add rd prec.

(* constants *)
Definition i1000 := [| 1000 |].
Definition i996 := [| 996 |].
Definition ifive := [| 5 |].
Definition ione := [| 1 |].
Definition itwo := [| 2 |].
Definition ithree := [| 3 |].

Definition Fhalf := Fdiv 1 2.
Definition Fone_sixteenth := Fdiv ( 1) ( 16).
Definition Fthirtythree_sixteenth := Fdiv ( 33) ( 16).
Definition ihalf := [| Fhalf |].
Definition i998 := [| 998 |].
Definition i0_1 := [|0, 1|].
Definition i0_10 := [|0, 10|].
Definition Ftwoandahalf := (Fdiv ( 5) ( 2)).
Definition itwoandahalf := [| Ftwoandahalf|].



(* end constants *)

(* pasted comment from C++ code: *)
(* returns a point between x and y.  Rounding is not material here. *)
Definition avgwt (x y : intervalle) (w : float) : float :=
  match x, y with
    | Inan, _ => F.nan
    | _, Inan => F.nan
    | Ibnd x1 x2, Ibnd y1 y2 =>
      if ~~ (iLt x y) then F.nan else
      Fadd (Fmul (Fsub Fone w) x2) (Fmul w y1)
  end.


(* sanity checks *)

Definition s1 := (FInt.I.join (iNeg ione) ione).
 (* should be [-1,1] *)
Definition s2 := (FInt.I.meet (iNeg ione) ione). (* should be empty *)
Definition small_interval := Ibnd F.zero (Fdiv ( 1) ( 32)).
Definition s3 := (iGeq (iMult i1000 ione) i996).
Definition s4 := (iLeq (iMult ifive small_interval) (ione)).
Definition s5 := avgwt [|1, 2|] [|3, 10|] Fone_sixteenth.
Definition s6 := compare [|1, 2|] [|3, 10|] [|0, 1|] [|0, 10|].
Definition s7 := compare [|3, 10|] [|1, 2|] [|0, 1|] [|0, 10|].
Definition s8 := IT.integral_intBounds prec (fun x => x) 5 [|1, 2|] [|3, 10|] rd.


(* end sanity checks *)



(* functions which are integrated: like in the paper, but with the appropriate arguments.
    The last one is the (future) integration variable. *)

Definition dx H F Y :=
iDiv (iSub (iMult (H) (iPow (Y) (2))) (F)) (( iSqrt (iMult (iPlus (iMult (itwo) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F))) (iSub (iMult (itwo) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F)))))).

Definition dxmin H F Y_min Z:=
iDiv (iMult (itwo) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (itwo) (iPlus (Y_min) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (iSub (iSub (itwo) (iMult (H) (Y_min))) (iMult (iPlus (Y_min) (iPow (Z) (2))) (H)))))).

Definition dxmax H F Y_max Z :=
iDiv (iMult (itwo) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (itwo) (iSub (Y_max) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (iMult (H) (iPlus (iSub (Y_max) (iPow (Z) (2))) (iDiv (F) (iPlus (ione) (( iSqrt (iPlus (ione) (iMult (F) (H)))))))))))).

Definition dv H F Y:=
iMult (iPow (Y) (2)) (iDiv (iSub (iMult (H) (iPow (Y) (2))) (F)) (( iSqrt (iMult (iPlus (iMult (itwo) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F))) (iSub (iMult (itwo) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F))))))).

Definition dvmin H F Y_min Z :=
iMult (iPow (iPlus (Y_min) (iPow (Z) (2))) (2)) (iDiv (iMult (itwo) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (itwo) (iPlus (Y_min) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (iSub (iSub (itwo) (iMult (H) (Y_min))) (iMult (iPlus (Y_min) (iPow (Z) (2))) (H))))))).

Definition dvmax H F Y_max Z :=
iMult (iPow (iSub (Y_max) (iPow (Z) (2))) (2)) (iDiv (iMult (itwo) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (itwo) (iSub (Y_max) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (iMult (H) (iPlus (iSub (Y_max) (iPow (Z) (2))) (iDiv (F) (iPlus (ione) (( iSqrt (iPlus (ione) (iMult (F) (H))))))))))))).

(* end functions which are integrated *)

Definition diam (x : intervalle) : float :=
  match x with
    | Inan => F.nan
    | Ibnd a b => Fsub b a
  end.

(* The return type for the step functions: Reject n means that the argument has
   been rejected at step n and NoResult n means that step n could not conclude;
   and therefore bisecting futher is required in order to conclude. *)
Inductive result :=
| Reject : nat -> result
| NoResult : forall A : Type, A -> nat -> result.

Arguments NoResult {A} _ _ .
(* This is the last step of the paper: the computation ends with either a (Reject 9) or
   a (NoResult 9) *)

Definition step9 z1 z2 z3 z4 hi fi ymin ymax w_ends y1 y4 f0 h0 idepth :=
  let w_base := IT.integral_intBounds prec (dvmin hi fi ymin) idepth z1 z3 rd in
  let w_i := iPlus w_ends w_base in
  let i1 := IT.integral_intBounds prec (dv h0 f0) idepth y1 y4 rd in
  let i2 := IT.integral_intBounds prec (dvmax h0 f0 ymax) idepth z4 z2 rd in
  let w_0 :=
    iPlus
      (i1)
      (iSub
	 (i2)
	 w_base
      ) in
  if iNeq w_i w_0 then Reject 9 else NoResult tt 9.


Definition step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth :=
  let t := iSqrt(iSub y1 ymin) in
  let z1 := compare c1 (iDiv (iSqrt(ithree)) (itwo)) (iNeg t) t in
  let z3 := iSqrt(iSub y2 ymin) in
  let delta_i := IT.integral_intBounds prec (dxmin hi fi ymin) idepth z1 z3 rd in
  let delta_0 := IT.integral_intBounds prec (dxmax h0 f0 ymax) idepth z4 z2 rd in
  if iLt delta_i delta_0 then Reject 8 else
  let delta_0 :=
    iPlus
      delta_0
      (IT.integral_intBounds prec (dx h0 f0) idepth y1 y4 rd) in
  if iNeq delta_i delta_0 then Reject 8
  else step9 z1 z2 z3 z4 hi fi ymin ymax w_ends y1 y4 f0 h0 idepth.


Definition step7 c1 h0 f0 y2 ymin ymax y1 fi hi w_ends idepth :=
  let yleft_init := iSqrt (iDiv f0 h0) in
  (* this was reformulated from Ocaml because of no side-effects, double check the semantics in case there is a problem *)
  if ~~((iLt ymin y2) && (iLt yleft_init ymax)) then
    NoResult [:: ymin; y2; yleft_init; ymax] 7
  else
    let yleft :=  iMax y1 yleft_init in
    let y4 := thin (avgwt yleft ymax Fone_sixteenth) in
    let z2 := iSqrt(iSub ymax y2) in
    let z4 := iNeg (iSqrt(iSub ymax y4)) in
    if iGeq (iMult i1000 c1) (i998) then
      (
        let t := (avgwt y1 y2 Fhalf) in
        let delta_i :=
	    iPlus
	      (iMult
	         (iSub (thin t) y1)
	         (thin Fthirtythree_sixteenth))
	      (IT.integral_intBounds prec (dx hi fi) idepth (thin t) y2 rd) in
        let delta_0 := iMult (iNeg (iSub yleft y1)) (iSqrt ithree) in
        let t := avgwt yleft y4 Fone_sixteenth in
        let delta_0 :=
	    iPlus
	      delta_0
	      (IT.integral_intBounds prec (dx h0 f0) idepth (thin t) y4 rd) in
        if iGt delta_0 delta_i then Reject 7 else
          let delta_0 :=
	      iPlus
	        delta_0
	        (IT.integral_intBounds prec (dxmax h0 f0 ymax) idepth z4 z2 rd)
          in
          if iGt delta_0 delta_i then Reject 7 else
            if containsB c1 Fone then NoResult tt 7 else step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth
      ) else step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth.


Definition step6 c1 h0 f0 c2 hi fi y1 y2 idepth :=
  let w_ends :=
    iPlus
      (iMult
	 (iPow (iSub ione c1) 2)
	 (iDiv
	    (iPlus itwo c1)
	    (ithree)
	 )
      )
      (iMult
	 (iPow (iSub ione c2) 2)
	 (iDiv
	    (iPlus itwo c2)
	    (ithree)
	 )
      ) in
  let ymin := iDiv (iNeg fi) (iPlus ione (iSqrt (iPlus ione (iMult fi hi)))) in
  let ymax := iDiv (iPlus ione (iSqrt (iPlus ione (iMult f0 h0)))) (h0) in
  let y := compare c1 (iDiv (iSqrt ithree) itwo) ymin y1 in
  if iLt (iMult y hi) (iNeg ione) then
    (
    (let r := iDiv (iDiv (iSqrt (ithree)) (itwo)) (iSub (iNeg hi) (iDiv ione y)) in
     let w := iMult
                (itwoandahalf)
                (iMult
	           (iPlus y (iMult r (iDiv (iSqrt (ithree)) (itwo))))
	           (iSqr r)
                ) in
     if iLt w w_ends then Reject 6 else step7 c1 h0 f0 y2 ymin ymax y1  fi hi w_ends idepth)) else step7 c1 h0 f0 y2 ymin ymax y1  fi hi w_ends idepth.


Definition step5 c1 h0 f0 c2 hi fi y1 y2 idepth :=
if (Fgt (diam c2) Fhalf) then NoResult tt 5 else step6 c1 h0 f0 c2 hi fi y1 y2 idepth.


Definition step4 c1 h0 f0 c2 hi fi y1 y2 idepth :=
if iLeq c1 ihalf && iLeq h0
    (iSub
       ione
       (iMult (iSqrt ithree) (iDiv c1 y1))
    ) then Reject 4 else step5 c1 h0 f0 c2 hi fi y1 y2 idepth.

Definition step3 t fi hi c1 c2 h0 f0 y1 idepth:=
  let y2 := iSqrt(FInt.meet t [|0, 1|]) in
  let c2 := FInt.meet c2
    (iDiv
       (iSub (iMult (iSub hi ione) (y2)) (iDiv fi y2))
       (iSqrt ithree)) in
  if is_empty c2 then Reject 3 else step4 c1 h0 f0 c2 hi fi y1 y2 idepth.

Definition step2 c1 h0 idepth :=
  let hi := iSub itwo h0 in
  let y1 := iSqrt (iSub ione (iSqr c1)) in
  let sub_hi_one := (iSub hi ione) in (* H-i - 1, reused many times *)
  let fi := iSub
    (iMult sub_hi_one (iPow y1 2))
    (iMult c1 (iMult y1 (iSqrt ithree))) in
  let f0 := iNeg fi in
  let c2 := FInt.meet
    (FInt.I.join (iNeg c1) c1)
    (FInt.I.join (iNeg ihalf) ihalf) in
  let t :=
    iSub
      (iDiv
	 (
	   iPlus (iMult (itwo) (iMult sub_hi_one (fi))) ithree
	 )
	 (
	   iPlus ithree (iSqr sub_hi_one)
	 )
      )
      (iSub ione (iSqr c1))
  in
  if iNeq (iPlus (iPow c2 2) t) ione then
    Reject 2
  else step3 t fi hi c1 c2 h0 f0 y1 idepth.


Definition step1 (c1 h0 : intervalle) (idepth : nat) :=
if (iGeq (iMult i1000 c1) i996) && (iLeq (iMult ifive h0) (ione)) then Reject 1
else step2 c1 h0 idepth.

Definition split x :=
  match x with
    | Inan => (Inan,Inan)
    | Ibnd a b => let m := FInt.I.midpoint x in
                 (Ibnd a m,Ibnd m b)
end.

Open Scope nat_scope.

Definition update nineuple i :=
  match nineuple,i with
| (k,x1,x2,x3,x4,x5,x6,x7,x8),1 => (S k,x1,x2,x3,x4,x5,x6,x7,x8)
| (x1,k,x2,x3,x4,x5,x6,x7,x8),2 => (x1,S k,x2,x3,x4,x5,x6,x7,x8)
| (x1,x2,k,x3,x4,x5,x6,x7,x8),3 => (x1,x2,S k,x3,x4,x5,x6,x7,x8)
| (x1,x2,x3,k,x4,x5,x6,x7,x8),4 => (x1,x2,x3,S k,x4,x5,x6,x7,x8)
| (x1,x2,x3,x4,k,x5,x6,x7,x8),5 => (x1,x2,x3,x4,S k,x5,x6,x7,x8)
| (x1,x2,x3,x4,x5,k,x6,x7,x8),6 => (x1,x2,x3,x4,x5,S k,x6,x7,x8)
| (x1,x2,x3,x4,x5,x6,k,x7,x8),7 => (x1,x2,x3,x4,x5,x6,S k,x7,x8)
| (x1,x2,x3,x4,x5,x6,x7,k,x8),8 => (x1,x2,x3,x4,x5,x6,x7,S k,x8)
| (x1,x2,x3,x4,x5,x6,x7,x8,k),9 => (x1,x2,x3,x4,x5,x6,x7,x8,S k)
| n,i => (0,0,0,0,0,0,0,0,0)%nat (* just to ensure we never encounter this *)
end.



Fixpoint divideAndCheckRectangle y1 h0 idepth fuel nRej nNoRes lrects {struct fuel} :=
  match fuel with
  | O => (false,nRej,nNoRes,lrects)
  | S k =>
    let c1 := iSqrt (iSub ione (iSqr y1)) in
    (match step1 c1 h0 idepth with
    | Reject i => (true, update nRej i, nNoRes, (y1, h0, S k)::lrects)
    | NoResult _ _ i =>
      let '(y1a,y1b) := split y1 in
      let '(h0a,h0b) := split h0 in
      let nNoRes := update nNoRes i in
      let '(b1,n1,nnr1,l1) := (divideAndCheckRectangle y1a h0a idepth k nRej nNoRes lrects) in
      if b1 then
        let '(b2,n2,nnr2,l2) := (divideAndCheckRectangle y1a h0b idepth k n1 nnr1 l1) in
        if b2 then
          let '(b3,n3,nnr3,l3) := (divideAndCheckRectangle y1b h0a idepth k n2 nnr2 l2) in
          if b3 then
            let '(b4,n4,nnr4,l4) := (divideAndCheckRectangle y1b h0b idepth k n3 nnr3 l3) in
            (b4,n4,nnr4,l4)
          else
            (b3,n3,nnr3,l3)
        else
          (b2,n2,nnr2,l2)
      else
        (b1,n1,nnr1,l1)
     end) end.


Fixpoint divideAndCheckRectangle_debug y1 h0 idepth fuel nRej nNoRes (ldebug : seq (seq intervalle))
         {struct fuel} :=
  match fuel with
  | O => (false,nRej,nNoRes,ldebug)
  | S k =>
    let c1 := iSqrt (iSub ione (iSqr y1)) in
    (match step1 c1 h0 idepth with
    | Reject i => (true, update nRej i, nNoRes, ldebug)
    | NoResult _ d i =>
      (true, nRej, nNoRes, d :: ldebug)
    | NoResult _ _ i => (true, nRej, nNoRes, ldebug)
     (*  let '(y1a,y1b) := split y1 in *)
     (*  let '(h0a,h0b) := split h0 in *)
     (*  let nNoRes := update nNoRes i in *)
     (*  let '(b1,n1,nnr1,l1) := (divideAndCheckRectangle y1a h0a idepth k nRej nNoRes ldebug) in *)
     (*  if b1 then *)
     (*    let '(b2,n2,nnr2,l2) := (divideAndCheckRectangle y1a h0b idepth k n1 nnr1 l1) in *)
     (*    if b2 then *)
     (*      let '(b3,n3,nnr3,l3) := (divideAndCheckRectangle y1b h0a idepth k n2 nnr2 l2) in *)
     (*      if b3 then *)
     (*        let '(b4,n4,nnr4,l4) := (divideAndCheckRectangle y1b h0b idepth k n3 nnr3 l3) in *)
     (*        (b4,n4,nnr4,l4) *)
     (*      else *)
     (*        (b3,n3,nnr3,l3) *)
     (*    else *)
     (*      (b2,n2,nnr2,l2) *)
     (*  else *)
     (*    (b1,n1,nnr1,l1) *)
      end) end.



Definition main idepth depth :=
  let y1 := [|0, 1|] in
  let h0 := [|0, 10|] in
    divideAndCheckRectangle y1 h0 idepth depth (0,0,0,0,0,0,0,0,0) (0,0,0,0,0,0,0,0,0) List.nil.

     (* if iLt w w_ends then reject c1 h0 6); *)
End Doubbub.
End Examples.

Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
Require Import BigZ.
Module Test := Examples F.

Definition prec60 := (60%bigZ) : F.precision.
Definition rd := rnd_DN.

Open Scope nat_scope.

About Test.step2_debug.

(* (hi, y1, fi, f0, c2, t, iPlus (iPow c2 2) t) and the results is Reject 2 if the
   last interval does not contain 1 *)

Eval vm_compute in Test.main prec60 rd 5 2.

(* battery of tests *)

Eval vm_compute in Test.s1.
Eval vm_compute in Test.s2.
Eval vm_compute in (Test.s3 prec60).
Eval vm_compute in (Test.s4 prec60 rd).
Eval vm_compute in (Test.s5 prec60 rd). (* avgwt seems to behave like in Ocaml *)
Eval vm_compute in (Test.s6).
Eval vm_compute in (Test.s7). (* compare seems to behave like in Ocaml *)
Eval vm_compute in (Test.s8 prec60 rd).
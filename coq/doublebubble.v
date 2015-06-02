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
Require Import integrals.

Module Examples (F : FloatOps with Definition even_radix := true).
Module IT := IntegralTactic F.
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

Definition Fle (x y : F.type) :=
  match F.cmp x y with
    | Xlt => true
    | Xeq => true
    | _ => false
  end.

Definition Fgt (x y : F.type) := Flt y x.
Definition Fge (x y : F.type) := Fle y x.
Definition Fmax a b := 
   if Fle a b then b else a.

(* etc. *)

About FInt.Flt.
Print FInt.I.type.
Print f_interval.
SearchAbout (f_interval _ -> f_interval _ -> bool).
Print FInt.I.subset.

Notation intervalle := FInt.I.type.
Notation float := F.type.

Definition iLt (i1 i2 : intervalle) := 
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Flt r1 l2) && (Flt l1 r2)
       else false
  else false.

Definition iGt (i1 i2 : intervalle) :=
  iLt i2 i1.


Definition iLeq (i1 i2 : intervalle) := 
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Fle r1 l2) && (Fle l1 r2)
       else false
  else false.

Definition iGeq (i1 i2 : intervalle) :=
  iLeq i2 i1.

Definition iMax x y := 
  match x,y with
    | Inan, _ => Inan
    | _, Inan => Inan
    | Ibnd a b, Ibnd c d => Ibnd (Fmax a c) (Fmax b d)
end.

 
Print pair.
Definition foo (n m : nat) :=
  match (n, m) with
  | pair (S O) l => l
  | _ => O
end.



Search "join".

Definition compare (x y a b : intervalle) := 
  if iLt x y then a else 
    if iGt x y then b else
      FInt.I.join a b.

Search "nan" in F.
SearchAbout F.type.

Parameter prec : F.precision.
Parameter rd : rounding_mode.
Print F.
Definition Fone := F.fromZ 1.

Definition iPlus := (FInt.add prec).
Definition iSub := (FInt.sub prec).
Definition iMult := (FInt.mul prec).
Definition iDiv := FInt.div prec.
Definition iSqrt := FInt.sqrt prec.
Definition iSqr := fun i => FInt.power_int prec i 2. 
Definition iPow x n := FInt.power_int prec x n.
Definition iNeg := FInt.neg.
Definition iNeq x y := (iLt x y) || (iLt y x).

(* constants *)
Definition i1000 := thin (F.fromZ  1000).
Definition i996 := thin (F.fromZ  996).
Definition five := thin (F.fromZ  5).
Definition one := thin (F.fromZ  1).
Definition two := thin (F.fromZ  2).
Definition three := thin (F.fromZ  3).
Definition float_half := (F.div rd prec (F.fromZ 1) (F.fromZ 2)) .
Definition one_sixteenth := (F.div rd prec (F.fromZ 1) (F.fromZ 16)).
Definition thirtythree_sixteenth := (F.div rd prec (F.fromZ 33) (F.fromZ 16)).
Definition half := thin float_half . (* there's got to be a better way http://imgur.com/gallery/ZG3r5 *)
Definition i998 := thin (F.fromZ  998).
Definition int01 := Ibnd F.zero Fone.
Definition int010 := Ibnd F.zero (F.fromZ 10).
Definition twoandahalf_float := (F.div rd prec (F.fromZ 5) (F.fromZ 2)).
Definition twoandahalf_int := thin twoandahalf_float.
Definition two_int := thin (F.fromZ 2).
Definition one_int := thin (Fone).

(* end constants *)

(* functions which are integrated *)

Definition dx H F Y := 
iDiv (iSub (iMult (H) (iPow (Y) (2))) (F)) (( iSqrt (iMult (iPlus (iMult (two_int) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F))) (iSub (iMult (two_int) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F)))))).

Definition dxmin H F Y_min Z:= 
iDiv (iMult (two_int) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (two_int) (iPlus (Y_min) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (iSub (iSub (two_int) (iMult (H) (Y_min))) (iMult (iPlus (Y_min) (iPow (Z) (2))) (H)))))).

Definition dxmax H F Y_max Z :=  
iDiv (iMult (two_int) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (two_int) (iSub (Y_max) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (iMult (H) (iPlus (iSub (Y_max) (iPow (Z) (2))) (iDiv (F) (iPlus (one_int) (( iSqrt (iPlus (one_int) (iMult (F) (H)))))))))))).

Definition dv H F Y:= 
iMult (iPow (Y) (2)) (iDiv (iSub (iMult (H) (iPow (Y) (2))) (F)) (( iSqrt (iMult (iPlus (iMult (two_int) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F))) (iSub (iMult (two_int) (Y)) (iSub (iMult (H) (iPow (Y) (2))) (F))))))).

Definition dvmin H F Y_min Z := 
iMult (iPow (iPlus (Y_min) (iPow (Z) (2))) (2)) (iDiv (iMult (two_int) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (two_int) (iPlus (Y_min) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iPlus (Y_min) (iPow (Z) (2))) (2))) (F))) (iSub (iSub (two_int) (iMult (H) (Y_min))) (iMult (iPlus (Y_min) (iPow (Z) (2))) (H))))))).

Definition dvmax H F Y_max Z := 
iMult (iPow (iSub (Y_max) (iPow (Z) (2))) (2)) (iDiv (iMult (two_int) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (( iSqrt (iMult (iPlus (iMult (two_int) (iSub (Y_max) (iPow (Z) (2)))) (iSub (iMult (H) (iPow (iSub (Y_max) (iPow (Z) (2))) (2))) (F))) (iMult (H) (iPlus (iSub (Y_max) (iPow (Z) (2))) (iDiv (F) (iPlus (one_int) (( iSqrt (iPlus (one_int) (iMult (F) (H))))))))))))).

(* end functions which are integrated *)


Definition is_empty x : bool := 
  match x with
    | Inan => false
    | Ibnd a b => Fle a b
  end.


(* pasted comment from C++ code: *)
(* returns a point between x and y.  Rounding is not material here. *)
Definition avgwt (x y : intervalle) (w : F.type) : F.type :=
  match x,y with
    | Inan,_ => F.nan
    | _,Inan => F.nan
    | Ibnd x1 x2,Ibnd y1 y2 => 
      F.add rd prec (F.mul rd prec (F.sub rd prec Fone w) x2) (F.mul rd prec w y1)
  end.



Print FInt.

Definition diam (x : intervalle) : float :=
  match x with
    | Inan => F.nan
    | Ibnd a b => F.sub rd prec b a
  end.

Search "max" in FInt.

Definition containsB x f :=
  match x with
    | Inan => true
    | Ibnd a b => Fle a f && Fle f b
end.


  (* assert (iLeq c1 (iDiv (iSqrt(three)) (two))  *)
  (*         || *)
  (*           iLeq y1 y2); *)  (* verify at step 8 in pseudocode page 43*)


Inductive result :=
| Reject : nat -> result
| NoResult.


Definition step9 z1 z2 z3 z4 hi fi ymin ymax w_ends y1 y4 f0 h0 (idepth : nat):=
  let w_base := IT.integral_intBounds prec (dvmin hi fi ymin) idepth z1 z3 rd in
  let w_i := iPlus w_ends w_base in
  let i1 := (IT.integral_intBounds prec (dv h0 f0) idepth y1 y4 rd) in
  let i2 := (IT.integral_intBounds prec (dvmax h0 f0 ymax) idepth z4 z2 rd) in
  let w_0 := 
    iPlus
      (i1)
      (iSub
	 (i2)
	 w_base
      ) in
  if iNeq w_i w_0 then Reject 9 else NoResult.


Definition step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends (idepth : nat):=
  let t := iSqrt(iSub y1 ymin) in
  let z1 := compare c1 (iDiv (iSqrt(three)) (two)) (iNeg t) t in
  let z3 := iSqrt(iSub y2 ymin) in
  let delta_i := IT.integral_intBounds prec (dxmin hi fi ymin) idepth z1 z3 rd in
  let delta_0 := IT.integral_intBounds prec (dxmax h0 f0 ymax) idepth z4 z2 rd in
  if iLt delta_i delta_0 then Reject 8 else
  let delta_0 := 
    iPlus 
      delta_0 
      (IT.integral_intBounds prec (dx h0 f0) idepth y1 y4 rd) in
  if iNeq delta_i delta_0 then Reject 8 else step9 z1 z2 z3 z4 hi fi ymin ymax w_ends y1 y4 f0 h0 idepth.


Definition step7 c1 h0 f0 y2 ymin ymax y1 fi hi w_ends (idepth : nat):=
  let yleft := iSqrt (iDiv f0 h0) in
  (* this was reformulated from Ocaml because of no side-effects, double check the semantics in case there is a problem *)
  if ~~((iLt ymin y2) && (iLt yleft ymax)) then 
    NoResult
  else
    let yleft :=  iMax y1 yleft in
    let y4 := thin (avgwt yleft ymax one_sixteenth) in
    let z2 := iSqrt(iSub ymax y2) in
    let z4 := iNeg (iSqrt(iSub ymax y4)) in
    if iGeq (iMult i1000 c1) (i998) then
      (
        let t := (avgwt y1 y2 float_half) in
        let delta_i := 
	    iPlus
	      (iMult 
	         (iSub (thin t) y1) 
	         (thin thirtythree_sixteenth))
	      (IT.integral_intBounds prec (dx hi fi) idepth (thin t) y2 rd) in
        let delta_0 := iMult (iNeg (iSub yleft y1)) (iSqrt three) in
        let t := avgwt yleft y4 one_sixteenth in
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
            if containsB c1 Fone then NoResult else step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth
      ) else step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth.


Definition step6 c1 h0 f0 c2 hi fi y1 y2  idepth := 
  let w_ends := 
    iPlus
      (iMult 
	 (iPow (iSub one c1) 2)
	 (iDiv
	    (iPlus two c1)
	    (three)
	 )
      )
      (iMult 
	 (iPow (iSub one c2) 2)
	 (iDiv
	    (iPlus two c2)
	    (three)
	 )
      ) in
  let ymin := iDiv (iNeg fi) (iPlus one (iSqrt (iPlus one (iMult fi hi)))) in 
  let ymax := iDiv (iPlus one (iSqrt (iPlus one (iMult f0 h0)))) (h0) in
  let y := compare c1 (iDiv (iSqrt three) two) ymin y1 in
  if iLt (iMult y hi) (iNeg one) then
    (
    (let r := iDiv (iDiv (iSqrt (three)) (two)) (iSub (iNeg hi) (iDiv one y)) in
     let w := iMult 
                (twoandahalf_int) 
                (iMult 
	           (iPlus y (iMult r (iDiv (iSqrt (three)) (two))))
	           (iSqr r)
                ) in
     if iLt w w_ends then Reject 6 else step7 c1 h0 f0 y2 ymin ymax y1  fi hi w_ends idepth)) else step7 c1 h0 f0 y2 ymin ymax y1  fi hi w_ends idepth.


Definition step5 c1 h0 f0 c2 hi fi y1 y2  idepth :=
if (Fgt (diam c2) float_half) then NoResult else step6 c1 h0 f0 c2 hi fi y1 y2  idepth.


Definition step4 c1 h0 f0 c2 hi fi y1 y2  idepth :=
if iLeq c1 half && iLeq h0 
    (iSub
       one
       (iMult (iSqrt three) (iDiv c1 y1))
    ) then Reject 4 else step5 c1 h0 f0 c2 hi fi y1 y2  idepth.

Definition step3 t fi hi c1 c2 h0 f0 y1  idepth:=
  let y2 := iSqrt(FInt.meet t int01) in
  let c2 := FInt.meet c2 
    (iDiv
       (iSub (iMult (iSub hi one) (y2)) (iDiv fi y2))
       (iSqrt three)) in
  if is_empty c2 then Reject 0 else step4 c1 h0 f0 c2 hi fi y1 y2  idepth.

Definition step2 c1 h0 idepth :=
  let hi := iSub two h0 in
  let y1 := iSqrt (iSub one (iSqr c1)) in
  let sub_hi_one := (iSub hi one) in (* H-i - 1, reused many times *)
  let fi := iSub
    (iMult sub_hi_one (iPow y1 2))
    (iMult c1 (iMult y1 (iSqrt three))) in
  let f0 := iNeg fi in
  let c2 := FInt.meet
    (FInt.I.join (iNeg c1) c1)
    (FInt.I.join (iNeg half) half) in
  let t := 
    iSub
      (iDiv 
	 (
	   iPlus (iMult (two) (iMult sub_hi_one (fi))) three
	 )
	 (
	   iPlus three (iSqr sub_hi_one)
	 )
      )
      (iSub one (iSqr c1))
  in 
  if iNeq (iPlus (iPow c2 2) t) one then 
    Reject 2
  else step3 t fi hi c1 c2 h0 f0 y1  idepth.

Definition step1 (c1 h0 : intervalle) (idepth : nat) := 
if (iGeq (iMult i1000 c1) i996) && (iLeq (iMult five h0) (one)) then Reject 1 else step2 c1 h0 idepth.

Search "midpoint".

Definition split x := 
  match x with
    | Inan => (Inan,Inan)
    |Ibnd a b => let m := FInt.I.midpoint x in 
                 (Ibnd a m,Ibnd m b)
end.

Fixpoint divideAndCheckRectangle y1 h0 idepth fuel :=
  match fuel with
  | O => false
  | S k =>
    let c1 := iSqrt (iSub one_int (iSqr y1)) in
    (match step1 c1 h0 idepth with
    | Reject i => true
    | NoResult =>
      let (y1a,y1b) := split y1 in
      let (h0a,h0b) := split h0 in
      (divideAndCheckRectangle y1a h0a idepth k)
      && (divideAndCheckRectangle y1a h0b idepth k)
      && (divideAndCheckRectangle y1b h0a idepth k)
      && (divideAndCheckRectangle y1b h0b idepth k) end) end.



Definition main idepth :=
  let y1 := int01 in
  let h0 := int010 in
    divideAndCheckRectangle y1 h0 idepth 15.

     (* if iLt w w_ends then reject c1 h0 6); *)

End Examples.
(* Require Import Interval_tactic. *)
(* Require Import Interval_generic_ops. *)
(* Require Import Interval_transcend. *)
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module F := SpecificFloat BigIntRadix2.
Require Import BigZ.
Definition prec10 := (10%bigZ) : F.precision.
Module Test := Examples F.
Print Test.prec.
Print Test.main.
(* Eval compute in Test.main 0. *)
Print Test.divideAndCheckRectangle.
Import Test.

(* battery of tests *)
Eval vm_compute in Test.compare I0 I0 I0 I0.

End Test.
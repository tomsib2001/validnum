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

Notation intervalle := FInt.I.type.
Notation float := F.type.

Definition iLt (i1 i2 : intervalle) := 
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Flt r1 l2) (* && (Flt l1 r2) *)
       else false
  else false.

Definition iGt (i1 i2 : intervalle) :=
  iLt i2 i1.


Definition iLeq (i1 i2 : intervalle) := 
  if i1 is Ibnd l1 r1
  then if i2 is Ibnd l2 r2
       then (Fle r1 l2) (* && (Fle l1 r2) *)
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

Definition compare (x y a b : intervalle) := 
  if iLt x y then a else 
    if iGt x y then b else
      FInt.I.join a b.

Definition is_empty x : bool := 
  match x with
    | Inan => false
    | Ibnd a b => Flt b a
  end.


Section Doubbub.

Variable prec : F.precision.
Variable rd : rounding_mode.

Definition Fone := F.fromZ 1.

Definition iPlus := (FInt.add prec).
Definition iSub := (FInt.sub prec).
Definition iMult := (FInt.mul prec).
Definition iDiv := FInt.div prec.
Definition iSqrt := FInt.sqrt prec.
Definition iSqr := fun i => FInt.power_int prec i 2. 
Definition iPow x n := FInt.power_int prec x n.
Definition iNeg := FInt.neg.
(* Definition iNeq x y := (iLt x y) || (iLt y x). *)
Definition iNeq x y := is_empty (FInt.meet x y).

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


(* sanity checks *)

Definition s1 := (FInt.I.join (iNeg one) one). (* should be [-1,1] *)
Definition s2 := (FInt.I.meet (iNeg one) one). (* should be empty *)
Definition small_interval := Ibnd F.zero (F.div rd prec (F.fromZ 1) (F.fromZ 32)).
Definition s3 := (iGeq (iMult i1000 one_int) i996).
Definition s4 := (iLeq (iMult five small_interval) (one)).

(* end sanity checks *)



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

Inductive result :=
| Reject : nat -> result
| NoResult : nat -> result.


Definition step9 z1 z2 z3 z4 hi fi ymin ymax w_ends y1 y4 f0 h0 idepth :=
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
  if iNeq w_i w_0 then Reject 9 else NoResult 9.


Definition step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth :=
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


Definition step7 c1 h0 f0 y2 ymin ymax y1 fi hi w_ends idepth :=
  let yleft := iSqrt (iDiv f0 h0) in
  (* this was reformulated from Ocaml because of no side-effects, double check the semantics in case there is a problem *)
  if ~~((iLt ymin y2) && (iLt yleft ymax)) then 
    NoResult 7
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
            if containsB c1 Fone then NoResult 7 else step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth
      ) else step8 c1 ymin y1 y2 fi hi z2 z4 ymax f0 h0 y4 w_ends idepth.


Definition step6 c1 h0 f0 c2 hi fi y1 y2 idepth := 
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


Definition step5 c1 h0 f0 c2 hi fi y1 y2 idepth :=
if (Fgt (diam c2) float_half) then NoResult 5 else step6 c1 h0 f0 c2 hi fi y1 y2 idepth.


Definition step4 c1 h0 f0 c2 hi fi y1 y2 idepth :=
if iLeq c1 half && iLeq h0 
    (iSub
       one
       (iMult (iSqrt three) (iDiv c1 y1))
    ) then Reject 4 else step5 c1 h0 f0 c2 hi fi y1 y2 idepth.

Definition step3 t fi hi c1 c2 h0 f0 y1 idepth:=
  let y2 := iSqrt(FInt.meet t int01) in
  let c2 := FInt.meet c2 
    (iDiv
       (iSub (iMult (iSub hi one) (y2)) (iDiv fi y2))
       (iSqrt three)) in
  if is_empty c2 then Reject 3 else step4 c1 h0 f0 c2 hi fi y1 y2 idepth.

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
  else step3 t fi hi c1 c2 h0 f0 y1 idepth.

Definition step1 (c1 h0 : intervalle) (idepth : nat) := 
if (iGeq (iMult i1000 c1) i996) && (iLeq (iMult five h0) (one)) then Reject 1 else step2 c1 h0 idepth.

Definition split x := 
  match x with
    | Inan => (Inan,Inan)
    |Ibnd a b => let m := FInt.I.midpoint x in 
                 (Ibnd a m,Ibnd m b)
end.

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
 
Fixpoint divideAndCheckRectangle y1 h0 idepth fuel nRej nNoRes lrects :=
  match fuel with
  | O => (false,nRej,nNoRes,lrects)
  | S k =>
    let c1 := iSqrt (iSub one (iSqr y1)) in
    (match step1 c1 h0 idepth with
    | Reject i => (true,update nRej i,nNoRes,(y1,h0,S k)::lrects)
    | NoResult i =>
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
            (b1 && b2 && b3 && b4,n4,nnr4,l4)
          else
            (b3,n3,nnr3,l3)
        else
          (b2,n2,nnr2,l2)
      else
        (b1,n1,nnr1,l1)
     end) end.

Open Scope nat_scope.

Definition main idepth depth :=
  let y1 := int01 in
  let h0 := int010 in
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
Definition rd := rnd_NE.

Open Scope nat_scope.

Eval vm_compute in Test.main prec60 rd 5 20.

Eval vm_compute in Test.s1.
Eval vm_compute in Test.s2.
Eval vm_compute in (Test.s3 prec60).
Eval vm_compute in (Test.s4 prec60 rd).
Import Test.

Print Test.divideAndCheckRectangle.
Import Test.

(* battery of tests *)
Eval vm_compute in Test.compare I0 I0 I0 I0.

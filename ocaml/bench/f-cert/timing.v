
Require Import QArith BigZ seq.
(*
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Require Import Interval_interval_float.
Require Import Interval_interval.
Require Import Interval_xreal. 
Require Import Interval_generic.

Module F := SpecificFloat BigIntRadix2.
Module I := FloatInterval F.

Definition Itv:= f_interval F.type.
Definition i0:= I.zero.
Definition i1:= (I.fromZ 1).
Definition Iplus:= I.add 50%bigZ.
Definition Iminus:= I.sub 50%bigZ.
Definition Itimes:= I.mul 50%bigZ.
Definition Iopp:= I.neg.
Definition Ipow:= I.power_int 50%bigZ.

Infix "I+":= Iplus (at level 45).
Infix "I-":= Iminus (at level 45).
Infix "I*":= Itimes (at level 45).
Notation "I- x":= (Iopp x) (at level 45).
Infix "I^":= Ipow (at level 45).

Definition QtoItv:= fun q =>
 I.bnd
   (F.div Interval_definitions.rnd_DN 50%bigZ (F.fromZ (Qnum q)) (F.fromZ (Zpos (Qden q))))
   (F.div Interval_definitions.rnd_UP 50%bigZ (F.fromZ (Qnum q)) (F.fromZ (Zpos (Qden q)))).

Definition QtoItv_opt:= fun q =>
 let den:=  (F.fromZ (Zpos (Qden q))) in
 let nom:=  (F.fromZ (Qnum q)) in
 I.bnd (F.div Interval_definitions.rnd_DN 50%bigZ nom den)
       (F.div Interval_definitions.rnd_UP 50%bigZ nom den).
*)
(* ******************** *)
Inductive PQ :=
 | PEc : Q -> PQ
 | PEX : positive -> PQ
 | PEadd : PQ -> PQ -> PQ
 | PEsub : PQ -> PQ -> PQ
 | PEmul : PQ -> PQ -> PQ
 | PEopp : PQ -> PQ
 | PEpow : PQ -> Z -> PQ.
(* ******************** *)


Definition PQ0 := PEc 0%Q.
Definition PQ1 := PEc 1%Q.

(*
(* ******************** *)
Inductive PolI : Type :=
 | IPc : Itv -> PolI
 | IPinj : positive -> PolI -> PolI
 | IPX : PolI -> positive -> PolI -> PolI.
(* ******************** *)


Definition PolI0 := IPc i0.
Definition PolI1 := IPc i1.
Local Open Scope positive.

  Definition mkIPinj j P :=
  match P with
  | IPc _ => P
  | IPinj j' Q => IPinj (j + j') Q
  | _ => IPinj j P
  end.

 Definition mkIPinj_pred j P:=
  match j with
  | xH => P
  | xO j => IPinj (Pos.pred_double j) P
  | xI j => IPinj (xO j) P
  end.

 Definition mkIPX P i I := IPX P i I.
 Definition mkIXi i := IPX PolI1 i PolI0.
 Definition mkIX := mkIXi 1.
 Definition mkI_X j := mkIPinj_pred j mkIX.

  (** Opposite of addition *)

 Fixpoint IPopp (P:PolI) : PolI :=
  match P with
  | IPc c => IPc (I-c)
  | IPinj j Q => IPinj j (IPopp Q)
  | IPX P i Q => IPX (IPopp P) i (IPopp Q)
  end.

 Notation "?-- P" := (IPopp P) (at level 40).

  (** Addition et subtraction *)

 Fixpoint IPaddC (P:PolI) (c:Itv) : PolI :=
  match P with
  | IPc c1 => IPc (c1 I+ c)
  | IPinj j Q => IPinj j (IPaddC Q c)
  | IPX P i Q => IPX P i (IPaddC Q c)
  end.

 Fixpoint IPsubC (P:PolI) (c:Itv) : PolI :=
  match P with
  | IPc c1 => IPc (c1 I- c)
  | IPinj j Q => IPinj j (IPsubC Q c)
  | IPX P i Q => IPX P i (IPsubC Q c)
  end.

Section PopI.

  Variable Pop : PolI -> PolI -> PolI.
  Variable I : PolI.

  Fixpoint IPaddI (j:positive) (P:PolI) : PolI :=
   match P with
   | IPc c => mkIPinj j (IPaddC I c)
   | IPinj j' I' =>
     match Z.pos_sub j' j with
     | Zpos k =>  mkIPinj j (Pop (IPinj k I') I)
     | Z0 => mkIPinj j (Pop I' I)
     | Zneg k => mkIPinj j' (IPaddI k I')
     end
   | IPX P i I' =>
     match j with
     | xH => IPX P i (Pop I' I)
     | xO j => IPX P i (IPaddI (Pos.pred_double j) I')
     | xI j => IPX P i (IPaddI (xO j) I')
     end
   end.

  Fixpoint IPsubI (j:positive) (P:PolI) : PolI :=
   match P with
   | IPc c => mkIPinj j (IPaddC (?--I) c)
   | IPinj j' I' =>
     match Z.pos_sub j' j with
     | Zpos k =>  mkIPinj j (Pop (IPinj k I') I)
     | Z0 => mkIPinj j (Pop I' I)
     | Zneg k => mkIPinj j' (IPsubI k I')
     end
   | IPX P i I' =>
     match j with
     | xH => IPX P i (Pop I' I)
     | xO j => IPX P i (IPsubI (Pos.pred_double j) I')
     | xI j => IPX P i (IPsubI (xO j) I')
     end
   end.

 Variable P' : PolI.

 Fixpoint IPaddX (i':positive) (P:PolI) : PolI :=
  match P with
  | IPc c => IPX P' i' P
  | IPinj j I' =>
    match j with
    | xH =>  IPX P' i' I'
    | xO j => IPX P' i' (IPinj (Pos.pred_double j) I')
    | xI j => IPX P' i' (IPinj (xO j) I')
    end
  | IPX P i I' =>
    match Z.pos_sub i i' with
    | Zpos k => mkIPX (Pop (IPX P k PolI0) P') i' I'
    | Z0 => mkIPX (Pop P P') i I'
    | Zneg k => mkIPX (IPaddX k P) i I'
    end
  end.

 Fixpoint IPsubX (i':positive) (P:PolI) : PolI :=
  match P with
  | IPc c => IPX (?--P') i' P
  | IPinj j I' =>
    match j with
    | xH =>  IPX (?--P') i' I'
    | xO j => IPX (?--P') i' (IPinj (Pos.pred_double j) I')
    | xI j => IPX (?--P') i' (IPinj (xO j) I')
    end
  | IPX P i I' =>
    match Z.pos_sub i i' with
    | Zpos k => mkIPX (Pop (IPX P k PolI0) P') i' I'
    | Z0 => mkIPX (Pop P P') i I'
    | Zneg k => mkIPX (IPsubX k P) i I'
    end
  end.

End PopI.

 Fixpoint IPadd (P P': PolI) {struct P'} : PolI :=
  match P' with
  | IPc c' => IPaddC P c'
  | IPinj j' I' => IPaddI IPadd I' j' P
  | IPX P' i' I' =>
    match P with
    | IPc c => IPX P' i' (IPaddC I' c)
    | IPinj j Q =>
      match j with
      | xH => IPX P' i' (IPadd Q I')
      | xO j => IPX P' i' (IPadd (IPinj (Pos.pred_double j) Q) I')
      | xI j => IPX P' i' (IPadd (IPinj (xO j) Q) I')
      end
    | IPX P i Q =>
      match Z.pos_sub i i' with
      | Zpos k => mkIPX (IPadd (IPX P k PolI0) P') i' (IPadd Q I')
      | Z0 => mkIPX (IPadd P P') i (IPadd Q I')
      | Zneg k => mkIPX (IPaddX IPadd P' k P) i (IPadd Q I')
      end
    end
  end.
 
 Infix "?++" := IPadd (at level 40).

 Fixpoint IPsub (P P': PolI) {struct P'} : PolI :=
  match P' with
  | IPc c' => IPsubC P c'
  | IPinj j' I' => IPsubI IPsub I' j' P
  | IPX P' i' I' =>
    match P with
    | IPc c => IPX (?--P') i' (IPaddC (?--I') c)
    | IPinj j Q =>
      match j with
      | xH => IPX (?--P') i' (IPsub Q I')
      | xO j => IPX (?--P') i' (IPsub (IPinj (Pos.pred_double j) Q) I')
      | xI j => IPX (?--P') i' (IPsub (IPinj (xO j) Q) I')
      end
   | IPX P i Q =>
      match Z.pos_sub i i' with
      | Zpos k => mkIPX (IPsub (IPX P k PolI0) P') i' (IPsub Q I')
      | Z0 => mkIPX (IPsub P P') i (IPsub Q I')
      | Zneg k => mkIPX (IPsubX IPsub P' k P) i (IPsub Q I')
      end
    end
  end.
 Infix "?--" := IPsub (at level 40).

  (** Multiplication *)

 Fixpoint IPmulC (P:PolI) (c:Itv) : PolI :=
  match P with
  | IPc c' => IPc (c' I* c)
  | IPinj j Q => mkIPinj j (IPmulC Q c)
  | IPX P i Q => mkIPX (IPmulC P c) i (IPmulC Q c)
  end.

  Section PmulI.
  Variable IPmul : PolI -> PolI -> PolI.
  Variable I : PolI.
  Fixpoint IPmulI (j:positive) (P:PolI) : PolI :=
   match P with
   | IPc c => mkIPinj j (IPmulC I c)
   | IPinj j' I' =>
     match Z.pos_sub j' j with
     | Zpos k => mkIPinj j (IPmul (IPinj k I') I)
     | Z0 => mkIPinj j (IPmul I' I)
     | Zneg k => mkIPinj j' (IPmulI k I')
     end
   | IPX P' i' I' =>
     match j with
     | xH => mkIPX (IPmulI xH P') i' (IPmul I' I)
     | xO j' => mkIPX (IPmulI j P') i' (IPmulI (Pos.pred_double j') I')
     | xI j' => mkIPX (IPmulI j P') i' (IPmulI (xO j') I')
     end
   end.

 End PmulI.

   Fixpoint IPmul (P P'' : PolI) {struct P''} : PolI :=
   match P'' with
   | IPc c => IPmulC P c
   | IPinj j' I' => IPmulI IPmul I' j' P
   | IPX P' i' I' =>
     match P with
     | IPc c => IPmulC P'' c
     | IPinj j Q =>
       let II' :=
         match j with
         | xH => IPmul Q I'
         | xO j => IPmul (IPinj (Pos.pred_double j) Q) I'
         | xI j => IPmul (IPinj (xO j) Q) I'
         end in
       mkIPX (IPmul P P') i' II'
     | IPX P i Q =>
       let II' := IPmul Q I' in
       let PI' := IPmulI IPmul I' xH P in
       let IP' := IPmul (mkIPinj xH Q) P' in
       let PP' := IPmul P P' in
       (mkIPX (mkIPX PP' i PolI0 ?++ IP') i' PolI0) ?++ mkIPX PI' i II'
     end
  end.

 Infix "?**" := IPmul (at level 40).

  Section POWER.
    
  Variable subst_l : PolI -> PolI.
    
  Fixpoint IPpow_pos (res P:PolI) (p:positive) : PolI :=
   match p with
   | xH => subst_l (res ?** P)
   | xO p => IPpow_pos (IPpow_pos res P p) P p
   | xI p => subst_l ((IPpow_pos (IPpow_pos res P p) P p) ?** P)
   end.

  Definition IPpow_N P n :=
   match n with
   | N0 => PolI1
   | Npos p => IPpow_pos PolI1 P p
   end.

 End POWER.
 
 (** Enclosure of a "polynomial" towards Itv *)

 Require Import Env.
 Fixpoint encl_polI (l:Env Itv) (P:PolI) : Itv :=
  match P with
  | IPc c => c
  | IPinj j Q => encl_polI (jump j l) Q
  | IPX P i Q => (encl_polI l P I* ((hd l) I^ (Z.pos i))) I+ encl_polI  (tail l) Q 
  end.

 Fixpoint toPolI (P:PQ) : PolI :=
  match P with
    |PEc q => IPc (QtoItv q )
    |PEX j => mkI_X j
    |PEadd pe1 pe2 => IPadd (toPolI pe1) (toPolI pe2)
    |PEsub pe1 pe2 => IPsub (toPolI pe1) (toPolI pe2)
    |PEmul pe1 pe2 => IPmul (toPolI pe1) (toPolI pe2)
    |PEopp pe1 => IPopp (toPolI pe1)
    |PEpow pe1 n => IPpow_N (fun p => p) (toPolI pe1) (ZtoN n)
  end.

Inductive IPQ :=
| IPEc : Itv -> IPQ
| IPEx : positive -> IPQ
| IPEadd : IPQ -> IPQ -> IPQ
| IPEsub : IPQ -> IPQ -> IPQ                         
| IPEmul : IPQ -> IPQ -> IPQ
| IPEopp : IPQ -> IPQ
| IPEpow : IPQ -> Z -> IPQ.                    

Fixpoint cencl pe :=
  match pe with
    | PEc q => IPEc (QtoItv q)
    | PEX j => IPEx j
    | PEadd pe1 pe2 => IPEadd (cencl pe1) (cencl pe2)
    | PEsub pe1 pe2 => IPEsub (cencl pe1) (cencl pe2)
    | PEmul pe1 pe2 => IPEmul (cencl pe1) (cencl pe2)
    | PEopp pe1 => IPEopp (cencl pe1)
    | PEpow pe1 n => IPEpow (cencl pe1) n
  end.
Fixpoint cencl_opt pe :=
  match pe with
    | PEc q => IPEc (QtoItv_opt q)
    | PEX j => IPEx j
    | PEadd pe1 pe2 => IPEadd (cencl pe1) (cencl pe2)
    | PEsub pe1 pe2 => IPEsub (cencl pe1) (cencl pe2)
    | PEmul pe1 pe2 => IPEmul (cencl pe1) (cencl pe2)
    | PEopp pe1 => IPEopp (cencl pe1)
    | PEpow pe1 n => IPEpow (cencl pe1) n
  end.

Fixpoint IPQtoPolI (P:IPQ) : PolI :=
  match P with
    |IPEc q => IPc q
    |IPEx j => mkI_X j
    |IPEadd pe1 pe2 => IPadd (IPQtoPolI pe1) (IPQtoPolI pe2)
    |IPEsub pe1 pe2 => IPsub (IPQtoPolI pe1) (IPQtoPolI pe2)
    |IPEmul pe1 pe2 => IPmul (IPQtoPolI pe1) (IPQtoPolI pe2)
    |IPEopp pe1 => IPopp (IPQtoPolI pe1)
    |IPEpow pe1 n => IPpow_N (fun p => p) (IPQtoPolI pe1) (ZtoN n)
  end.
*)

Require Import seq.
Section FoldRightPsatz.
  Set Implicit Arguments. 
  Variables (A Rt: Type) (e : Rt) (plus : Rt -> Rt -> Rt) (interp : A -> Rt).

  Fixpoint foldr_psatz l := match l with
    [::] => e
  | [::hd] => interp hd
  | x::tl => plus (interp x) (foldr_psatz tl) end.
End FoldRightPsatz.

Definition itv := (Q * Q)%type.
Definition QBOX := seq itv.
Definition nth_box := seq.nth (pair 0%Q 0%Q).
Definition lo_box box n := fst (nth_box box n).
Definition up_box box n := snd (nth_box box n).

Definition Eig := nat.
Inductive Ineq : Type :=
  | Triv : Ineq
  | Hyp : nat -> Ineq
  | LoBnd : nat -> Ineq
  | UpBnd : nat -> Ineq
  | SqrBnd : nat -> Ineq.
Definition Sos_block :=  (Eig * (PQ))%type.
Definition Sos := seq Sos_block.
Definition Putinar_summand := (Sos * Ineq)%type.
Definition Putinar_psatz := seq Putinar_summand.

Local Open Scope Q.
Definition seqQ := seq Q.
Definition nthQ := seq.nth 0.
Definition nthPQ := seq.nth PQ0.

Record cert_pop := mk_cert_pop {
 eigs : seqQ;
 sos : seq Putinar_summand
}.


Definition ineq_toPQ box hyps ineq :=
  match ineq with
    | Triv => PEc 1
    | Hyp n => nthPQ hyps n
    | LoBnd 0 => PEsub (PEX 1%positive) (PEc (lo_box box 0))
    | LoBnd n => PEsub (PEX (Pos.of_nat n + 1)%positive) (PEc (lo_box box n))
    | UpBnd 0 => PEsub (PEc (up_box box 0)) (PEX 1%positive)
    | UpBnd n => PEsub (PEc (up_box box n)) (PEX (Pos.of_nat n + 1)%positive)
    | SqrBnd 0 => PEmul (PEsub (PEX 1%positive) (PEc (lo_box box 0)))
                         (PEsub (PEc (up_box box 0)) (PEX 1%positive))
    | SqrBnd n => PEmul (PEsub (PEX (Pos.of_nat n + 1)%positive) (PEc (lo_box box n)))
                        (PEsub (PEc (up_box box n)) (PEX (Pos.of_nat n + 1)%positive))
  end.
Definition Sos_block_toPQ eig_pos (sos_block : Sos_block) := 
   let (eig, sqr) := sos_block in 
   PEmul (PEpow sqr 2) (PEc (nthQ eig_pos eig)).

Definition Sos_toPQ eig_pos (sos: Sos) :=
  foldr_psatz PQ0 PEadd (Sos_block_toPQ eig_pos) sos.

Definition Putinar_summand_toPQ box hyps eig_pos (putinar_summand: Putinar_summand) := 
  let (sos, ineq) := putinar_summand in
   PEmul (Sos_toPQ eig_pos sos) (ineq_toPQ box hyps ineq).

Definition Psatz_toPQ box hyps eig_pos summands :=
  foldr_psatz PQ0 PEadd (Putinar_summand_toPQ box hyps eig_pos) summands.
(*
Definition itv_nneg (xi: Itv):= 
  match xi with
   | Interval_interval_float.Inan => false
   | Interval_interval_float.Ibnd f _ =>
                       match f with
                        | Interval_specific_ops.Fnan => false
                        | Interval_specific_ops.Float m _ => BigZ.leb 0 m
                       end
  end.

Definition QQtoItv:= fun q1 q2 =>
 I.bnd
   (F.div Interval_definitions.rnd_DN 50%bigZ (F.fromZ (Qnum q1)) (F.fromZ (Zpos (Qden q1))))
   (F.div Interval_definitions.rnd_UP 50%bigZ (F.fromZ (Qnum q2)) (F.fromZ (Zpos (Qden q2)))).

Definition box_toEnvI box := fun p =>
                               QQtoItv (lo_box box ((Pos.to_nat p) - 1)%nat) (up_box box ((Pos.to_nat p) - 1)).

Definition checker_pop_encl box hyps obj cert :=
  let cert_pq := Psatz_toPQ box hyps (eigs cert) (sos cert) in
  let certif_itv:= encl_polI (box_toEnvI box) (toPolI (PEsub obj cert_pq)) in
  itv_nneg certif_itv.

Definition ISos_block := (Eig*PolI)%type.
Definition ISos := seq ISos_block.
Definition IPutinar_summand := (ISos * Ineq)%type.
Definition IPutinar_psatz := seq IPutinar_summand.

Definition ineq_toPolI box hyps ineq :=
  match ineq with
    | Triv => IPc i1
    | Hyp n => toPolI (nthPQ hyps n)
    | LoBnd 0 => toPolI (PEsub (PEX 1%positive) (PEc (lo_box box 0)))
    | LoBnd n => toPolI (PEsub (PEX (Pos.of_nat n + 1)%positive) (PEc (lo_box box n)))
    | UpBnd 0 => toPolI (PEsub (PEc (up_box box 0)) (PEX 1%positive))
    | UpBnd n => toPolI (PEsub (PEc (up_box box n)) (PEX (Pos.of_nat n + 1)%positive))
    | SqrBnd 0 => toPolI (PEmul (PEsub (PEX 1%positive) (PEc (lo_box box 0)))
                         (PEsub (PEc (up_box box 0)) (PEX 1%positive)))
    | SqrBnd n => toPolI (PEmul (PEsub (PEX (Pos.of_nat n + 1)%positive) (PEc (lo_box box n)))
                        (PEsub (PEc (up_box box n)) (PEX (Pos.of_nat n + 1)%positive)))
  end.

Definition Sos_block_toPolI eig_pos (sos_block : ISos_block) := 
   let (eig, sqr) := sos_block in 
   IPmul (IPpow_N (fun p => p) sqr 2) (IPc (QtoItv (nthQ eig_pos eig))).

Definition Sos_toPolI eig_pos (sos: ISos) :=
  foldr_psatz PolI0 IPadd (Sos_block_toPolI eig_pos) sos.

Definition Putinar_summand_toPolI box hyps eig_pos (putinar_summand: IPutinar_summand) := 
  let (sos, ineq) := putinar_summand in
   IPmul (Sos_toPolI eig_pos sos) (ineq_toPolI box hyps ineq).

Definition Psatz_toPolI box hyps eig_pos summands :=
  foldr_psatz PolI0 IPadd (Putinar_summand_toPolI box hyps eig_pos) summands.

Inductive PolQ :=
 | QPc : Q -> PolQ
 | QPinj : positive -> PolQ -> PolQ
 | QPX : PolQ -> positive -> PolQ -> PolQ.
Definition PolQ0 := QPc 0%Q.
Definition PolQ1 := QPc 1%Q.

 Definition mkQPinj j P :=
  match P with
  | QPc _ => P
  | QPinj j' Q => QPinj (j + j') Q
  | _ => QPinj j P
  end.

 Definition mkQPinj_pred j P:=
  match j with
  | xH => P
  | xO j => QPinj (Pos.pred_double j) P
  | xI j => QPinj (xO j) P
  end.

 Definition mkQPX P i Q := QPX P i Q.


 Definition mkQXi i := QPX PolQ1 i PolQ0.
 Definition mkQX := mkQXi 1.
 Definition mkQ_X j := mkQPinj_pred j mkQX.

  (** Opposite of addition *)
Local Open Scope Q.
 Fixpoint QPopp (P:PolQ) : PolQ :=
  match P with
  | QPc c => QPc (Qopp c)
  | QPinj j Q => QPinj j (QPopp Q)
  | QPX P i Q => QPX (QPopp P) i (QPopp Q)
  end.

 Notation "!-- P" := (QPopp P) (at level 40).

  (** Addition et subtraction *)

 Fixpoint QPaddC (P:PolQ) (c:Q) : PolQ :=
  match P with
  | QPc c1 => QPc (c1 + c)
  | QPinj j Q => QPinj j (QPaddC Q c)
  | QPX P i Q => QPX P i (QPaddC Q c)
  end.

 Fixpoint QPsubC (P:PolQ) (c:Q) : PolQ :=
  match P with
  | QPc c1 => QPc (c1 - c)
  | QPinj j Q => QPinj j (QPsubC Q c)
  | QPX P i Q => QPX P i (QPsubC Q c)
  end.

Section PopIQ.

  Variable Pop : PolQ -> PolQ -> PolQ.
  Variable Q : PolQ.

  Fixpoint QPaddI (j:positive) (P:PolQ) : PolQ :=
   match P with
   | QPc c => mkQPinj j (QPaddC Q c)
   | QPinj j' Q' =>
     match Z.pos_sub j' j with
     | Zpos k =>  mkQPinj j (Pop (QPinj k Q') Q)
     | Z0 => mkQPinj j (Pop Q' Q)
     | Zneg k => mkQPinj j' (QPaddI k Q')
     end
   | QPX P i Q' =>
     match j with
     | xH => QPX P i (Pop Q' Q)
     | xO j => QPX P i (QPaddI (Pos.pred_double j) Q')
     | xI j => QPX P i (QPaddI (xO j) Q')
     end
   end.

  Fixpoint QPsubI (j:positive) (P:PolQ) : PolQ :=
   match P with
   | QPc c => mkQPinj j (QPaddC (!--Q) c)
   | QPinj j' Q' =>
     match Z.pos_sub j' j with
     | Zpos k =>  mkQPinj j (Pop (QPinj k Q') Q)
     | Z0 => mkQPinj j (Pop Q' Q)
     | Zneg k => mkQPinj j' (QPsubI k Q')
     end
   | QPX P i Q' =>
     match j with
     | xH => QPX P i (Pop Q' Q)
     | xO j => QPX P i (QPsubI (Pos.pred_double j) Q')
     | xI j => QPX P i (QPsubI (xO j) Q')
     end
   end.

 Variable P' : PolQ.

 Fixpoint QPaddX (i':positive) (P:PolQ) : PolQ :=
  match P with
  | QPc c => QPX P' i' P
  | QPinj j Q' =>
    match j with
    | xH =>  QPX P' i' Q'
    | xO j => QPX P' i' (QPinj (Pos.pred_double j) Q')
    | xI j => QPX P' i' (QPinj (xO j) Q')
    end
  | QPX P i Q' =>
    match Z.pos_sub i i' with
    | Zpos k => mkQPX (Pop (QPX P k PolQ0) P') i' Q'
    | Z0 => mkQPX (Pop P P') i Q'
    | Zneg k => mkQPX (QPaddX k P) i Q'
    end
  end.

 Fixpoint QPsubX (i':positive) (P:PolQ) : PolQ :=
  match P with
  | QPc c => QPX (!--P') i' P
  | QPinj j Q' =>
    match j with
    | xH =>  QPX (!--P') i' Q'
    | xO j => QPX (!--P') i' (QPinj (Pos.pred_double j) Q')
    | xI j => QPX (!--P') i' (QPinj (xO j) Q')
    end
  | QPX P i Q' =>
    match Z.pos_sub i i' with
    | Zpos k => mkQPX (Pop (QPX P k PolQ0) P') i' Q'
    | Z0 => mkQPX (Pop P P') i Q'
    | Zneg k => mkQPX (QPsubX k P) i Q'
    end
  end.

End PopIQ.

 Fixpoint QPadd (P P': PolQ) {struct P'} : PolQ :=
  match P' with
  | QPc c' => QPaddC P c'
  | QPinj j' Q' => QPaddI QPadd Q' j' P
  | QPX P' i' Q' =>
    match P with
    | QPc c => QPX P' i' (QPaddC Q' c)
    | QPinj j Q =>
      match j with
      | xH => QPX P' i' (QPadd Q Q')
      | xO j => QPX P' i' (QPadd (QPinj (Pos.pred_double j) Q) Q')
      | xI j => QPX P' i' (QPadd (QPinj (xO j) Q) Q')
      end
    | QPX P i Q =>
      match Z.pos_sub i i' with
      | Zpos k => mkQPX (QPadd (QPX P k PolQ0) P') i' (QPadd Q Q')
      | Z0 => mkQPX (QPadd P P') i (QPadd Q Q')
      | Zneg k => mkQPX (QPaddX QPadd P' k P) i (QPadd Q Q')
      end
    end
  end.
 
 Infix "!++" := QPadd (at level 40).

 Fixpoint QPsub (P P': PolQ) {struct P'} : PolQ :=
  match P' with
  | QPc c' => QPsubC P c'
  | QPinj j' Q' => QPsubI QPsub Q' j' P
  | QPX P' i' Q' =>
    match P with
    | QPc c => QPX (!--P') i' (QPaddC (!--Q') c)
    | QPinj j Q =>
      match j with
      | xH => QPX (!--P') i' (QPsub Q Q')
      | xO j => QPX (!--P') i' (QPsub (QPinj (Pos.pred_double j) Q) Q')
      | xI j => QPX (!--P') i' (QPsub (QPinj (xO j) Q) Q')
      end
    | QPX P i Q =>
      match Z.pos_sub i i' with
      | Zpos k => mkQPX (QPsub (QPX P k PolQ0) P') i' (QPsub Q Q')
      | Z0 => mkQPX (QPsub P P') i (QPsub Q Q')
      | Zneg k => mkQPX (QPsubX QPsub P' k P) i (QPsub Q Q')
      end
    end
  end.
 Infix "!--" := QPsub (at level 40).

  (** Multiplication *)

 Fixpoint QPmulC (P:PolQ) (c:Q) : PolQ :=
  match P with
  | QPc c' => QPc (c' * c)
  | QPinj j Q => mkQPinj j (QPmulC Q c)
  | QPX P i Q => mkQPX (QPmulC P c) i (QPmulC Q c)
  end.

  Section PmulIQ.
  Variable QPmul : PolQ -> PolQ -> PolQ.
  Variable Q : PolQ.
  Fixpoint QPmulIQ (j:positive) (P:PolQ) : PolQ :=
   match P with
   | QPc c => mkQPinj j (QPmulC Q c)
   | QPinj j' Q' =>
     match Z.pos_sub j' j with
     | Zpos k => mkQPinj j (QPmul (QPinj k Q') Q)
     | Z0 => mkQPinj j (QPmul Q' Q)
     | Zneg k => mkQPinj j' (QPmulIQ k Q')
     end
   | QPX P' i' Q' =>
     match j with
     | xH => mkQPX (QPmulIQ xH P') i' (QPmul Q' Q)
     | xO j' => mkQPX (QPmulIQ j P') i' (QPmulIQ (Pos.pred_double j') Q')
     | xI j' => mkQPX (QPmulIQ j P') i' (QPmulIQ (xO j') Q')
     end
   end.

 End PmulIQ.

   Fixpoint QPmul (P P'' : PolQ) {struct P''} : PolQ :=
   match P'' with
   | QPc c => QPmulC P c
   | QPinj j' Q' => QPmulIQ QPmul Q' j' P
   | QPX P' i' Q' =>
     match P with
     | QPc c => QPmulC P'' c
     | QPinj j Q =>
       let QQ' :=
         match j with
         | xH => QPmul Q Q'
         | xO j => QPmul (QPinj (Pos.pred_double j) Q) Q'
         | xI j => QPmul (QPinj (xO j) Q) Q'
         end in
       mkQPX (QPmul P P') i' QQ'
     | QPX P i Q=>
       let QQ' := QPmul Q Q' in
       let PQ' := QPmulIQ QPmul Q' xH P in
       let QP' := QPmul (mkQPinj xH Q) P' in
       let PP' := QPmul P P' in
       (mkQPX (mkQPX PP' i PolQ0 !++ QP') i' PolQ0) !++ mkQPX PQ' i QQ'
     end
  end.

 Infix "!**" := QPmul (at level 40).

  Fixpoint QPsquare (P:PolQ) : PolQ :=
   match P with
   | QPc c => QPc (c * c)
   | QPinj j Q => QPinj j (QPsquare Q)
   | QPX P i Q =>
     let twoPQ := QPmul P (mkQPinj xH (QPmulC Q (2#1))) in
     let Q2 := QPsquare Q in
     let P2 := QPsquare P in
     mkQPX (mkQPX P2 i PolQ0 !++ twoPQ) i Q2
   end.

  Section QPOWER.
  Variable subst_l : PolQ -> PolQ.
  Fixpoint QPpow_pos (res P:PolQ) (p:positive) : PolQ :=
   match p with
   | xH => subst_l (res !** P)
   | xO p => QPpow_pos (QPpow_pos res P p) P p
   | xI p => subst_l ((QPpow_pos (QPpow_pos res P p) P p) !** P)
   end.

  Definition QPpow_N P n :=
   match n with
   | N0 => PolQ1
   | Npos p => QPpow_pos PolQ1 P p
   end.
  End QPOWER.
  
 Fixpoint toPolQ P :=
   match P with
   | PEc c => QPc c
   | PEX j => mkQ_X j
   | PEadd pe1 pe2 => QPadd (toPolQ pe1) (toPolQ pe2)
   | PEsub pe1 pe2 => QPsub (toPolQ pe1) (toPolQ pe2)
   | PEmul pe1 pe2 => QPmul (toPolQ pe1) (toPolQ pe2)
   | PEopp pe1 => QPopp (toPolQ pe1)
   | PEpow pe1 n => QPpow_N (fun p => p) (toPolQ pe1) (ZtoN n)
   end.


Definition Sos_block_polQ :=  (Eig * (PolQ))%type.

Definition toSosblockpolQ (sos_block:Sos_block) := match sos_block with (eig_pos, pq) => (eig_pos, toPolQ pq) end.

Definition Sos_block_toPolQ eig_pos (sos_block : Sos_block_polQ) := 
   let (eig, sqr) := sos_block in 
   (eig_pos, QPmulC  (QPsquare sqr) (nthQ eig_pos eig)).

Print Sos_block_toPolQ.

Definition poli_vij := seq PolI.

Fixpoint vij_toPolQ eigs sos := match (eigs,sos) with
                              | (hd1::tl1,hd2::tl2) => (Sos_block_toPolQ hd1 hd2) :: (vij_toPolQ tl1 tl2 )
                              | (_,_) => [::]
                                end.
Check vij_toPolQ.

fix foldr_psatz sos :=
  match sos with
  | [::] => [::]
  | [:: x] => [::Sos_block_toPolQ eig_pos x]
  | [:: x, _ & _] => plus (interp x) (foldr_psatz tl)
  end

Fixpoint cencl_polq (P:PolQ) : PolI :=
  match P with
  | QPc c => IPc (QtoItv c)
  | QPinj j Q => IPinj j (cencl_polq Q)
  | QPX P i Q => IPX (cencl_polq P) i (cencl_polq Q) 
  end. 

Fixpoint cencl_vij vij := match vij with
  | [::] => PolI0
  | [::hd] => cencl_polq hd
  | x::tl => IPadd (cencl_polq x) (cencl_vij tl)
end.

Fixpoint Sum_vij (l:seq PolI) := match l with
  | [::] => PolI0
  | [::hd] => hd
  | x::tl => IPadd x (Sum_vij tl)
 end.
*)
  

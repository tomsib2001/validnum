open Basicdefs;;
open Reification;;
open Poly;;
open Quasiring;;

module Recurrence (R : QUASIRING) =
struct
  module SFP=PolyOfQuasiRing(SymFunQuasiRing(R));;
  type recurrence = SFP.polynomial

  let (expRec : recurrence) =
    SFP.makePol([Plus(Var "n",Const R.one),1 ; (Const(R.neg R.one),0)]);;

  let rec applyRec (r : recurrence) (phi : 'a -> 'b) (initCond : 'b list) n =
  let m = List.length initCond in
  assert(m = SFP.degree r);
  let rec aux vect compt = match compt with
    | 0 -> List.
end;;

module R = Recurrence(IntervalQuasiRing);;

let expRec = []



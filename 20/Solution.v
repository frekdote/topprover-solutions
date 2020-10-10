Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Auxiliary lemmas to convert functions in the Coq standard library into the *)
(* ones in MathComp                                                           *)
(******************************************************************************)

Require Import Arith.

Lemma lebE m n : (m <=? n) = (m <= n).
Proof. by apply/Nat.leb_spec0/leP. Qed.

Lemma minE m n : Nat.min m n = minn m n.
rewrite /minn; case: leqP => [| /ltnW] /leP.
  exact: Nat.min_r.
exact: Nat.min_l.
Qed.

(******************************************************************************)
(* Instances for enabling lia to handle MathComp functions                    *)
(******************************************************************************)

Require Import ZArith ZifyClasses ZifyInst ZifyBool Lia.

Instance Op_addn : BinOp addn := Op_plus.
Add BinOp Op_addn.

Instance Op_subn : BinOp subn := Op_sub.
Add BinOp Op_subn.

Instance Op_minn : BinOp minn :=
  { TBOp := Z.min;
    TBOpInj := ltac:(by move=> *; rewrite /= -minE; lia) }.
Add BinOp Op_minn.

Instance Op_leq : BinOp leq :=
  { TBOp := fun x y => isLeZero (x - y);
    TBOpInj := ltac:(by move=> *; rewrite -lebE Z_of_nat_leb_iff Z_leb_sub) }.
Add BinOp Op_leq.

Ltac lia' := unfold is_true in *; lia.

(******************************************************************************)

Require Import Problem.

Variant seq_spec : seq nat -> Type :=
| SeqNil : seq_spec [::]
| SeqApp s s' : seq_spec (s ++ [:: 0] ++ s')
| SeqSucc x s : seq_spec (S x :: map S s).

Lemma seqP s : seq_spec s.
Proof.
elim: s => [| x s IH]; first by apply: SeqNil.
case: x => [| x]; first by apply: (SeqApp [::]).
case: s / IH => [| s s' | y s].
- by apply: (SeqSucc x [::]).
- by apply: (SeqApp (S x :: s) s').
- by apply: (SeqSucc x (y :: s)).
Qed.

Lemma compute2_cons_cons h1 h2 t :
  compute2 (h1 :: h2 :: t) = h1 - h2 + compute2 (h2 :: t).
Proof. rewrite /=; lia'. Qed.

Lemma compute2_app s s' :
  compute2 (s ++ [:: 0] ++ s') = compute2 s + compute2 s'.
Proof.
elim: s => [| h1 t].
  by case: s'.
case: t => [_ | h2 t IH].
  by rewrite [_ ++ _ ++ _]/= compute2_cons_cons /=; congr (_ + _); [lia' | case: s'].
by rewrite [_ ++ _ ++ _]/= !compute2_cons_cons IH; lia'.
Qed.

Lemma compute2_succ h t :
  compute2 (map S (h :: t)) = S (compute2 (h :: t)).
Proof.
elim: t h => // h' t IH h.
by rewrite [map _ _]/= !compute2_cons_cons IH; lia'.
Qed.

Lemma sumn_succ s :
  sumn (map S s) = sumn s + size s.
Proof. by elim: s => //= x s ->; lia'. Qed.

Theorem solution: task.
Proof.
unfold task.
move=> s.
have [x] := ubnP (size s + sumn s).
elim: x => // x IH in s *.
case: s / (seqP s) => [_ | s s' ine | y s ine].
- exact: c1_nil.
- rewrite !size_cat !sumn_cat /= in ine.
  by rewrite compute2_app; apply: c1_app; apply: IH; lia'.
- rewrite /= size_map sumn_succ in ine.
  by rewrite compute2_succ; apply: c1_succ; apply: IH; rewrite /=; lia'.
Qed.

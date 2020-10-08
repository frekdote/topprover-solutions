Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat.
Require Import Problem.

Lemma complete_induction (P : nat -> Prop) :
  (forall n, ((forall m, m < n -> P m) -> P n)) ->
  forall n, P n.
Proof.
  move=> H.
  have H': forall n m, m < n -> P m.
  { elim => // n IHn m.
    rewrite ltnS leq_eqVlt.
    by move=> /orP[/eqP->|]; auto.
  }
  move=> n.
  apply: H' (ltnSn _).
Qed.

Lemma compute2E h1 h2 l :
  compute2 (h1 :: h2 :: l) = h1 - Nat.min h1 h2 + compute2 (h2 :: l).
Proof. by []. Qed.

Lemma compute2_zero l1 l2 :
  compute2 (l1 ++ [:: 0] ++ l2) =
  compute2 l1 + compute2 l2.
Proof.
  elim: l1 => [| h t]; [| case: t => [| h' t']].
  - by case: l2.
  - by rewrite /= Nat.min_0_r minusE subn0; case: l2.
  - move=> IH. rewrite !compute2E IH. ring.
Qed.

Lemma compute2_S l :
  ~~ nilp l ->
  compute2 [ seq x.+1 | x <- l ] =
  (compute2 l).+1.
Proof.
  elim: l => // h t; case t => // h' t' IH _.
  rewrite [map _ _]/= 2!compute2E.
  rewrite -Nat.succ_min_distr subSS.
  rewrite IH //. ring.
Qed.

Lemma lem l :
  l = [::] \/
  (exists l1 l2, l = l1 ++ [:: 0] ++ l2) \/
  (exists h t, l = [ seq x.+1 | x <- h :: t ]).
Proof.
  elim: l => [| h t H]; auto.
  right.
  case: (h =P 0) => [->|].
  - by left; exists [::], t.
  - move/Nat.neq_0_r => [h' Hh'].
    case: H => [-> | [[l1 [l2 H12]] | [h'' [t' Ht']]]].
    + by right; exists h', [::]; rewrite Hh'.
    + by left; exists (h :: l1), l2; rewrite H12.
    + by right; exists h', (h'' :: t'); rewrite Hh' Ht'.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  move=> s.
  remember (size s + sumn s) as si.
  generalize dependent s.
  elim/complete_induction: si.
  move=> n IH s Heqsi.
  case: (lem s); [| case].
  - by move->; constructor.
  - move=> [l1 [l2 H12]].
    rewrite H12 compute2_zero.
    constructor.
    + apply (IH (size l1 + sumn l1)); auto.
      rewrite Heqsi H12.
      rewrite -addSn leq_add //.
      * rewrite size_cat /= addnS ltnS leq_addr //.
      * rewrite !sumn_cat leq_addr //.
    + apply (IH (size l2 + sumn l2)); auto.
      rewrite Heqsi H12.
      rewrite -addSn leq_add //.
      * rewrite size_cat /= addnS ltnS leq_addl //.
      * rewrite !sumn_cat leq_addl //.
  - move=> [h [t Hht]].
    rewrite Hht compute2_S; auto.
    constructor.
    apply (IH (size (h :: t) + sumn (h :: t))); auto.
    rewrite Heqsi Hht.
    rewrite -addnS leq_add //.
    * by rewrite size_map.
    * rewrite /= addSn ltnS leq_add2l.
      elim t => // h' t' IHt'.
      rewrite /= addSn.
      apply leqW.
      rewrite leq_add2l //.
Qed.

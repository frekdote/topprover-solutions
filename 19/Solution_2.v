Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import List PeanoNat.

Lemma list_in_mem x s :
  list_in s x = (x \in s).
Proof.
by elim: s => //= y s ->. (* Nat.eqb = eqn *)
Qed.

Lemma unique_undup s :
  unique s = undup s.
Proof. by elim: s => //= x s ->; rewrite list_in_mem. Qed.

Lemma count_occ_count_mem x s :
  count_occ Nat.eq_dec s x = count_mem x s.
Proof.
by elim: s => //= y s ->; case: eqP; case: Nat.eq_dec.
Qed.

Theorem solution: task.
Proof.
unfold task.
move=> s x.
suff : count_mem x (undup s) = (x \in s).
  by rewrite unique_undup list_in_mem count_occ_count_mem => -> ->.
by rewrite (count_uniq_mem _ (undup_uniq _)) mem_undup.
Qed.

Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma list_in_mem x s :
  list_in s x = (x \in s).
Proof.
by elim: s => //= y s ->. (* Nat.eqb = eqn *)
Qed.

Lemma unique_undup s :
  unique s = undup s.
Proof. by elim: s => //= x s ->; rewrite list_in_mem. Qed.

Theorem solution: task.
Proof.
unfold task.
move=> s.
rewrite !unique_undup.
by apply: undup_id (undup_uniq _).
Qed.

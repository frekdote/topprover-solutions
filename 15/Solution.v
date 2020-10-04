Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Sorting.Permutation.
Require Import Problem.

Lemma permutation_count (a : nat) s s' :
  Permutation s s' -> count_mem a s = count_mem a s'.
Proof.
  elim => //=.
  - by move=> x t t' _ ->.
  - move=> x y t.
    rewrite !addnA. f_equal. apply addnC.
  - by move=> s1 s2 s3 _ -> _ ->.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  move=> a b s.
  move/(permutation_count b).
  case: (a =P b) => //= /eqP/negPf->.
  Print n_Sn.
  rewrite eq_refl add0n add1n.
    by move/n_Sn.
Qed.

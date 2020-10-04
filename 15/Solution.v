Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import Sorting.Permutation.

Lemma Permutation_count (a : nat) s s' :
  Permutation s s' -> count_mem a s = count_mem a s'.
Proof.
elim: s s' / => //= [x s s' _ ? | x y s | s s' s'' _ + _].
- by congr (_ + _).
- by rewrite addnCA.
- by apply: etrans.
Qed.

Theorem solution: task.
Proof.
unfold task.
move=> a b s /(Permutation_count b); rewrite /= eq_refl.
by case: (a =P b) => //= _ /addIn.
Qed.

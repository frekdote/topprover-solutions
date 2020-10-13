Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  move=> x y. split.
  - move=> Hxy z Hyz.
    apply: R_trans Hxy Hyz.
  - move=> H.
    apply: (H _) (R_refl _).
Qed.

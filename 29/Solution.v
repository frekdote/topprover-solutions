Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
unfold task.
move=> x y; split.
  by move=> + z; exact: R_trans.
by move/(_ y (R_refl y)).
Qed.

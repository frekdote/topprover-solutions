Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
unfold task.
move=> f; split.
  by move=> H m n ? /H.
by move=> H m n; case: (m =P n) => // /H.
Qed.

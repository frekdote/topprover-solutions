Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
unfold task.
by move=> [] [] []; auto.
Qed.

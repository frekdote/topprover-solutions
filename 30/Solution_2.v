Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
unfold task; rewrite multE.
elim/ltn_ind => -[| [| n IH]] //=.
by rewrite (IH n) // !mulnS.
Qed.

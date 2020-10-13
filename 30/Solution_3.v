Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma double_S n : double n.+1 = 2 + double n.
Proof. by elim: n => // ? ->. Qed.

Theorem solution: task.
Proof.
unfold task; rewrite multE.
by elim => // n IH; rewrite double_S IH mulnS.
Qed.

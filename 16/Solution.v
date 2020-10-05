Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma gcd_n_1 n :
    gcd n 1 1.
Proof.
elim: n => [| n' IHn'].
  by apply/gcd_swap/gcd_O.
by rewrite -add1n; apply: gcd_step.
Qed.

Theorem solution: task.
Proof.
unfold task.
move=> n.
by apply/gcd_swap/gcd_step/gcd_swap/gcd_n_1.
Qed.

Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
unfold task; rewrite multE => n.
have /(_ n) [] // : forall n, double n = 2 * n /\ double n.+1 = 2 * n.+1.
by elim => //= m [-> ->]; rewrite !mulnS.
Qed.

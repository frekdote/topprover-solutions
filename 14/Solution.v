Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma mod2_odd n :
  mod2 n = odd n.
Proof.
by elim: n => //= n ->; case (odd n).
Qed.

Theorem solution: task.
Proof.
unfold task.
move=> n.
by rewrite multE !mod2_odd odd_mul andbb.
Qed.

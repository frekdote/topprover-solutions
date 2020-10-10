Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import Arith.

Lemma lem1 m :
  bin (2 * m + 1) -> bin (S (2 * m)).
Proof. by rewrite Nat.add_1_r. Qed.

Lemma lem2 m :
  bin (2 * S m) -> bin (S (2 * m + 1)).
Proof. by rewrite Nat.mul_succ_r Nat.add_succ_r. Qed.

Fixpoint bin_succ n (H : bin n) : bin (S n) :=
  match H with
    bin_epsilon => bin_1 0 bin_epsilon
  | bin_0 m H' => lem1 (bin_1 m H')
  | bin_1 m H' => lem2 (bin_0 (S m) (bin_succ H'))
  end.

Theorem solution: task.
Proof.
unfold task.
elim => [| n /bin_succ //].
exact: bin_epsilon.
Qed.

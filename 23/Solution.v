Require Import Problem.
Require Import Omega.

Lemma lem1 m :
  bin (2 * m + 1) -> bin (S (2 * m)).
Proof. rewrite Nat.add_1_r; auto. Qed.

Lemma lem2 m :
  bin (2 * S m) -> bin (S (2 * m + 1)).
Proof. replace (2 * S m) with (S (2 * m + 1)) by omega; auto. Qed.

Fixpoint bin_succ n (H : bin n) : bin (S n) :=
  match H with
    bin_epsilon => bin_1 0 bin_epsilon
  | bin_0 m H' => lem1 _ (bin_1 m H')
  | bin_1 m H' => lem2 _ (bin_0 (S m) (bin_succ m H'))
  end.

Theorem solution: task.
Proof.
  unfold task.
  intros n.
  induction n as [| n' IH].
  - constructor.
  - exact (bin_succ _ IH).
Qed.

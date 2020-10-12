Require Import Problem.
Require Import Nat.

Lemma lem : forall (f : nat -> nat) n m x,
    iter (m + n) f x = iter m f (iter n f x).
Proof.
  intros f n m x.
  induction m as [| m IHm]; auto.
  simpl.
  f_equal.
  auto.
Qed.

Lemma lem2 : forall (f : nat -> nat) n m x,
    iter (m * n) f x = iter m (iter n f) x.
Proof.
  intros f n m x.
  induction m as [| m IHm]; auto.
  simpl.
  rewrite lem.
  f_equal.
  auto.
Qed.

Lemma lem3 : forall (f g : nat -> nat),
    (forall n, f n = g n) ->
    forall n x, iter n f x = iter n g x.
Proof.
  intros f g H n x.
  induction n as [| n IHn]; auto.
  simpl.
  rewrite H, IHn.
  reflexivity.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros f n.
  induction n as [| n IHn]; intros m x; auto.
  simpl.
  rewrite lem2.
  rewrite lem3 with (f := iter (m ^ n) f) (g := iter n (iter m) f); auto.
Qed.

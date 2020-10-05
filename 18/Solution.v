Require Import Problem.
Require Import List.
Import ListNotations.

Lemma list_in_unique : forall l x,
    list_in (unique l) x = list_in l x.
Proof.
  intros l. induction l as [| y l IHl]; auto.
  intros x.
  simpl. destruct (list_in l y) eqn:E.
  - rewrite IHl. destruct (Nat.eqb x y) eqn:E'; auto.
    apply PeanoNat.Nat.eqb_eq in E'. subst. auto.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros l. induction l as [| x l IHl]; auto.
  simpl. destruct (list_in l x) eqn:E; auto.
  simpl. rewrite list_in_unique, E. f_equal. auto.
Qed.

Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Definition binom_1 m n :=
  match m, n with
    _, 0 => 1
  | 0, _ => 0
  | m'.+1, _ => binom m' n
  end.

Definition binom_2 m n :=
  match m, n with
    _, 0 => 0
  | 0, _ => 0
  | m'.+1, n'.+1 => binom m' n'
  end.

Lemma binom_binom_1_binom_2 n k :
  binom n k = binom_1 n k + binom_2 n k.
Proof. by case: n => [| n']; case: k => [| k']. Qed.

Fixpoint binom_1_sum n k :=
  match k with 0 => 1 | S k' => binom_1 n k + binom_1_sum n k' end.

Fixpoint binom_2_sum n k :=
  match k with 0 => 0 | S k' => binom_2 n k + binom_2_sum n k' end.

Lemma binom_sum_binom_1_sum_binom_2_sum n k:
  binom_sum n k = binom_1_sum n k + binom_2_sum n k.
Proof.
  elim: k => //= k IH.
  rewrite plusE binom_binom_1_binom_2 IH. ring.
Qed.

Lemma binom_1_sum_binom_sum n k :
  binom_1_sum n.+1 k = binom_sum n k.
Proof. by elim: k => //= k' ->. Qed.

Lemma binom_2_sum_binom_sum n k :
  binom_2_sum n.+1 k.+1 = binom_sum n k.
Proof.
  elim: k => //= [| k' ->] //=.
  case: n; rewrite ?addn0 //.
Qed.

Lemma binom_n_gt_n : forall n m,
  m > n -> binom n m = 0.
Proof.
  elim => [| n' IH].
  - by case.
  - case => //= m' H.
    rewrite !IH; auto.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  elim => // n' IH.
  rewrite binom_sum_binom_1_sum_binom_2_sum binom_1_sum_binom_sum binom_2_sum_binom_sum /=.
  rewrite binom_n_gt_n /=; auto.
  rewrite IH plusE addn0 //.
Qed.

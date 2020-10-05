Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import List PeanoNat.
Import ListNotations.

Lemma list_in_unique : forall l x,
    list_in (unique l) x = list_in l x.
Proof.
  elim => //= h t IHt x.
  case: (Nat.eqb_spec _ _).
  - move=> ->.
    case E : (list_in t h).
    + rewrite IHt //.
    + rewrite /= Nat.eqb_refl //.
  - move=> /Nat.eqb_neq NE.
    case: (list_in t h); rewrite /= ?NE //.
Qed.

Lemma not_list_in_count_occ_0 l x :
    list_in l x = false -> count_occ Nat.eq_dec l x = 0.
Proof.
  elim l => //= h t IHt.
  case: (Nat.eq_dec _ _).
  - move=> ->.
    rewrite Nat.eqb_refl //.
  - rewrite Nat.eqb_sym.
    move=> /Nat.eqb_neq -> //.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  elim => //= h t IHt n.
  case: (Nat.eqb_spec n h).
  - move=> <- _.
    case E : (list_in t n).
    + apply: IHt E.
    + rewrite /=.
      case: (Nat.eq_dec n n) => // _.
      rewrite not_list_in_count_occ_0 ?list_in_unique //.
  - move=> /Nat.neq_sym NE.
    case: (list_in t h) => /=;
    [| case: (Nat.eq_dec h n); try easy; intro ];
    apply IHt.
Qed.

Require Import Problem.
Require Import List PeanoNat.
Import ListNotations.

Lemma list_in_unique : forall l x,
    list_in (unique l) x = list_in l x.
Proof.
  intros l. induction l as [| h t IHt]; auto.
  intros x. simpl. destruct (list_in t h) eqn:E.
  - destruct (Nat.eqb_spec x h); subst; auto.
    rewrite <- E; auto.
  - simpl. rewrite IHt. auto.
Qed.

Lemma not_list_in_count_occ : forall x l,
    list_in l x = false -> count_occ Nat.eq_dec l x = 0.
Proof.
  intros x l. induction l as [| h t IHt]; auto.
  simpl. destruct (Nat.eq_dec _ _) as [| NE].
  - subst. now rewrite Nat.eqb_refl.
  - apply not_eq_sym in NE.
    apply Nat.eqb_neq in NE.
    now rewrite NE.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros l n H. induction l as [| m l IHl]; try easy.
  simpl. destruct (list_in l m) eqn:E.
  - simpl in H. destruct (n =? m) eqn:E'; auto.
    apply Nat.eqb_eq in E'. subst. auto.
  - simpl. destruct (Nat.eq_dec m n) as [| NE].
    + subst. rewrite <- list_in_unique in E. rewrite (not_list_in_count_occ _ _ E). reflexivity.
    + apply not_eq_sym, Nat.eqb_neq in NE. simpl in H. rewrite NE in H. auto.
Qed.

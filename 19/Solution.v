Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import List PeanoNat.

Theorem solution: task.
Proof.
unfold task.
move=> l n.
suff : count_occ Nat.eq_dec (unique l) n = list_in l n.
  by move => -> ->.
elim: l => //= m l IH.
case: (boolP (list_in l m)) => [m_in_l | m_notin_l] /=; rewrite IH -[_ =? _]/(n == m) eq_sym.
  by case: eqP => // <-; rewrite m_in_l.
by case: eqP; case: Nat.eq_dec => // <- _; rewrite (negbTE m_notin_l).
Qed.

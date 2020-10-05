Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import List PeanoNat.
Import ListNotations.

Lemma count_occ_cat l1 l2 n :
    count_occ Nat.eq_dec (l1 ++ l2) n =
    count_occ Nat.eq_dec l1 n + count_occ Nat.eq_dec l2 n.
Proof.
by elim: l1 => //= x l1 IH; case: Nat.eq_dec => // _; rewrite addSn; congr S.
Qed.

Theorem solution: task.
Proof.
unfold task.
elim => // x l IH n.
by rewrite -{1}[_ :: _]/([x] ++ l) [rev _]/= !count_occ_cat addnC; congr (_ + _).
Qed.

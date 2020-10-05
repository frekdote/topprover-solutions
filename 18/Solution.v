Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma list_in_unique l x :
  list_in (unique l) x = list_in l x.
Proof.
elim: l => //= h t IH.
case: (boolP (list_in t h)); rewrite /= IH //.
by rewrite -[Nat.eqb _ _]/(x == h); case: eqP => // ->.
Qed.

Theorem solution: task.
Proof.
unfold task.
elim => //= x l IH; case: (boolP (list_in l x)) => //=.
by rewrite list_in_unique => /negbTE ->; congr (_ :: _).
Qed.

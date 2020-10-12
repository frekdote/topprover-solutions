Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Theorem solution: task.
Proof.
unfold task.
move=> cont.
have : forall a b c : Two, a = b \/ b = c \/ c = a by move=> [] [] []; auto.
by rewrite cont => /(_ C31 C32 C33) [| [|]].
Qed.

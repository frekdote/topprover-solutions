Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

(*
  Prove task1 or task2. You can choose either one you like.
 *)

Lemma solution2: task2.
Proof.
unfold task2.
move=> P Q; split.
  by case => HNP HNQ; case => [/HNP | /HNQ].
by move=> H; split => [HP | HQ]; apply: H; [left | right].
Qed.

Theorem solution: task1 \/ task2.
Proof.
  (* left. apply solution1. *)
  right. apply solution2.
Qed.

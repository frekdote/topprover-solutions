Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma powE n m : Nat.pow n m = expn n m.
Proof. by elim: m => //= m ->; rewrite expnS. Qed.

Lemma iterE T n :
  @Nat.iter n T = @iter T n. (* [Nat.iter] coincides with [iter] except the order of arguments *)
Proof. by []. Qed.

Lemma iter_mul T n m f (x : T) :
  iter (n * m) f x = iter n (iter m f) x.
Proof. by elim: n => // n IH; rewrite mulSn iter_add IH. Qed.

Theorem solution: task.
Proof.
unfold task.
move=> f n m; rewrite !iterE powE; elim: n => //= n IH x.
by rewrite expnS iter_mul; apply: eq_iter.
Qed.

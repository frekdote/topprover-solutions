Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import ZArith Znumtheory Lia.

Open Scope Z.

Theorem solution: task.
Proof.
  unfold task.
  move=> p [Hp1 Hp2] a Ha k1 Hk1 k2 Hk2 H12.
  move: (Zis_gcd_bezout _ _ _ (Hp2 a Ha)) => [u v Huv].
  have: k1 mod p = k2 mod p.
  { rewrite -(Z.mul_1_r k1) -(Z.mul_1_r k2).
    rewrite -Huv.
    rewrite !Z.mul_add_distr_l.
    rewrite ![_ * (v * p)]Z.mul_assoc !Z.mod_add; try omega.
    rewrite [u * a]Z.mul_comm.
    rewrite !Z.mul_assoc.
    rewrite ![(_ * _ * _) mod _]Z.mul_mod; try omega.
    rewrite H12 //.
  }
  rewrite !Zmod_small //.
Qed.

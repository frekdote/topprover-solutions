Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import ZArith Znumtheory Lia.

Open Scope Z_scope.

Theorem solution: task.
Proof.
unfold task.
move=> p [Hp1 Hp2] a Ha k1 Hk1 k2 Hk2 Emul.
have Hp1' : p <> 0 by lia.
suff : k1 mod p = k2 mod p by rewrite !Z.mod_small.
have [u v Euv] := Zis_gcd_bezout _ _ _ (Hp2 a Ha).
have /(f_equal (fun x => k1 * x mod p)) := Euv.
have /(f_equal (fun x => k2 * x mod p)) := Euv.
rewrite !Z.mul_add_distr_l !Z.mul_assoc !Z.mod_add // ![_ * _ * a]Z.mul_shuffle0 ![(_ * _ * u) mod _]Z.mul_mod // !Z.mul_1_r Emul.
by lia.
Qed.

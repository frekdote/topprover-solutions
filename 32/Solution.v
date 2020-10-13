Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem Omega.

(* HINT *)
Scheme le_max_ind := Induction for le Sort Prop.

(* HINT 2: Eqdep_dec.UIP_refl_nat *)

(* BEWARE: do not use Program.Equality, which imports extra axioms from JMeq *)

Theorem solution: task.
Proof.
  unfold task.
  induction p using le_max_ind.
  - move=> q.
    rewrite (_ : le_n m = @eq_rect _ _ (fun x => m <= x) (le_n m) _ (eq_refl m)) //.
    move: {2 4 6 10}m q (eq_refl m).
    destruct q.
    + move=> e. rewrite (Eqdep_dec.UIP_refl_nat _ e) //.
    + move=> ?. subst. omega.
  - move=> q.
    rewrite (_ : le_S m m0 p = @eq_rect _ _ (fun x => m <= x) (le_S m m0 p) _ (eq_refl (S m0))) //.
    move: {1 3 4 6}(S m0) q (eq_refl _).
    destruct q.
    + move=> ?. subst. omega.
    + move=> e. inversion e. subst.
      rewrite (Eqdep_dec.UIP_refl_nat _ e).
      congr le_S; auto.
Qed.

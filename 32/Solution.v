Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.
Require Import Lia.

(* HINT *)
Scheme le_max_ind := Induction for le Sort Prop.

(* HINT 2: Eqdep_dec.UIP_refl_nat *)

(* BEWARE: do not use Program.Equality, which imports extra axioms from JMeq *)

Theorem solution: task.
Proof.
unfold task.
move=> m n.
elim/le_max_ind: n / => [q | n' p' IH q].
  rewrite -[le_n m]/(eq_rect m (fun x => m <= x) (le_n m) m (eq_refl m)).
  (* Set Printing All. *)
  (* move: q eq_refl. *)
  move: {2 4 6 10}m q eq_refl => l q.
  case: l / q => [e |]; last by lia.
  by rewrite (Eqdep_dec.UIP_refl_nat _ e).
rewrite -[le_S m n' p']/(eq_rect (S n') (fun x => m <= x) (le_S m n' p') (S n') eq_refl).
(* Set Printing All. *)
(* move: q eq_refl. *)
move: {1 3 4 6}(S n') q eq_refl => l q.
case: l / q => [| l' q' e]; first by lia.
have [En'l'] := e; rewrite En'l' in p' IH q' e *.
by rewrite (Eqdep_dec.UIP_refl_nat _ e); congr le_S.
Qed.

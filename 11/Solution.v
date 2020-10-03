Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Fixpoint f (l : seq nat) :=
  match l with
    [::] => 0
  | x :: l' => count (fun y => x > y) l' + f l'
  end.

Lemma swap_once_count l l' p :
  swap_once l l' ->
  count p l = count p l'.
Proof.
  elim.
  - by move=> h1 h2 t /=; ring.
  - by move=> h t1 t2 _ /= ->.
Qed.

Lemma NoDup_swap_once_odd l l' :
  List.NoDup l -> swap_once l l' -> odd (f l') = odd ((f l).+1).
Proof.
  move=> H H'.
  elim: H' H.
  - move=> h1 h2 t H.
    inversion H; subst.
    move: (Decidable.not_or _ _ H2) => [/eqP H22 _] /=.
    case: ltngtP H22 => //= _ _;
      rewrite -addnE ?negbK;
      [ congr (~~ odd _) | congr (odd _) ];
      ring.
  - move=> h t1 t2 H IH H' /=.
    inversion H'; subst.
    rewrite !odd_add (swap_once_count _ H) IH ?addbN //=.
Qed.

Lemma swap_once_In l l' :
  swap_once l l' -> forall x, List.In x l <-> List.In x l'.
Proof.
  elim.
  - move=> h1 h2 t x /=; intuition.
  - move=> h t1 t2 _ IH x /=; rewrite IH //.
Qed.

Lemma NoDup_swap_once_NoDup l l' :
  List.NoDup l -> swap_once l l' -> List.NoDup l'.
Proof.
  move=> H H'.
  elim: H' H.
  - move=> h1 h2 t H.
    inversion H; subst.
    move: (Decidable.not_or _ _ H2) => [H21 H22].
    apply not_eq_sym in H21.
    inversion H3; subst.
    constructor.
    + by move=> [].
    + by constructor.
  - move=> h t1 t2 H IH H'.
    inversion H'; subst.
    constructor.
    + move=> cont.
      apply (swap_once_In H) in cont.
      intuition.
    + intuition.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  move=> l1 l2 H H' /(f_equal (fun l => odd (f l)))cont.
  induction H'.
  - move: cont (NoDup_swap_once_odd H H0) => /= ->.
      by case: (odd (f l2)).
  - move: (NoDup_swap_once_NoDup H H0) => H''.
    move: (NoDup_swap_once_NoDup H'' H1) => H'''.
    move: (NoDup_swap_once_odd H'' H1) (NoDup_swap_once_odd H H0) IHH' => -> /= ->.
    rewrite negbK.
    intuition.
Qed.

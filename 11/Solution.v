Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Problem.

Lemma memP (T : eqType) (x : T) (s : seq T) :
  reflect (List.In x s) (x \in s).
Proof.
apply: (iffP idP).
  by elim: s => //= y s IH; rewrite in_cons; case/orP => [/eqP | /IH]; auto.
by elim: s => //= y s IH; rewrite in_cons; case => [-> | /IH ->]; rewrite ?eq_refl ?orbT.
Qed.

Lemma uniqP' (T : eqType) (s : seq T) :
  reflect (List.NoDup s) (uniq s).
Proof.
apply: (iffP idP).
  by elim: s => /= [_ | x s IH /andP [/memP ? /IH ?]]; constructor.
by elim: s / => //= x s /memP -> _ ->.
Qed.

Lemma perm_count (T : eqType) (s s' : seq T) (a : pred T) :
  perm_eq s s' -> count a s = count a s'.
Proof.
by move=> ?; rewrite -!size_filter; apply/perm_size/perm_filter.
Qed.

Lemma swap_once_perm s s' :
  swap_once s s' -> perm_eq s s'.
Proof.
elim: s s' / => [x y s | x s s' _ IH]; last by rewrite perm_cons.
by apply/permP => ? /=; ring.
Qed.

Fixpoint f (s : seq nat) :=
  match s with
    [::] => 0
  | x :: s' => count (fun y => x > y) s' + f s'
  end.

Lemma swap_once_odd_f s s' :
  swap_once s s' -> uniq s -> odd (f s') = ~~ odd (f s).
Proof.
elim: s s' / => /= [x y s | x s s' so IH /andP [_ /IH E]].
  rewrite in_cons; case/and3P => /norP [+ _] _ _.
  case: ltngtP => //= _ _.
    by congr (~~ (odd _)); rewrite add0n addnCA.
  by rewrite negbK add0n addnCA.
have /perm_count -> := swap_once_perm so.
by rewrite !odd_add E addbN.
Qed.

Lemma is_odd_permutation_odd_f s s' :
  is_odd_permutation s s' -> uniq s -> odd (f s') = ~~ odd (f s).
Proof.
elim: s s' / => [| s1 s2 s3 s4 so12 so23 _ IH uniq_s1]; first by exact: swap_once_odd_f.
have /perm_uniq/esym := swap_once_perm so12; rewrite uniq_s1 => uniq_s2.
have /perm_uniq/esym := swap_once_perm so23; rewrite uniq_s2 => uniq_s3.
by rewrite (IH uniq_s3) (swap_once_odd_f so23 uniq_s2) (swap_once_odd_f so12 uniq_s1) negbK.
Qed.

Theorem solution: task.
Proof.
unfold task.
move=> s s' /uniqP' un op /(f_equal (fun s => odd (f s))).
rewrite (is_odd_permutation_odd_f op un).
by case: (odd _).
Qed.

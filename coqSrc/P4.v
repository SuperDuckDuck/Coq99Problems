Require Import List.
Import ListNotations.

Fixpoint len {X : Type} (ls : list X) : nat :=
match ls with 
| [] => 0
| x::xs => S (len xs)
end.

Theorem emptyL {X : Type} : len ([] : list X) = 0.
Proof.
  auto.
Qed.

Theorem lenStep {X : Type} : forall (xs ys : list X) x, 
  len (xs ++ x :: ys) = S (len (xs ++ ys)).
Proof.
  intro.
  induction xs; intros.
  + reflexivity.
  + simpl. apply eq_S.
    apply IHxs.
Qed.

Theorem lenListStep {X : Type} : forall (xs zs ys : list X),
  len (xs ++ zs ++ ys)  = len zs + len (xs ++ ys).
Proof.
  intro.
  induction xs; intro.
  + induction zs; intro.
    - reflexivity.
    - simpl. apply eq_S.
      simpl in IHzs. apply IHzs.
  + intro. simpl. rewrite PeanoNat.Nat.add_succ_r.
    apply eq_S. apply IHxs.
Qed.


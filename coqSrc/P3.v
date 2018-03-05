Require Import List.
Import ListNotations.
Require Import Nat.



Fixpoint myNth {X : Type} (n : nat) (ls : list X) : option X := 
match ls with
| [] => None
| x::xs => match n with 
           | 0 => None 
           | (S m) => if eqb m 0 then Some x else myNth m xs
           end
end.

Theorem emptyList {X : Type} (n : nat) : myNth n ([] : list X) = None.
Proof.
  destruct n; auto.
Qed.

Theorem zeroNth {X : Type} (ls : list X) : myNth 0 ls = None.
Proof.
  destruct ls; auto.
Qed.

Theorem leLtN {X : Type} (ls : list X) (n : nat) : 
  length ls < n -> myNth n ls = None.
Proof.
  generalize dependent n.
  induction ls; intros.
  + destruct n; auto.
  + destruct n.
    - inversion H.
    - destruct n.
      * inversion H.
        inversion H1.
      * assert (myNth (S (S n)) (a::ls) = myNth (S n) ls).
        { clear; reflexivity. }
        rewrite H0. clear H0.
        apply IHls.
        simpl in H.
        intuition.
Qed.

Theorem myNthCorrect {X : Type}: forall (ls xs ys : list X) n x, 
  length (xs ++ [x]) = n -> ls = xs ++ x :: ys -> myNth n ls = Some x.
Proof.
  intro.
  induction ls; intros.
  + destruct xs; inversion H0.
  + destruct n.
    - destruct xs.
      * inversion H.
      * inversion H.
    - destruct n. 
      * destruct xs.
        ++ inversion H0.
           auto.
        ++ destruct xs.
           -- inversion H.
           -- inversion H.
      * destruct xs.
        ++ inversion H.
        ++ inversion H0.
           assert (myNth (S (S n)) (x0 :: xs ++ x :: ys) = myNth (S n) (xs ++ x :: ys)).
           { clear. reflexivity. }
           rewrite H1. clear H1. rewrite <- H3.
           eapply IHls.
           -- simpl in H.
              apply eq_add_S in H.
              exact H.
           -- exact H3.
Qed.


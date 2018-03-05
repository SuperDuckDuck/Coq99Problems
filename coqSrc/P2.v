Require Import List.
Import ListNotations.

Fixpoint penU {X : Type} (ls: list X): option X := 
match ls with 
| [] => None
| [x;y] => Some x
| x::xs => penU xs
end.

Theorem penUNone {X : Type} : forall (ls : list X), 
  length ls < 2 -> penU ls = None.
Proof.
  destruct ls.
  auto.
  destruct ls.
  auto.
  intro.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem penUCorrect {X : Type} : forall (ls : list X) x y, penU (ls ++ [x;y]) = Some x.
Proof.
  intros.
  induction ls.
  + reflexivity.
  + destruct ls.
    - auto.
    - destruct ls.
      * auto.
      * assert (penU ((a :: x0 :: x1 :: ls) ++ [x; y]) =  penU ((x0 :: x1 :: ls) ++ [x; y])).
        { reflexivity. }
        rewrite H.
        exact IHls.
Qed.
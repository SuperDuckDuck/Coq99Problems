Require Import List.
Import ListNotations.
Require Import Omega.


Fixpoint reverse {X : Type} (ls : list X) : list X := 
match ls with 
| [] => []
| x::xs => reverse xs ++ [x]
end.

Inductive predReverse {X : Type} : list X -> list X -> Prop :=
| base : predReverse [] []
| step : forall xs ys x, predReverse xs ys -> predReverse (x::xs) (ys ++ [x]).

Theorem reversePred {X : Type}: forall (xs : list X), predReverse xs (reverse xs).
Proof.
  intros.
  induction xs.
  + apply base.
  + simpl. apply step.
    exact IHxs.
Qed.


Theorem reverseCorrect {X : Type} : forall (ls : list X) n d, 
  let len := length ls - 1 in   n <= len -> 
  nth n ls d = nth (len - n) (reverse ls) d.
Proof.
  intro.
  induction ls; intros.
  + unfold len. destruct n; auto.
  + destruct n.
    - simpl. inversion H.
      * simpl. unfold len in H1.
        inversion H1. destruct ls.
        ++ reflexivity.
        ++ inversion H2.
      * rewrite H0.
        unfold len. simpl. 
        assert (forall ( xs ls : list X) (x:X) de, length xs = length ls -> nth (length ls) (xs ++ [x]) de = x).
        { clear. induction xs; intros.
          + inversion H. destruct ls.
            - reflexivity.
            - inversion H1.
          + rewrite <- H. simpl. apply IHxs.
            reflexivity.
        }
        repeat rewrite <- Coq.Arith.Minus.minus_n_O.
        rewrite H2.
        ++ reflexivity.
        ++ assert (length (reverse ls) = length ls).
           { clear. induction ls.
              + reflexivity.
              + simpl. rewrite app_length.
                rewrite IHls. simpl. rewrite PeanoNat.Nat.add_comm.
                simpl. reflexivity.
           }
           rewrite H3.
           reflexivity.
    - simpl. 
      unfold len in *.
      simpl length. simpl.
      rewrite <- (Coq.Arith.Minus.minus_n_O (length ls)).
      assert ((length ls - S n) = (length ls - 1 - n)).
      { clear. assert (S n = 1 + n). reflexivity.
        rewrite H. rewrite PeanoNat.Nat.sub_add_distr. reflexivity.
      }
      rewrite H0.
      rewrite IHls.
      * assert (forall m (xs : list X) (x : X)de , 
        m < length xs -> xs <> [] -> 
        nth m (xs ++ [x]) de = nth m xs de).
        {
          clear. induction m; intros.
          + simpl. destruct xs.
            - exfalso. apply H0. reflexivity.
            - reflexivity. 
          + destruct xs.
            - simpl. destruct m; auto.
            - simpl. apply IHm. simpl in H. omega.
              intro. rewrite H1 in H. simpl in H. inversion H.
              inversion H3.
        }
        simpl in H.
        rewrite <- Coq.Arith.Minus.minus_n_O in H.
        assert (length ls -1 -n < length (reverse ls)).
        {
          induction ls.
          + inversion H.
          + simpl. rewrite app_length. simpl. 
            assert (forall (xs: list X), length (reverse xs) = length xs).
            { 
              clear.
              induction xs.
              + reflexivity.
              + simpl. rewrite app_length. simpl. rewrite IHxs. omega.
            }
            rewrite H2. omega.
        }
        rewrite H1. 
        ++ reflexivity.
        ++ exact H2.
        ++ intro. destruct ls.
           -- inversion H. 
           -- inversion H3. 
              assert (forall (xs : list X) x, xs ++ [x] <> []).
              {
                clear. induction xs; intros; intro; inversion H.
              }
              specialize (H4 (reverse ls) x).
              contradiction.
      * simpl length in H.
        omega.
Qed.
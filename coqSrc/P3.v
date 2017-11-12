Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Omega.
Require Import Coq.Arith.PeanoNat.



Fixpoint myNth {X : Type} (n : nat) (ls : list X) : option X := 
match ls with
| [] => None
| x::xs => if leb n 1 then Some x else myNth (pred n) xs
end.


Theorem myNth1 {X : Type} : 
  forall (n : nat)(ls : list X), length ls < n -> myNth n ls = None.
Proof.
  intros.
  generalize dependent n.
  induction ls.
  + reflexivity.
  + intro. 
    destruct n. 
    - intro. inversion H.
    - intro. destruct n.
      * simpl in H. omega. 
      * simpl. apply IHls.
        simpl in H. apply lt_S_n in H. exact H.
Qed.
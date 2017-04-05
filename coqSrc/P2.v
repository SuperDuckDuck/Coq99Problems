(*Problem 2: find the penultimate element of a list*)

Require Import List.
Import ListNotations.
Open Scope list_scope.




Fixpoint lastButOne {A : Type} (ls : list A)(default : A) : A := 
match ls with 
  | [ ] => default 
  | [x;_] => x
  | _::xs => lastButOne xs default 
end.
 
(*proof for empty lists*)
Lemma  lastButOneNil {A : Type} :  forall (x : A), lastButOne [] x = x.
Proof.
reflexivity.
Qed.
(*proof that if the length of the input list is smaller than two, the default *)
Lemma lenSmallerTwo : forall (ls : list A) c

(*proof that nonempty lists do in fact return the last but one element of a list*)
Lemma lastButOneNonEmpty {A : Type} : forall (ls : list A)(x : A)(y : A)(z : A), lastButOne (ls ++ [x] ++ [y] ) z = x.


Fixpoint lastButOneOption  {A : Type}(ls : list A) : A := 
match ls with 
  | [x ;_] => Some x
  | 
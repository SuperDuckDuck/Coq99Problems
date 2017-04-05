Require Import List.
Import ListNotations.
Open Scope list_scope.



Variable A : Type.


Fixpoint lastWithDefault {A : Type} (ls :list A)(default : A) : A :=
match ls with 
  | [x] => x
  | x::xs => lastWithDefault xs default 
  | [] => default
end.



Lemma defaultWhenEmpty: forall (ls : list A) (x : A) , ls = nil -> lastWithDefault ls x = x.
Proof.
intros.
induction ls.
simpl.
reflexivity.
rewrite -> H .
reflexivity.
Qed.

Lemma lastWithDefaultOneElement : forall (a : A)(b : A), lastWithDefault [a] b = a.
Proof.
intros.
reflexivity.
Qed.

Lemma lastWithDefaultNonEmpty : forall (a : A)(b : A)(ls : list A), lastWithDefault  (ls ++[a]) b  = a. 
Proof.
intros.
induction ls.
reflexivity.
simpl.
destruct ls .
reflexivity.
exact IHls.
Qed.






(*version using the option type (Maybe in Haskell)*)
Fixpoint lastOption {A : Type} (ls : list A) :option A :=
match ls with 
  | [x] => Some x
  | (x::xs) => lastOption xs 
  | [] => None 
end.


(*proof that lastOptions returns None in case it is called with an empty list*)
Lemma nilLastNone :  forall (ls : list A)(a : A) , ls = nil -> lastOption ls = None.
Proof.
intros.
rewrite -> H .
reflexivity.
Qed.


(*proof that with an empty list lastOption never returns anything but None*)
Lemma notNilLast : ~ (lastOption ([] : list A) <> None).
Proof.
intros.
unfold not.
intro.
apply H.
apply eq_refl.
Qed.

(*proof that a list containing exact one element returns exactly this element when passed to lastOption*)
Lemma tmp a : lastOption ( [a] : list A) = Some a.
Proof.
reflexivity.
Qed.


(*proof that if lastOption is called with an nonemtpy list that the last element in this list will be returned wrapped in the Some constructor*)
Lemma appLastSome : forall (ls : list A)(a : A), lastOption (ls ++ [a]) = Some a.
Proof.
intros.
induction ls.
reflexivity.
simpl.
destruct (ls ++ [a]).
simpl in IHls.
discriminate IHls.
apply IHls.
Qed.


(*proof that if a list is nonempty , that lastOption returns _Some a_*)
Lemma lastSomeType : forall (ls : list A)(a : A) ,  (fun val1  => match val1  with | Some _ => true | None => false end)(lastOption (a:: ls)) = true.
Proof.
intros.
induction (ls).
reflexivity.
rewrite <- IHl at 1.
simpl lastOption.
destruct l.
reflexivity.
reflexivity.
Qed.

(*proof that lastOption returns the right type ... more of a exploration proof to see what is possible*)
Lemma rightType : forall (ls : list A) , ((fun (val : option A) => true)) (lastOption ls) = true.
Proof.
reflexivity.
Qed. 
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Bool.

Variable A : Type.


Fixpoint lastWithDefault {A : Type} (ls :list A)(default : A) : A :=
match ls with 
  | [x] => x
  | x::xs => lastWithDefault xs default 
  | [] => default
end.

(*useful commands*)
Print lastWithDefault. (*prints definition of a function / type*)
Print true.
Print find.  (*does also work for library functions*)

Locate lastWithDefault. (*shows where the function/type is defined*)
Locate true.
Locate find.


(*shows type of an expression*)
Check lastWithDefault.
Check find.
Check true.



(*evaluates an expression. Can be used for testing*)
Eval compute in lastWithDefault [1;2;3;4] 0.
(*Eval compute in find (beq 5) [1;2;3;4] .*) 


(*tests*)

Check lastWithDefault.

Eval compute in lastWithDefault [1;2;3;4] 0.
Eval compute in lastWithDefault [1] 0.
Eval compute in lastWithDefault [] 0.


(*proofs*)
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

(*a more general and nonsencical version of the previous proof*)
Lemma lastWithDefaultIn : forall (a : A)(b : A)(ls : list A) , lastWithDefault ls b = a /\ a <> b -> In a ls .
Proof.
intros.
induction ls.
destruct H.
simpl lastWithDefault in H.
simpl.
apply H0.
apply eq_sym.
exact H.
destruct ls.
intros.
simpl.
left.
simpl in H.
destruct H.
exact H.
intros.
simpl In.
Show Proof.
destruct H.
right.
apply IHls.
split.
simpl in H.
simpl.
exact H.
assumption.
Qed.



(*work in progress 
Lemma lastWithDefaultNotIn : forall (a : A)(ls : list A) , lastWithDefault ls a = a -> ~ In a ls .
Proof.
intros.
unfold not.
intro.
induction ls.
simpl in H0.
contradiction.
apply IHls.
destruct ls.


Lemma nonEmptyListFindTrue : forall (a : A) ( b : A) (ls : list A) , 
*)


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
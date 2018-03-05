Require Import List.
Import ListNotations.
Require Import EquivDec.

Definition pal {X : Type} `{EqDec X} (ls : list X) : bool :=
let len := length ls in 
let half := Nat.div len 2 in 
let firstHalf := firstn half ls in 

Require Import Bool.
Notation " ! b " := (negb b) (at level 0). 

(*1*)
(*a*)
Goal forall x y, !(x && y) || (!x && y) || (!x || !y) = !x || !y.
Proof.
  intros. destruct x,y ; simpl ; reflexivity.
Qed.

(*b*)
Goal forall x y z, !(!x && y && !z) && !(x && y && z) && (x && !y && !z) = x && !y && !z.
Proof.
  intros. destruct x,y,z ; simpl ; reflexivity.
Qed.
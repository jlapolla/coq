Module ProgramState.

Require Export Coq.Lists.List.

Set Implicit Arguments.

Section ListOperations.

Variable A : Type.

Fixpoint replace (n : nat) (a : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a' l' =>
    match n with
    | O => cons a l'
    | S n' => cons a' (replace n' a l')
    end
  end.

(** TODO: Fill in Lemmas *)

Fixpoint repeat (x : A) (n : nat) : list A :=
  match n with
  | O => nil
  | S k => cons x (repeat x k)
  end.

(** TODO: Fill in Lemmas *)

End ListOperations.

Section Stacks.

Variable A : Type.

Definition stack_frame := list A.

Definition stack := list stack_frame.

Definition push := cons.

Definition pop := tl.

Function assign (n : nat) (a : A) (sk : stack) : stack :=
  match sk with
  | nil => nil
  | cons sf' sk' => cons (replace n a sf') sk'
  end.

(** TODO: Fill in Lemmas *)

End Stacks.

Section Stores.

Variable A : Type.

Definition store := list A.

Definition alloc (a : A) (sr : store) :=
  app sr (cons a nil).

(** TODO: Fill in Lemmas *)

End Stores.

End ProgramState.

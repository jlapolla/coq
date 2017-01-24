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

Function sk_write (n : nat) (a : A) (sk : stack) : stack :=
  match sk with
  | nil => nil
  | cons sf' sk' => cons (replace n a sf') sk'
  end.

Function sk_read (n : nat) (sk : stack) (default : A) : A :=
  match sk with
  | nil => default
  | cons sf' sk' => nth n sf' default
  end.

(** TODO: Fill in Lemmas *)

End Stacks.

Section Stores.

Variable A : Type.

Definition store := list A.

Definition alloc (a : A) (sr : store) :=
  app sr (cons a nil).

Definition sr_write := replace.

Definition sr_read := nth.

(** TODO: Fill in Lemmas *)

End Stores.

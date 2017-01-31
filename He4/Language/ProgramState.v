Require Export Coq.Lists.List.
Require Export He4.Lists.List.

Set Implicit Arguments.

Section Stacks.

Variable A : Type.

Definition stack_frame := list A.

Definition stack := list stack_frame.

Definition push := cons.

Definition pop := tl.

Definition sk_write_hd (n : nat) (a : A) (sk : stack) : stack :=
  push (replace n a (hd nil sk)) (pop sk).

Definition sk_read_hd (n : nat) (sk : stack) (default : A) : A :=
  nth n (hd nil sk) default.

Definition sk_resize_hd (n : nat) (sk : stack) (default : A) : stack :=
  push (resize n (hd nil sk) default) (pop sk).

(** TODO: Fill in Lemmas *)

End Stacks.

Section Stores.

Variable A : Type.

Definition store := list A.

Definition sr_alloc (a : A) (sr : store) :=
  app sr (cons a nil).

Definition sr_write := replace.

Definition sr_read := nth.

(** TODO: Fill in Lemmas *)

End Stores.

Require Import He4.Language.Term.
Require Export Coq.Lists.List.
Require Export He4.Lists.List.

Set Implicit Arguments.

Section Stacks.

Definition stack_frame := list tm.

Definition stack := list stack_frame.

Definition push := cons.

Definition pop := tl.

Definition sk_write_hd (n : nat) (a : tm) (sk : stack) : stack :=
  push (replace n a (hd nil sk)) (pop sk).

Definition sk_read_hd (n : nat) (sk : stack) : tm :=
  nth n (hd nil sk) tvoid.

Definition sk_resize_hd (n : nat) (sk : stack) : stack :=
  push (resize n (hd nil sk) tvoid) (pop sk).

(** TODO: Fill in Lemmas *)

End Stacks.

Section Stores.

Definition store := list tm.

Definition sr_alloc (a : tm) (sr : store) :=
  app sr (cons a nil).

Definition sr_write := replace.

Definition sr_read (n : nat) (sr : store) : tm := nth n sr tvoid.

(** TODO: Fill in Lemmas *)

End Stores.

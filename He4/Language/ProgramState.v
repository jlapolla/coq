Require Import He4.Language.Term.
Require Export Coq.Lists.List.
Require Export He4.Lists.List.

Set Implicit Arguments.

Section Stacks.

Definition stack_frame : Type := list tm.

Definition stack : Type := list stack_frame.

Definition push : stack_frame -> stack -> stack := @cons stack_frame.

Definition pop : stack -> stack := @tl stack_frame.

Definition sk_write_hd (n : nat) (a : tm) (sk : stack) : stack :=
  push (replace n a (hd nil sk)) (pop sk).

Definition sk_read_hd (n : nat) (sk : stack) : tm :=
  nth n (hd nil sk) tvoid.

Definition sk_resize_hd (n : nat) (sk : stack) : stack :=
  push (resize n (hd nil sk) tvoid) (pop sk).

Definition empty_stack : stack := push nil nil.

(** TODO: Fill in Lemmas *)

End Stacks.

Section Stores.

Definition store : Type := list tm.

Definition sr_alloc (a : tm) (sr : store) : store :=
  app sr (cons a nil).

Definition sr_write : nat -> tm -> store -> store := @replace tm.

Definition sr_read (n : nat) (sr : store) : tm := nth n sr tvoid.

Definition empty_store : store := sr_alloc tvoid nil. (* Position 0 represents the "null" reference *)

(** TODO: Fill in Lemmas *)

End Stores.


Require Import He4.Language.Term.
Require Import Coq.Lists.List.
Require Import He4.Lists.List.

(** * Types *)

Definition stack_frame : Type := list tm.
Definition stack : Type := list stack_frame.

(** * Functions *)

Definition push (sf : stack_frame) (sk : stack) : stack := cons sf sk.

Definition pop (sk : stack) : stack := tl sk.

Definition write_hd (n : nat) (a : tm) (sk : stack) : stack :=
  push (replace n a (hd nil sk)) (pop sk).

Definition read_hd (n : nat) (sk : stack) : tm :=
  nth n (hd nil sk) tvoid.

Definition resize_hd (n : nat) (sk : stack) : stack :=
  push (resize n (hd nil sk) tvoid) (pop sk).

(** TODO: Lemmas *)

(** Functions unfold with [simpl]. *)

Arguments push sf sk /.
Arguments pop sk /.
Arguments write_hd n a sk /.
Arguments read_hd n sk /.
Arguments resize_hd n sk /.

(** * Constants *)

Definition empty_stack : stack := push nil nil.


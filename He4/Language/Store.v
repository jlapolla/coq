Require Import He4.Language.Term.
Require Import Coq.Lists.List.
Require Import He4.Lists.List.

(** * Types *)

Definition store : Type := list tm.

(** * Functions *)

Definition alloc (a : tm) (sr : store) : store :=
  app sr (cons a nil).

Definition write (n : nat) (t : tm) (sr : store) : store := replace n t sr.

Definition read (n : nat) (sr : store) : tm := nth n sr tvoid.

(** TODO: Lemmas *)

(** Functions unfold with [simpl]. *)

Arguments alloc a sr /.
Arguments write n t sr /.
Arguments read n sr /.

(** * Constants

    Position [0] in a [store] represents the "null reference". *)

Definition empty_store : store := alloc tvoid nil.


Require Import He4.Language.Term.
Require Import Coq.Lists.List.
Require Import He4.Lists.List.

(** * Types *)

Definition store : Type := list tm.

(** * Functions *)

Definition sr_alloc (a : tm) (sr : store) : store :=
  app sr (cons a nil).

Definition sr_write (n : nat) (t : tm) (sr : store) : store := replace n t sr.

Definition sr_read (n : nat) (sr : store) : tm := nth n sr tvoid.

(** TODO: Lemmas *)

(** Functions unfold with [simpl]. *)

Arguments sr_alloc a sr /.
Arguments sr_write n t sr /.
Arguments sr_read n sr /.

(** * Constants

    Position [0] in a [store] represents the "null reference". *)

Definition empty_store : store := sr_alloc tvoid nil.


Require Import Software.Language.Syntax.
Require Import Software.Lib.Lists.List.

(** * Types *)

Definition store : Type := list term.

(** * Functions *)

Definition alloc (a : term) (sr : store) : store :=
  app sr (cons a nil).

Definition write (n : nat) (t : term) (sr : store) : store := replace n t sr.

Definition read (n : nat) (sr : store) : term := nth n sr tvoid.

(** TODO: Lemmas *)

(** Functions unfold with [simpl]. *)

Arguments alloc a sr /.
Arguments write n t sr /.
Arguments read n sr /.

(** * Constants

    Position [0] in a [store] represents the "null reference". *)

Definition init_store : store := alloc tvoid nil.


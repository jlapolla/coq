Require Import He4.Language.Term.
Require Import Coq.Lists.List.
Require Import He4.Lists.List.

(** * Types *)

Definition stack_frame : Type := list tm.
Definition stack : Type := list stack_frame.
Definition store : Type := list tm.
Definition state : Type := prod stack store.

(** * Functions *)
(** ** State accessors *)

Definition get_stack (st : state) : stack := fst st.
Definition get_store (st : state) : store := snd st.
Definition set_stack (sk : stack) (st : state) : state := pair sk (get_store st).
Definition set_store (sr : store) (st : state) : state := pair (get_stack st) sr.

(** ** Stack functions *)

Definition push (sf : stack_frame) (sk : stack) : stack := cons sf sk.

Definition push_sf (sf : stack_frame) (st : state) : state :=
  set_stack (push sf (get_stack st)) st.

Definition pop (sk : stack) : stack := tl sk.

Definition pop_sf (st : state) : state :=
  set_stack (pop (get_stack st)) st.

Definition sk_write_hd (n : nat) (a : tm) (sk : stack) : stack :=
  push (replace n a (hd nil sk)) (pop sk).

Definition write_sk_hd (n : nat) (a : tm) (st : state) : state :=
  set_stack (sk_write_hd n a (get_stack st)) st.

Definition sk_read_hd (n : nat) (sk : stack) : tm :=
  nth n (hd nil sk) tvoid.

Definition read_sk_hd (n : nat) (st : state) : tm :=
  sk_read_hd n (get_stack st).

Definition sk_resize_hd (n : nat) (sk : stack) : stack :=
  push (resize n (hd nil sk) tvoid) (pop sk).

Definition resize_sk_hd (n : nat) (st : state) : state :=
  set_stack (sk_resize_hd n (get_stack st)) st.

(** TODO: Lemmas *)

(** ** Store functions *)

Definition sr_alloc (a : tm) (sr : store) : store :=
  app sr (cons a nil).

Definition alloc_sr (a : tm) (st : state) : state :=
  set_store (sr_alloc a (get_store st)) st.

Definition sr_write (n : nat) (t : tm) (sr : store) : store := replace n t sr.

Definition write_sr (n : nat) (t : tm) (st : state) : state :=
  set_store (sr_write n t (get_store st)) st.

Definition sr_read (n : nat) (sr : store) : tm := nth n sr tvoid.

Definition read_sr (n : nat) (st : state) : tm :=
  sr_read n (get_store st).

(** TODO: Lemmas *)

(** ** Function unfolding

    [Arguments] statement with [/] tells tactic [simpl] to unfold these
    functions when arguments before the [/] are provided [[1]].

    [[1]] #<a href="https://coq.inria.fr/distrib/8.4pl4/refman/Reference-Manual010.html##sec395">
           https://coq.inria.fr/distrib/8.4pl4/refman/Reference-Manual010.html##sec395</a># *)

Arguments get_stack st /.
Arguments get_store st /.
Arguments set_stack sk st /.
Arguments set_store sr st /.
Arguments push sf sk /.
Arguments push_sf sf st /.
Arguments pop sk /.
Arguments pop_sf st /.
Arguments sk_write_hd n a sk /.
Arguments write_sk_hd n a st /.
Arguments sk_read_hd n sk /.
Arguments read_sk_hd n st /.
Arguments sk_resize_hd n sk /.
Arguments resize_sk_hd n st /.
Arguments sr_alloc a sr /.
Arguments alloc_sr a st /.
Arguments sr_write n t sr /.
Arguments write_sr n t st /.
Arguments sr_read n sr /.
Arguments read_sr n st /.

(** * Constants

    Position [0] in a [store] represents the "null reference". *)

Definition empty_stack : stack := push nil nil.
Definition empty_store : store := sr_alloc tvoid nil.
Definition empty_state : state := pair empty_stack empty_store.


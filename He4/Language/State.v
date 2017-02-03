Require Import He4.Language.CallStack.
Require Import He4.Language.Term.
Require Import He4.Language.Stack.
Require Import He4.Language.Store.

(** * Types *)

Inductive state : Type :=
  | Cstate: stack -> call_stack -> store -> state.

(** * Functions *)
(** ** State accessors *)

Definition get_stack (st : state) : stack :=
  match st with
  | Cstate sk _ _ => sk
  end.

Definition get_call_stack (st : state) : call_stack :=
  match st with
  | Cstate _ csk _ => csk
  end.

Definition get_store (st : state) : store :=
  match st with
  | Cstate _ _ sr => sr
  end.

Definition set_stack (sk : stack) (st : state) : state :=
  match st with
  | Cstate _ csk sr => Cstate sk csk sr
  end.

Definition set_call_stack (csk : call_stack) (st : state) : state :=
  match st with
  | Cstate sk _ sr => Cstate sk csk sr
  end.

Definition set_store (sr : store) (st : state) : state :=
  match st with
  | Cstate sk csk _ => Cstate sk csk sr
  end.

(** ** Stack functions *)

Definition push_sf (sf : stack_frame) (st : state) : state :=
  set_stack (push sf (get_stack st)) st.

Definition pop_sf (st : state) : state :=
  set_stack (pop (get_stack st)) st.

Definition write_sk_hd (n : nat) (a : tm) (st : state) : state :=
  set_stack (write_hd n a (get_stack st)) st.

Definition read_sk_hd (n : nat) (st : state) : tm :=
  read_hd n (get_stack st).

Definition resize_sk_hd (n : nat) (st : state) : state :=
  set_stack (resize_hd n (get_stack st)) st.

(** ** Store functions *)

Definition alloc_sr (a : tm) (st : state) : state :=
  set_store (alloc a (get_store st)) st.

Definition write_sr (n : nat) (t : tm) (st : state) : state :=
  set_store (write n t (get_store st)) st.

Definition read_sr (n : nat) (st : state) : tm :=
  read n (get_store st).

(** ** Function unfolding

    [Arguments] statement with [/] tells tactic [simpl] to unfold these
    functions when arguments before the [/] are provided [[1]].

    [[1]] #<a href="https://coq.inria.fr/distrib/8.4pl4/refman/Reference-Manual010.html##sec395">
           https://coq.inria.fr/distrib/8.4pl4/refman/Reference-Manual010.html##sec395</a># *)

Arguments get_stack st /.
Arguments get_call_stack st /.
Arguments get_store st /.
Arguments set_stack sk st /.
Arguments set_call_stack csk st /.
Arguments set_store sr st /.
Arguments push_sf sf st /.
Arguments pop_sf st /.
Arguments write_sk_hd n a st /.
Arguments read_sk_hd n st /.
Arguments resize_sk_hd n st /.
Arguments alloc_sr a st /.
Arguments write_sr n t st /.
Arguments read_sr n st /.

(** * Constants *)

Definition init_state : state := Cstate init_stack init_call_stack init_store.


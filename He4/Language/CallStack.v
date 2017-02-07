Require Import Coq.Lists.List.

(** * Types *)

Definition call_frame : Type := list (option nat).
Definition call_stack : Type := list call_frame.

(** * Functions *)

Definition push (cf : call_frame) (csk : call_stack) : call_stack := cons cf csk.

Definition pop (csk : call_stack) : call_stack := tl csk.

(** Functions unfold with [simpl]. *)

Arguments push cf csk /.
Arguments pop csk /.

(** * Constants *)

Definition init_call_stack : call_stack := push nil nil.


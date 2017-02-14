Require Import Software.Lib.Lists.List.

(** * Types *)

Definition ref_pass_stack_frame : Type := list (option nat).
Definition ref_pass_stack : Type := list ref_pass_stack_frame.

(** * Functions *)

Definition push (rpsf : ref_pass_stack_frame) (rpsk : ref_pass_stack) : ref_pass_stack := cons rpsf rpsk.

Definition pop (rpsk : ref_pass_stack) : ref_pass_stack := tl rpsk.

(** Functions unfold with [simpl]. *)

Arguments push rpsf rpsk /.
Arguments pop rpsk /.

(** * Constants *)

Definition init_ref_pass_stack : ref_pass_stack := push nil nil.


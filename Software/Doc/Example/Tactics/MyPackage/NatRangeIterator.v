Require Import Software.Language.DynamicBinding.
Require Import Software.Language.State.
Require Import Software.Language.Syntax.
Require Import App.Lib.NatRangeIterator.Execution.

Ltac reduce_function class fn rule :=
  match goal with
  | |- exec_step (Cexec_state (texec fn) ?st) _ =>
    match eval cbv in (called_on_classb class st) with
    | true => eapply rule
    | _ =>
      match eval cbv in (read_sk_hd 0 st) with
      | tref ?r =>
        match goal with
        | H: List.nth r ?sr tvoid = tcl class _ |- exec_step (Cexec_state (texec fn) (Cstate _ _ ?sr)) _ => eapply rule
        | H: read_sr r (Cstate _ _ ?sr) = tcl class _ |- exec_step (Cexec_state (texec fn) (Cstate _ _ ?sr)) _ => eapply rule
        end
      end
    end
  end.

Ltac reduce_static_function fn rule :=
  match goal with
  | |- exec_step (Cexec_state (texec fn) _) _ => eapply rule
  end.

Open Scope string_scope.

Ltac reduce_exec_step :=
     reduce_static_function "NatRangeIterator_make" STexec_NatRangeIterator_make
  || reduce_function "NatRangeIterator" "get_at_start" STexec_get_at_start
  || reduce_function "NatRangeIterator" "get_count" STexec_get_count
  || reduce_function "NatRangeIterator" "get_first" STexec_get_first
  || reduce_function "NatRangeIterator" "set_at_start" STexec_set_at_start
  || reduce_function "NatRangeIterator" "set_count" STexec_set_count
  || reduce_function "NatRangeIterator" "set_first" STexec_set_first
  || reduce_function "NatRangeIterator" "off" STexec_off
  || reduce_function "NatRangeIterator" "after" STexec_after
  || reduce_function "NatRangeIterator" "forth" STexec_forth
  || reduce_function "NatRangeIterator" "item" STexec_item
.

Close Scope string_scope.


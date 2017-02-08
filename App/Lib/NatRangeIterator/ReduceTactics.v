Require Import He4.Language.DynamicBinding.
Require Import He4.Language.Term.
Require Import App.Lib.NatRangeIterator.Step.

Ltac reduce_NatRangeIterator_make :=
  match goal with
  | |- step (pair (texec "NatRangeIterator_make") _) _ => eapply STexec_NatRangeIterator_make
  end.

Ltac reduce_get_at_start :=
  match goal with
  | |- step (pair (texec "get_at_start") _) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator") with
    | true => eapply STexec_get_at_start
    end
  end.

Ltac reduce_step :=
     reduce_NatRangeIterator_make
  || reduce_get_at_start
.


Require Import He4.Language.DynamicBinding.
Require Import He4.Language.Term.
Require Import App.Lib.NatRangeIterator.Step.

Ltac reduce_NatRangeIterator_make :=
  match goal with
  | |- step (pair (texec "NatRangeIterator_make") _) _ => eapply STexec_NatRangeIterator_make
  end.

Ltac reduce_get_at_start :=
  match goal with
  | |- step (pair (texec "get_at_start") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_get_at_start
    end
  end.

Ltac reduce_get_count :=
  match goal with
  | |- step (pair (texec "get_count") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_get_count
    end
  end.

Ltac reduce_get_first :=
  match goal with
  | |- step (pair (texec "get_first") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_get_first
    end
  end.

Ltac reduce_set_at_start :=
  match goal with
  | |- step (pair (texec "set_at_start") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_set_at_start
    end
  end.

Ltac reduce_set_count :=
  match goal with
  | |- step (pair (texec "set_count") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_set_count
    end
  end.

Ltac reduce_set_first :=
  match goal with
  | |- step (pair (texec "set_first") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_set_first
    end
  end.

Ltac reduce_off :=
  match goal with
  | |- step (pair (texec "off") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_off
    end
  end.

Ltac reduce_after :=
  match goal with
  | |- step (pair (texec "after") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_after
    end
  end.

Ltac reduce_forth :=
  match goal with
  | |- step (pair (texec "forth") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_forth
    end
  end.

Ltac reduce_item :=
  match goal with
  | |- step (pair (texec "item") ?st) _ =>
    match eval cbv in (called_on_classb "NatRangeIterator" st) with
    | true => eapply STexec_item
    end
  end.

Ltac reduce_step :=
     reduce_NatRangeIterator_make
  || reduce_get_at_start
  || reduce_get_count
  || reduce_get_first
  || reduce_set_at_start
  || reduce_set_count
  || reduce_set_first
  || reduce_off
  || reduce_after
  || reduce_forth
  || reduce_item
.


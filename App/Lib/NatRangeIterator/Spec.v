Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.

Section Specs.

Variable step : step_relation.

Definition wf (st : state) : Prop :=
     called_on_class "NatRangeIterator" st
  /\ (exists b, multi step (pair (texec "get_at_start") st) (pair (tbool b) st))
  /\ (exists n, multi step (pair (texec "get_count") st) (pair (tnat n) st))
  /\ (exists n, multi step (pair (texec "get_first") st) (pair (tnat n) st)).

End Specs.


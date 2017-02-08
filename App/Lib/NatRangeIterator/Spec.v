Require Import He4.Language.State.
Require Import He4.Language.StepProp.

Section Specs.

Variable step : step_relation.

Definition wf (st : state) : Prop :=
  True.

End Specs.


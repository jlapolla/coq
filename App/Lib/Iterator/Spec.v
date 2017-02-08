Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.

Section Specs.

Variable step : step_relation.
Variable wf : state -> Prop.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Definition off__no_side_effects : Prop :=
  forall st,
  wf st ->
    exists b st',
       texec "off" / st ==>* tbool b / st'
    /\ states_eq_wrt step (texec "off") st st'
    /\ states_eq_wrt step (texec "after") st st'
    /\ states_eq_wrt step (texec "item") st st'.

End Specs.


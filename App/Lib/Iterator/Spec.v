Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Import ObjectOrientedNotations.

Section Specs.
Open Scope oo_scope.

Variable step : step_relation.
Variable wf : tm -> state -> Prop.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Definition off__no_side_effects : Prop :=
  forall x st,
  wf x st ->
    exists b st',
       (x # "off"|()|) / st ==>* tbool b / st'
    /\ states_eq_wrt step (x # "off"|()|) st st'
    /\ states_eq_wrt step (x # "after"|()|) st st'
    /\ states_eq_wrt step (x # "item"|()|) st st'.

End Specs.


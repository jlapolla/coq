Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.Value.
Import ObjectOrientedNotations.

Section Specs.
Open Scope oo_scope.

Variable step : step_relation.
Variable wf : tm -> state -> Prop.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition deterministic_off : Prop :=
  forall x st,
  wf x st ->
  term_deterministic step (x # "off"|()|) st.

Definition terminates_off : Prop :=
  forall x st,
  wf x st ->
  term_terminates step (x # "off"|()|) st.

Definition preserves_wf_off : Prop :=
  forall x v st st',
  wf x st ->
  value v ->
  (x # "off"|()|) / st ==>* v / st' ->
  wf x st'.

Definition returns_tbool_off : Prop :=
  forall x v st st',
  wf x st ->
  value v ->
  (x # "off"|()|) / st ==>* v / st' ->
  exists b, v = (tbool b).

Definition perserves_off_off : Prop :=
  forall x st,
  wf x st ->
  term_preserves_term step (x # "off"|()|) st (x # "off"|()|).

Definition perserves_off_after : Prop :=
  forall x st,
  wf x st ->
  term_preserves_term step (x # "off"|()|) st (x # "after"|()|).

Definition perserves_off_item : Prop :=
  forall x st,
  wf x st ->
  term_preserves_term step (x # "off"|()|) st (x # "item"|()|).

Definition off__no_side_effects : Prop :=
  forall x st,
  wf x st ->
    exists b st',
       (x # "off"|()|) / st ==>* tbool b / st'
    /\ states_eq_wrt step (x # "off"|()|) st st'
    /\ states_eq_wrt step (x # "after"|()|) st st'
    /\ states_eq_wrt step (x # "item"|()|) st st'.

End Specs.


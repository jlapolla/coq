Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.ExecutionProp.
Require Import He4.Language.Syntax.
Require Import He4.Language.Value.
Import ObjectOrientedNotations.

Section Specs.
Open Scope oo_scope.

Variable exec_step : exec_step_relation.
Variable wf : term -> state -> Prop.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition deterministic_off : Prop :=
  forall x st,
  wf x st ->
  term_deterministic exec_step (x # "off"|()|) st.

Definition terminates_off : Prop :=
  forall x st,
  wf x st ->
  term_terminates exec_step (x # "off"|()|) st.

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
  term_preserves_term exec_step (x # "off"|()|) st (x # "off"|()|).

Definition perserves_off_after : Prop :=
  forall x st,
  wf x st ->
  term_preserves_term exec_step (x # "off"|()|) st (x # "after"|()|).

Definition perserves_off_item : Prop :=
  forall x st,
  wf x st ->
  term_preserves_term exec_step (x # "off"|()|) st (x # "item"|()|).

Definition off__no_side_effects : Prop :=
  forall x st,
  wf x st ->
    exists b st',
       (x # "off"|()|) / st ==>* tbool b / st'
    /\ states_eq_wrt exec_step (x # "off"|()|) st st'
    /\ states_eq_wrt exec_step (x # "after"|()|) st st'
    /\ states_eq_wrt exec_step (x # "item"|()|) st st'.

End Specs.


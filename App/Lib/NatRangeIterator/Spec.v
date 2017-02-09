Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.Value.
Import ObjectOrientedNotations.

Section Specs.
Open Scope oo_scope.

Definition wf_ex (var : tm) (st : state) : Prop :=
  exists n ref at_start count first,
      var = tvar n
  /\  read_sk_hd n st = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>.

Definition wf : Prop :=
  forall var ref st at_start count first,
      read_sk_hd var st = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>.

Variable step : step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition get_at_start__returns_tbool : Prop :=
  forall v x st st',
  wf_ex x st ->
  value v ->
  (x # "get_at_start"|()|) / st ==>* v / st' ->
  exists b, v = tbool b.

Definition get_at_start__terminates : Prop :=
  forall x st,
  wf_ex x st ->
  term_terminates step (x # "get_at_start"|()|) st.

Definition get_at_start__deterministic : Prop :=
  forall x st,
  wf_ex x st ->
  term_deterministic step (x # "get_at_start"|()|) st.

Definition get_at_start__preserves_state : Prop :=
  forall x st,
  wf_ex x st ->
  term_preserves_state step (x # "get_at_start"|()|) st.

End Specs.


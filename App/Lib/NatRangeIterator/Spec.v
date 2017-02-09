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

Definition wf var ref st at_start count first : Prop :=
      read_sk_hd var st = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>.

Variable step : step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition get_at_start__behavior : Prop :=
  forall var ref st at_start count first,
  wf var ref st at_start count first ->
  ((tvar var) # "get_at_start"|()|) / st ==>* (tbool at_start) / st.

Variable get_at_start__behavior_proof : get_at_start__behavior.

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

Definition get_at_start__terminates_proof:
  forall x st,
  wf_ex x st ->
  term_terminates step (x # "get_at_start"|()|) st.
Proof.
  intros.
  unfold wf_ex in H.
  destruct H as [var [ref [at_start [count [first [Hvar [Hsk Hsr]]]]]]].
  subst x.
  assert (wf var ref st at_start count first).
  { unfold wf. split; assumption. }
  unfold term_terminates.
  exists (tbool at_start). exists st.
  intros.
  apply (get_at_start__behavior_proof var ref st at_start count first).
  assumption.
  Qed.

Definition get_at_start__deterministic : Prop :=
  forall x st,
  wf_ex x st ->
  term_deterministic step (x # "get_at_start"|()|) st.

Definition get_at_start__preserves_state : Prop :=
  forall x st,
  wf_ex x st ->
  term_preserves_state step (x # "get_at_start"|()|) st.

End Specs.


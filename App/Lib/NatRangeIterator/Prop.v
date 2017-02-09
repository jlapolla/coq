Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.Value.
Require Import App.Lib.NatRangeIterator.Spec.
Import ObjectOrientedNotations.

Section Props.
Open Scope oo_scope.

Variable step : step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Variable get_at_start__behavior_proof : get_at_start__behavior step.

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

End Props.



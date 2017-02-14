Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Syntax.
Require Import He4.Language.Value.
Require Import App.Lib.Iterator.Spec.
Require Import App.Lib.NatRangeIterator.Spec.
Import ObjectOrientedNotations.

Ltac destruct_wf_ex H var ref at_start count Hvar Hsk Hsr :=
  destruct H as [var [ref [at_start [count [first [Hvar [Hsk Hsr]]]]]]].

Section Props.
Open Scope oo_scope.

Variable exec_step : exec_step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Variable proof_get_at_start : get_at_start exec_step.

Definition terminates_get_at_start:
  forall x st,
  wf_ex x st ->
  term_terminates exec_step (x # "get_at_start"|()|) st.
Proof.
  intros.
  destruct_wf_ex H var ref at_start count Hvar Hsk Hsr.
  subst x.
  assert (wf (tvar var) var ref st at_start count first).
  { unfold wf; auto. }
  unfold term_terminates.
  exists (tbool at_start). exists st.
  intros.
  apply (proof_get_at_start (tvar var) var ref st at_start count first).
  assumption.
  Qed.

End Props.

Module IteratorVerification.

Section ConformsToIterator.
Open Scope oo_scope.

Variable exec_step : exec_step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1  /  st1  '==>'  t2  /  st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1  /  st1  '==>*'  t2  /  st2 ']'").

Variable proof_off_true : off_true exec_step.
Variable proof_off_false : off_false exec_step.
Variable proof_after_true : after_true exec_step.
Variable proof_after_false : after_false exec_step.
Variable proof_forth_at_start : forth_at_start exec_step.
Variable proof_forth : forth exec_step.
Variable proof_item : item exec_step.

Theorem deterministic_off:
  Iterator.Spec.deterministic_off exec_step wf_ex.
Proof.
  unfold deterministic_off. intros.
  destruct_wf_ex H var ref at_start count Hvar Hsk Hsr.
  subst x.
  assert (wf (tvar var) var ref st at_start count first).
  { unfold wf; auto. }
  unfold term_deterministic. intros.
  destruct count.
  (* count = 0 *)
    assert ((tvar var # "off"|()|) / st ==>* (tbool true) / st).
    { apply (proof_off_true (tvar var) var ref st at_start 0 first); [assumption | left; reflexivity]. }
  Abort.

Theorem terminates_off:
  Iterator.Spec.terminates_off exec_step wf_ex.
Proof.
  Abort.

Theorem preserves_wf_off:
  Iterator.Spec.preserves_wf_off exec_step wf_ex.
Proof.
  Abort.

Theorem returns_tbool_off:
  Iterator.Spec.returns_tbool_off exec_step wf_ex.
Proof.
  Abort.

Theorem perserves_off_off:
  Iterator.Spec.perserves_off_off exec_step wf_ex.
Proof.
  Abort.

Theorem perserves_off_after:
  Iterator.Spec.perserves_off_after exec_step wf_ex.
Proof.
  Abort.

Theorem perserves_off_item:
  Iterator.Spec.perserves_off_item exec_step wf_ex.
Proof.
  Abort.

End ConformsToIterator.

End IteratorVerification.


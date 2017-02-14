Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Syntax.
Require Import App.FeasibilityStep.
Require Import App.FeasibilityTactics.
Require Import App.Lib.Iterator.Spec.
Require Import App.Lib.NatRangeIterator.Spec.
Require Import App.Lib.NatRangeIterator.Props.
Import ObjectOrientedNotations.
Import StateNotations.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'['  t1  /  st1  '==>*'  t2  /  st2 ']'").

Ltac reduce_exec_step := Language.reduce_exec_step || NatRangeIterator.reduce_exec_step.

Ltac rewrite_nth :=
  match goal with
  | H: List.nth ?n ?sf tvoid = _ |- context [List.nth ?n ?sf tvoid] => rewrite H
  end.

Ltac reduce :=
  match goal with
  | |- multi exec_step _ _ => solve [apply Relation_Operators.rt1n_refl]
  | |- multi exec_step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [repeat reduce_exec_step | instantiate; simpl; repeat rewrite_nth; fold multi]
  end.

Open Scope oo_scope.
Open Scope state_scope.

Example ex_NatRangeIterator_make:
  exists st',
  (tnat 1) # "NatRangeIterator_make"|(tnat 2)| / init_state ==>* tref 1 / st'.
Proof.
  eapply ex_intro.
  reduce. reduce. reduce. reduce. reduce. reduce. reduce. reduce. reduce.
  reduce. reduce. reduce. reduce. reduce. reduce. reduce. reduce. reduce.
  reduce. reduce. reduce. reduce. reduce. reduce. reduce. reduce. reduce.
  reduce. reduce. reduce. reduce. reduce. reduce. reduce.
  Qed.

Close Scope state_scope.
Open Scope string_scope.

Ltac expand_wf_ex :=
  match goal with
  | H: wf_ex _ _ |- _ => destruct H as [n [ref [at_start [count [first [Hvar [Hsk Hsr]]]]]]]
  end.

Theorem off__no_side_effects:
  Iterator.Spec.off__no_side_effects exec_step NatRangeIterator.Spec.wf_ex.
Proof.
  unfold off__no_side_effects.
  intros. expand_wf_ex. subst x.
  destruct st as [sk rpsk sr] eqn:Hst.
  destruct sk; try solve [destruct n; inversion Hsk].
  simpl in Hsk, Hsr.
  destruct count.
  (* count = 0 *)
    exists true. exists st. subst st.
    repeat split.
      repeat reduce.
  Abort.

Theorem proof_get_at_start:
  Spec.get_at_start exec_step.
Proof.
  unfold get_at_start.
  unfold wf. intros.
  destruct st as [sk rpsk sr] eqn:Hst.
  destruct H as [Hvar [Hsk Hsr]].
  subst x.
  destruct sk; try solve [destruct var; inversion Hsk].
  simpl in Hsk, Hsr.
  repeat reduce.
  Qed.

Theorem terminates_get_at_start :
  forall x st,
  wf_ex x st ->
  term_terminates exec_step (x # "get_at_start"|()|) st.
Proof.
  apply (terminates_get_at_start exec_step proof_get_at_start).
  Qed.


Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import App.FeasibilityStep.
Require Import App.FeasibilityTactics.
Require Import App.Lib.Iterator.Spec.
Require Import App.Lib.NatRangeIterator.Spec.
Import ObjectOrientedNotations.
Import StateNotations.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'['  t1  /  st1  '==>*'  t2  /  st2 ']'").

Ltac reduce_step := Language.reduce_step || NatRangeIterator.reduce_step.

Ltac rewrite_nth :=
  match goal with
  | H: List.nth ?n ?sf tvoid = _ |- context [List.nth ?n ?sf tvoid] => rewrite H
  end.

Ltac reduce :=
  match goal with
  | |- multi step _ _ => solve [apply Relation_Operators.rt1n_refl]
  | |- multi step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [repeat reduce_step | instantiate; simpl; repeat rewrite_nth; fold multi]
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
  Iterator.Spec.off__no_side_effects step NatRangeIterator.Spec.wf_ex.
Proof.
  unfold off__no_side_effects.
  intros. expand_wf_ex. subst x.
  destruct st as [sk csk sr] eqn:Hst.
  destruct sk; try solve [destruct n; inversion Hsk].
  simpl in Hsk, Hsr.
  destruct count.
  (* count = 0 *)
    exists true. exists st. subst st.
    repeat split.
      repeat reduce.
  Abort.


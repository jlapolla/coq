Require Import Software.Doc.Example.Tactics.MyPackage.NatRangeIterator.
Require Import App.Lib.NatRangeIterator.Execution.
Require Import Software.Language.State.
Require Import Software.Language.Execution.
Require Import Software.Language.ExecutionProp.
Require Import Software.Language.Syntax.
Require Import Software.Language.ReduceTactics.
Import ObjectOrientedNotations.
Import StateNotations.

Section Steps.
Import StepRelationNotations.

(** I want to use stepping rules from the base [Software.Language.Execution], and extend
    them with the stepping rules from [App.Lib.NatRangeIterator.Execution]. We
    define a new [exec_step_relation] that is the union of the two
    [exec_step_relation]'s. *)

Definition exec_step : exec_step_relation := Language.Execution.exec_step \U NatRangeIterator.Execution.exec_step.

End Steps.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Open Scope oo_scope.
Open Scope state_scope.

(** Unforutnately, our [reduce] tactics apply only to a specific
    [exec_step_relation], not to our new union of [exec_step_relation]'s. To get around
    this, we destruct the union into its component [exec_step_relation]'s, then try
    the corresponding step reduction tactic for each [exec_step_relation] in turn. *)

Ltac reduce_exec_step :=
  unfold exec_step; unfold Relation_Operators.union;
     (left; progress repeat Language.ReduceTactics.reduce_exec_step)
  || (right; progress repeat NatRangeIterator.reduce_exec_step).

Ltac reduce :=
  match goal with
  | |- multi exec_step ?t ?t => apply Relation_Operators.rt1n_refl
  | |- multi exec_step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [reduce_exec_step | instantiate; simpl; fold multi]
  end.

(** This works for all of the examples from [Software.Language.Test.ReduceTactics].
    For example, here we've copied [ex_tnot] from
    [Software.Language.Test.ReduceTactics]. *)

Example ex_tnot:
  forall st,
  (!!tbool true) / st ==>* (tbool true) / st.
Proof.
  intros st. repeat reduce. Qed.

(** However, we run into trouble when we try to reduce a function defined in
    [App.Lib.NatRangeIterator.Execution]. The problem is that [STreturn_r] and
    [STreturn] say we can reduce a [treturn t] by first reducing [t] to a
    value. But notice this subtelty: [t] must be able to reduce by
    [Software.Language.Execution]!
      
    In the following example, we end up with a term [treturn (texec
    "NatRangeIterator_make")]. This is reducible in
    [App.Lib.NatRangeIterator.Execution], but it is not reducible in
    [Software.Language.Execution]. Therefore, we cannot apply [STreturn_r]. *)

Example ex_NatRangeIterator_make:
  exists st',
  (tnat 1) # "NatRangeIterator_make"|(tnat 2)| / init_state ==>* tref 1 / st'.
Proof.
  eapply ex_intro. reduce. reduce.
  Abort.

(** At first glance, it appears we can solve this problem by moving the
    [STreturn_r] rule from [Software.Language.Execution] to
    [App.Lib.NatRangeIterator.Execution]. While this will work for terms of the form
    [treturn t], it will not work for [treturn t] terms that are nested in
    another term. For example, [tseq (treturn t) tvoid] will not reduce unless we
    also move the [tseq] reduction rules into [App.Lib.NatRangeIterator.Execution]. In
    effect, we end up moving all the reduction rules into a single [exec_step_relation],
    and we no longer have a union of individual [exec_step_relation]'s. *)


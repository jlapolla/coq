Require Import App.Lib.NatRangeIterator.ReduceTactics.
Require Import App.Lib.NatRangeIterator.Step.
Require Import He4.Language.State.
Require Import He4.Language.Step.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.ReduceTactics.
Import ObjectOrientedNotations.
Import StateNotations.

Section Steps.
Import StepRelationNotations.

(** I want to use stepping rules from the base [He4.Language.Step], and extend
    them with the stepping rules from [App.Lib.NatRangeIterator.Step]. We
    define a new [step_relation] that is the union of the two
    [step_relation]'s. *)

Definition step : step_relation := Language.Step.step \U NatRangeIterator.Step.step.

End Steps.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Open Scope oo_scope.
Open Scope state_scope.

(** Unforutnately, our [reduce] tactics apply only to a specific
    [step_relation], not to our new union of [step_relation]'s. To get around
    this, we destruct the union into its component [step_relation]'s, then try
    the corresponding step reduction tactic for each [step_relation] in turn. *)

Ltac reduce_step :=
  unfold step; unfold Relation_Operators.union;
     (left; progress repeat Language.ReduceTactics.reduce_step)
  || (right; progress repeat NatRangeIterator.ReduceTactics.reduce_step).

Ltac reduce :=
  match goal with
  | |- multi step ?t ?t => apply Relation_Operators.rt1n_refl
  | |- multi step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [reduce_step | instantiate; simpl; fold multi]
  end.

(** This works for all of the examples from [He4.Language.Test.ReduceTactics].
    For example, here we've copied [ex_tnot] from
    [He4.Language.Test.ReduceTactics]. *)

Example ex_tnot:
  forall st,
  (!!tbool true) / st ==>* (tbool true) / st.
Proof.
  intros st. repeat reduce. Qed.

(** However, we run into trouble when we try to reduce a function defined in
    [App.Lib.NatRangeIterator.Step]. The problem is that [STreturn_r] and
    [STreturn] say we can reduce a [treturn t] by first reducing [t] to a
    value. But notice this subtelty: [t] must be able to reduce by
    [He4.Language.Step]!
      
    In the following example, we end up with a term [treturn (texec
    "NatRangeIterator_make")]. This is reducible in
    [App.Lib.NatRangeIterator.Step], but it is not reducible in
    [He4.Language.Step]. Therefore, we cannot apply [STreturn_r]. *)

Example ex_NatRangeIterator_make:
  exists st',
  (tnat 1) # "NatRangeIterator_make"|(tnat 2)| / init_state ==>* tref 1 / st'.
Proof.
  eapply ex_intro. reduce. reduce.
  Abort.

(** At first glance, it appears we can solve this problem by moving the
    [STreturn_r] rule from [He4.Language.Step] to
    [App.Lib.NatRangeIterator.Step]. While this will work for terms of the form
    [treturn t], it will not work for [treturn t] terms that are nested in
    another term. For example, [tseq (treturn t) tvoid] will not reduce unless we
    also move the [tseq] reduction rules into [App.Lib.NatRangeIterator.Step]. In
    effect, we end up moving all the reduction rules into a single [step_relation],
    and we no longer have a union of individual [step_relation]'s. *)


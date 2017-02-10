Require Import App.Lib.NatRangeIterator.Verify.Sys1.Step.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.Value.

Section StepProps.

Lemma value_irreducible_step:
  value_irreducible step.
Proof with auto.
  intros t Hval.
  induction Hval;
  try solve [intros t' st st' Hcontra; inversion Hcontra].
  intros t' st st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval1 in H0. inversion H0.
  apply IHHval2 in H5. inversion H5.
  intros t' st st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval in H0. inversion H0.
  Qed.

Ltac value_step_impossible :=
  match goal with
  | H: value ?t, H0: step (pair ?t ?st) (pair ?t' ?st') |- _ =>
    solve [destruct (value_irreducible_step t H t' st st'); assumption]
  end.

Ltac step_impossible :=
  match goal with
  | H: step _ _ |- _ =>
    solve [inversion H]
  end.

Ltac step_inductive :=
  match goal with
  | H: forall z, step ?x z -> z = ?y, H0: step ?x ?a |- _ = _ =>
    solve [apply H in H0; inversion H0; auto]
  end.

Ltac rewrite_invert :=
  match goal with
  | H: ?x = ?y, H0: ?x = ?z |- _ = _ =>
    solve [rewrite H in H0; inversion H0; reflexivity]
  end.

Ltac equality_contradiction :=
  match goal with
  | H: ?x = ?x -> False |- _ =>
    solve [exfalso; apply H; reflexivity]
  end.

Lemma deterministic_step:
  deterministic step.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [value_step_impossible];
  try solve [auto];
  try solve [step_inductive];
  try solve [rewrite_invert];
  try solve [equality_contradiction];
  try solve [step_impossible].
  Qed.

Lemma deterministic_multi_step:
  deterministic_multi step.
Proof.
  unfold deterministic_multi.
  intros. inversion H0; inversion H2.
    (* t = v1 = v2 /\ st = st1 = st2 *)
    subst v1 v2 st1 st2.
    split; reflexivity.
    (* t = v1 /\ st = st1 *)
    subst v1 st1. destruct y.
    value_step_impossible.
    (* t = v2 /\ st = st2 *)
    subst v2 st2. destruct y.
    value_step_impossible.
    (* no nice equalities *)
    subst z z0. assert (step (t, st) y0). { assumption. }
    apply deterministic_step in H3. apply H3 in H6. clear H3.
    subst y0. destruct y.
  Abort.

End StepProps.


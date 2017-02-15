Require Import Software.Language.Execution.
Require Import Software.Language.ExecutionProp.
Require Import Software.Language.Syntax.
Require Import Software.Language.State.
Require Import Software.Language.Value.

Section Verification.

Lemma value_irreducible__exec_step:
  value_irreducible exec_step.
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

Ltac value_exec_step_impossible :=
  match goal with
  | H: value ?t, H0: exec_step (Cexec_state ?t ?st) (Cexec_state ?t' ?st') |- _ =>
    solve [destruct (value_irreducible__exec_step t H t' st st'); assumption]
  end.

Ltac exec_step_impossible :=
  match goal with
  | H: exec_step _ _ |- _ =>
    solve [inversion H]
  end.

Ltac exec_step_inductive :=
  match goal with
  | H: forall z, exec_step ?x z -> z = ?y, H0: exec_step ?x ?a |- _ = _ =>
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

Lemma deterministic__exec_step:
  deterministic exec_step.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [value_exec_step_impossible];
  try solve [auto];
  try solve [exec_step_inductive];
  try solve [rewrite_invert];
  try solve [equality_contradiction];
  try solve [exec_step_impossible].
  Qed.

End Verification.


Require Import Software.Lib.Relations.Relations.
Require Import Software.Doc.Example.System.System1Execution.
Require Import Software.Language.Syntax.
Require Import Software.Language.State.
Require Import Software.Language.Value.

Section Verification.

Lemma value_not_in_domain :
  forall v st,
  value v ->
  not_in_domain exec_state exec_step (Cexec_state v st).
Proof.
  intros. generalize dependent st.
  induction H; unfold not_in_domain; intros; try solve [inversion H].
  - inversion H1; subst.
    + unfold not_in_domain in IHvalue1.
      apply (IHvalue1 st (Cexec_state t' st')). assumption.
    + unfold not_in_domain in IHvalue2.
      apply (IHvalue2 st (Cexec_state t0' st')). assumption.
  - inversion H0; subst.
    unfold not_in_domain in IHvalue.
    apply (IHvalue st (Cexec_state t0' st')). assumption.
  Qed.

Ltac apply_value_not_in_domain :=
  match goal with
  | H : value ?t, H0 : exec_step (Cexec_state ?t ?st) _ |- _ =>
    apply (value_not_in_domain t st) in H;
    apply H in H0;
    inversion H0
  end.

Ltac exec_step_inductive :=
  match goal with
  | H: forall z, exec_step ?x z -> z = ?y, H0: exec_step ?x ?a |- _ = _ =>
    apply H in H0;
    inversion H0;
    auto
  end.

Ltac exec_step_impossible :=
  match goal with
  | H: exec_step _ _ |- _ =>
    solve [inversion H]
  end.

Ltac rewrite_invert :=
  match goal with
  | H: ?x = ?y, H0: ?x = ?z |- _ = _ =>
    rewrite H in H0;
    inversion H0;
    reflexivity
  end.

Lemma is_function_exec_step :
  is_function exec_state exec_step.
Proof.
  unfold is_function. intros x y1 y2 Hxy1.
  generalize dependent y2.
  induction Hxy1; intros y2 Hxy2; inversion Hxy2; subst;
  try solve [auto];
  try solve [apply_value_not_in_domain];
  try solve [exec_step_inductive];
  try solve [exec_step_impossible];
  try solve [rewrite_invert].
  Qed.

End Verification.


Require Import Coq.Bool.Bool.
Require Export Coq.Strings.Ascii.

Definition eqb (a a0 : ascii) : bool :=
  match a, a0 with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii b0' b1' b2' b3' b4' b5' b6' b7' =>
    match Bool.eqb b0 b0' with
    | false => false
    | true =>
      match Bool.eqb b1 b1' with
      | false => false
      | true =>
        match Bool.eqb b2 b2' with
        | false => false
        | true =>
          match Bool.eqb b3 b3' with
          | false => false
          | true =>
            match Bool.eqb b4 b4' with
            | false => false
            | true =>
              match Bool.eqb b5 b5' with
              | false => false
              | true =>
                match Bool.eqb b6 b6' with
                | false => false
                | true => Bool.eqb b7 b7'
                end
              end
            end
          end
        end
      end
    end
  end.

Lemma eqb_true_iff:
  forall a a0,
  eqb a a0 = true <-> a = a0.
Proof.
  destruct a; destruct a0.
  split.
  - unfold eqb.
    intros Heqb.
    destruct (Bool.eqb b b7) eqn:eq0; try solve [inversion Heqb].
    destruct (Bool.eqb b0 b8) eqn:eq1; try solve [inversion Heqb].
    destruct (Bool.eqb b1 b9) eqn:eq2; try solve [inversion Heqb].
    destruct (Bool.eqb b2 b10) eqn:eq3; try solve [inversion Heqb].
    destruct (Bool.eqb b3 b11) eqn:eq4; try solve [inversion Heqb].
    destruct (Bool.eqb b4 b12) eqn:eq5; try solve [inversion Heqb].
    destruct (Bool.eqb b5 b13) eqn:eq6; try solve [inversion Heqb].
    destruct (Bool.eqb b6 b14) eqn:eq7; try solve [inversion Heqb].
    clear Heqb.
    rewrite Bool.eqb_true_iff in eq0.
    rewrite Bool.eqb_true_iff in eq1.
    rewrite Bool.eqb_true_iff in eq2.
    rewrite Bool.eqb_true_iff in eq3.
    rewrite Bool.eqb_true_iff in eq4.
    rewrite Bool.eqb_true_iff in eq5.
    rewrite Bool.eqb_true_iff in eq6.
    rewrite Bool.eqb_true_iff in eq7.
    subst. reflexivity.
  - unfold eqb.
    intros Heq.
    inversion Heq; subst.
    destruct (Bool.eqb b7 b7) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b8 b8) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b9 b9) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b10 b10) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b11 b11) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b12 b12) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b13 b13) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    destruct (Bool.eqb b14 b14) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
    reflexivity.
  Qed. 

Lemma eqb_false_iff:
  forall a a0,
  eqb a a0 = false <-> a <> a0.
Proof.
  destruct a; destruct a0.
  unfold eqb.
  split.
  - intros Heqb Heq.
    destruct (Bool.eqb b b7) eqn:eq0; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq0; inversion eq0].
    destruct (Bool.eqb b0 b8) eqn:eq1; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq1; inversion eq1].
    destruct (Bool.eqb b1 b9) eqn:eq2; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq2; inversion eq2].
    destruct (Bool.eqb b2 b10) eqn:eq3; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq3; inversion eq3].
    destruct (Bool.eqb b3 b11) eqn:eq4; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq4; inversion eq4].
    destruct (Bool.eqb b4 b12) eqn:eq5; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq5; inversion eq5].
    destruct (Bool.eqb b5 b13) eqn:eq6; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq6; inversion eq6].
    destruct (Bool.eqb b6 b14) eqn:eq7; try solve [inversion Heq; subst; rewrite Bool.eqb_reflx in eq7; inversion eq7].
    inversion Heqb.
  - unfold not.
    intros Heq.
    destruct (Bool.eqb b b7) eqn:eq0; try solve [reflexivity].
    destruct (Bool.eqb b0 b8) eqn:eq1; try solve [reflexivity].
    destruct (Bool.eqb b1 b9) eqn:eq2; try solve [reflexivity].
    destruct (Bool.eqb b2 b10) eqn:eq3; try solve [reflexivity].
    destruct (Bool.eqb b3 b11) eqn:eq4; try solve [reflexivity].
    destruct (Bool.eqb b4 b12) eqn:eq5; try solve [reflexivity].
    destruct (Bool.eqb b5 b13) eqn:eq6; try solve [reflexivity].
    destruct (Bool.eqb b6 b14) eqn:eq7; try solve [reflexivity].
    exfalso. apply Heq; clear Heq.
    rewrite Bool.eqb_true_iff in eq0.
    rewrite Bool.eqb_true_iff in eq1.
    rewrite Bool.eqb_true_iff in eq2.
    rewrite Bool.eqb_true_iff in eq3.
    rewrite Bool.eqb_true_iff in eq4.
    rewrite Bool.eqb_true_iff in eq5.
    rewrite Bool.eqb_true_iff in eq6.
    rewrite Bool.eqb_true_iff in eq7.
    subst. reflexivity.
  Qed.

Lemma eqb_subst:
  forall P a a0,
  eqb a a0 = true -> P a -> P a0.
Proof.
  intros P a a0 Heq HP.
  rewrite eqb_true_iff in Heq. subst. assumption.
  Qed.

Lemma eqb_reflx:
  forall a,
  eqb a a = true.
Proof.
  destruct a.
  unfold eqb.
  destruct (Bool.eqb b b) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b0 b0) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b1 b1) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b2 b2) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b3 b3) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b4 b4) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b5 b5) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  destruct (Bool.eqb b6 b6) eqn:eq; try solve [rewrite Bool.eqb_reflx in eq; inversion eq]; clear eq.
  reflexivity.
  Qed.


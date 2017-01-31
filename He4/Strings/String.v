Require Import Coq.Strings.String.
Require Import He4.Strings.Ascii.

Fixpoint eqb (s s0 : string) : bool :=
  match s, s0 with
  | EmptyString, EmptyString => true
  | EmptyString, String _ _ => false
  | String _ _, EmptyString => false
  | String a s', String a0 s0' =>
    match Ascii.eqb a a0 with
    | false => false
    | true => eqb s' s0'
    end
  end.

Lemma eqb_true_iff:
  forall s s0,
  eqb s s0 = true <-> s = s0.
Proof.
  split.
  - generalize dependent s0.
    induction s; destruct s0; simpl;
    try solve [reflexivity];
    try solve [intros Heqb; inversion Heqb].
    destruct (Ascii.eqb a a0) eqn:eq; try solve [intros Heqb; inversion Heqb].
    rewrite Ascii.eqb_true_iff in eq; subst.
    intros Heqb. apply IHs in Heqb; clear IHs; subst.
    reflexivity.
  - intros Heq. subst.
    induction s0.
    reflexivity.
    simpl. destruct (Ascii.eqb a a) eqn:eq.
    assumption.
    rewrite Ascii.eqb_reflx in eq; inversion eq.
  Qed.

Lemma eqb_false_iff:
  forall s s0,
  eqb s s0 = false <-> s <> s0.
Proof.
  split.
  - generalize dependent s0.
    induction s; destruct s0; simpl;
    try solve [intros Heqb; inversion Heqb];
    try solve [intros _ contra; inversion contra].
    destruct (Ascii.eqb a a0) eqn:eq.
    rewrite Ascii.eqb_true_iff in eq; subst.
    intros Heqb Heqs.
    apply IHs in Heqb; clear IHs. apply Heqb; clear Heqb.
    inversion Heqs. reflexivity.
    intros _ Heqs. inversion Heqs; subst.
    rewrite Ascii.eqb_reflx in eq. inversion eq.
  - unfold not.
    generalize dependent s0.
    induction s; destruct s0; simpl;
    try solve [reflexivity].
    intros Heqs. exfalso. apply Heqs. reflexivity.
    destruct (Ascii.eqb a a0) eqn:eq; try solve [reflexivity].
    rewrite Ascii.eqb_true_iff in eq; subst.
    intros Heqs. apply IHs. intros Heqs2. subst.
    apply Heqs. reflexivity.
  Qed.

Lemma eqb_subst:
  forall P s s0,
  eqb s s0 = true -> P s -> P s0.
Proof.
  intros P s s0 Heqb HP.
  rewrite eqb_true_iff in Heqb. subst. assumption.
  Qed.

Lemma eqb_reflx:
  forall s,
  eqb s s = true.
Proof.
  induction s.
  simpl. reflexivity.
  unfold eqb.
  destruct (Ascii.eqb a a) eqn:eq. assumption.
  rewrite Ascii.eqb_reflx in eq; inversion eq.
  Qed.

Require Import He4.Lib.Strings.String.
Require Import He4.Language.State.
Require Import He4.Language.Syntax.

Definition called_on_class (c : string) (st : state) : Prop :=
  exists n, read_sk_hd 0 st = tref n /\ (exists t, read_sr n st = tcl c t).

Definition called_on_classb (c : string) (st : state) : bool :=
  match read_sk_hd 0 st with
  | tref n =>
    match read_sr n st with
    | tcl s _ => String.eqb s c
    | _ => false
    end
  | _ => false
  end.

Definition called_on_vclass (c : string) (st : state) : Prop :=
  exists t, read_sk_hd 0 st = tcl c t.

Definition called_on_vclassb (c : string) (st : state) : bool :=
  match read_sk_hd 0 st with
  | tcl s _ => String.eqb s c
  | _ => false
  end.

Lemma called_on_classb_true_iff:
  forall c st,
  called_on_classb c st = true <-> called_on_class c st.
Proof with auto.
  split.
  - intros. unfold called_on_classb in H.
    destruct (read_sk_hd 0 st) eqn:Hsk0; try inversion H.
    destruct (read_sr n st) eqn:Hsrn; try inversion H.
    clear H1 H2. unfold called_on_class. exists n.
    split.
    + assumption.
    + exists t. apply String.eqb_true_iff in H. subst. assumption.
  - unfold called_on_class. intros [n [Hsk [t Hsr]]].
    unfold called_on_classb. rewrite Hsk. rewrite Hsr.
    apply String.eqb_reflx.
  Qed.

Lemma called_on_classb_false_iff:
  forall c st,
  called_on_classb c st = false <-> ~(called_on_class c st).
Proof with auto.
  unfold not. split.
  - unfold called_on_class. intros H [n [Hsk [t Hsr]]].
    unfold called_on_classb in H.
    rewrite Hsk in H. rewrite Hsr in H. rewrite String.eqb_reflx in H.
    inversion H.
  - intros. unfold called_on_class in H.
    unfold called_on_classb.
    destruct (read_sk_hd 0 st) eqn:Hsk0; try reflexivity.
    destruct (read_sr n st) eqn:Hsrn; try reflexivity.
    apply String.eqb_false_iff. intros Hsc. subst.
    apply H. exists n.
    split.
    + reflexivity.
    + exists t. assumption.
  Qed.

Lemma called_on_vclassb_true_iff:
  forall c st,
  called_on_vclassb c st = true <-> called_on_vclass c st.
Proof with auto.
  split.
  - intros. unfold called_on_vclassb in H.
    destruct (read_sk_hd 0 st) eqn:Hsk0; try inversion H.
    clear H1. apply String.eqb_true_iff in H. subst.
    unfold called_on_vclass.
    exists t. assumption.
  - unfold called_on_vclass. intros [t Hsk].
    unfold called_on_vclassb. rewrite Hsk.
    apply String.eqb_reflx.
  Qed.

Lemma called_on_vclassb_false_iff:
  forall c st,
  called_on_vclassb c st = false <-> ~(called_on_vclass c st).
Proof with auto.
  unfold not. split.
  - unfold called_on_vclass. intros H [t Hsk].
    unfold called_on_vclassb in H.
    rewrite Hsk in H. rewrite String.eqb_reflx in H.
    inversion H.
  - intros. unfold called_on_vclass in H.
    unfold called_on_vclassb.
    destruct (read_sk_hd 0 st) eqn:Hsk0; try reflexivity.
    apply String.eqb_false_iff. intros Hsc. subst.
    apply H. exists t. reflexivity.
  Qed.


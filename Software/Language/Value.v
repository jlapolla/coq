Require Import Software.Language.Syntax.

Section Values.

Inductive value : term -> Prop :=

  (* Base types *)
  | vvoid : value tvoid
  | vnat : forall n, value (tnat n)
  | vbool : forall b, value (tbool b)
  | vref : forall n, value (tref n)
  | vrc : forall t rc, value t -> value rc -> value (trc t rc)
  | vrefpass : forall t, value (trefpass t)

  (* Classes *)
  | vcl : forall c t, value t -> value (tcl c t).

Fixpoint valueb (x : term) : bool :=
  match x with
  | tvoid => true
  | tnat _ => true
  | tbool _ => true
  | tref _ => true
  | trc t rc =>
    match valueb t with
    | true => valueb rc
    | false => false
    end
  | trefpass _ => true
  | tcl _ t => valueb t
  | _ => false
  end.

Hint Constructors value.

Lemma valueb_true_iff:
  forall t,
  valueb t = true <-> value t.
Proof with auto.
  split.
  - induction t; intros;
    try solve [inversion H]...
    inversion H.
    destruct (valueb t1); destruct (valueb t2);
    try solve [inversion H1].
    constructor...
  - induction t; intros; simpl;
    try solve [inversion H];
    try solve [reflexivity].
    inversion H; subst.
    apply IHt1 in H2; clear IHt1; apply IHt2 in H3; clear IHt2.
    rewrite H2; rewrite H3.
    reflexivity.
    inversion H; subst.
    apply IHt in H1; clear IHt.
    assumption.
  Qed.

Lemma valueb_false_iff:
  forall t,
  valueb t = false <-> ~(value t).
Proof with auto.
  unfold not.
  split.
  - induction t; simpl; intros;
    try solve [inversion H0];
    try solve [inversion H].
    inversion H0; subst.
    destruct (valueb t1) eqn:eq1; destruct (valueb t2) eqn:eq2...
    inversion H0; subst...
  - induction t; simpl; intros;
    try solve [auto];
    try solve [exfalso; auto].
    destruct (valueb t1) eqn:eq1; destruct (valueb t2) eqn:eq2...
    rewrite valueb_true_iff in eq1;
    rewrite valueb_true_iff in eq2.
    exfalso...
  Qed.

End Values.


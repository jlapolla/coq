Require Import He4.Language.Term.

Inductive value : tm -> Prop :=

  (* Base types *)
  | vvoid : value tvoid
  | vnat : forall n, value (tnat n)
  | vbool : forall b, value (tbool b)
  | vref : forall n, value (tref n)
  | vrc : forall t rc, value t -> value rc -> value (trc t rc)

  (* Classes *)
  | vcl : forall c t, value t -> value (tcl c t).

Fixpoint valueb (x : tm) : bool :=
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
  | tcl _ t => valueb t
  | _ => false
  end.

Lemma valueb_true_iff:
  forall t,
  valueb t = true <-> value t.
Proof with auto.
  split.
  - induction t; intros;
    try solve [inversion H];
    try solve [constructor].
    inversion H.
    destruct (valueb t1); destruct (valueb t2);
    try solve [inversion H1].
    constructor...
    inversion H.
    destruct (valueb t);
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


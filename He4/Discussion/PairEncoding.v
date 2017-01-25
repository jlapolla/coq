Section Records.

(** Records encoded as nested pair terms. *)

Hint Resolve Lt.lt_S_n.

Definition tempty := tvoid.

Inductive is_rc : tm -> Prop :=
  | RC_tempty : is_rc tempty
  | RC_tpair : forall t rc, is_rc rc -> is_rc (tpair t rc).

Fixpoint rc_create (n : nat) : tm :=
  match n with
  | O => tempty
  | S n' => tpair tempty (rc_create n')
  end.

Fixpoint rc_length (rc : tm) : nat :=
  match rc with
  | tpair _ rc' => S (rc_length rc')
  | _ => O
  end.

Fixpoint rc_read (n : nat) (rc : tm) : tm :=
  match n with
  | O =>
    match rc with
    | tpair t1 _ => t1
    | _ => tempty
    end
  | S n' =>
    match rc with
    | tpair _ rc' => rc_read n' rc'
    | _ => tempty
    end
  end.

Fixpoint rc_write (n : nat) (t rc : tm) : tm :=
  match n with
  | O =>
    match rc with
    | tpair _ rc' => tpair t rc'
    | _ => rc
    end
  | S n' =>
    match rc with
    | tpair t1 rc' => tpair t1 (rc_write n' t rc')
    | _ => rc
    end
  end.

Lemma rc_create_is_rc:
  forall n,
  is_rc (rc_create n).
Proof with auto.
  induction n; simpl; constructor...
  Qed.

Lemma rc_create_length:
  forall n,
  rc_length (rc_create n) = n.
Proof with auto.
  induction n; simpl...
  Qed.

Lemma rc_create_correct:
  forall n m,
  lt m n ->
  rc_read m (rc_create n) = tempty.
Proof with auto.
  induction n. intros. inversion H.
  destruct m; simpl...
  Qed.

Lemma rc_read_overflow:
  forall rc,
  is_rc rc ->
  forall m,
    le (rc_length rc) m ->
    rc_read m rc = tempty.
Proof with auto.
  intros rc H. induction H; destruct m...
  simpl. intros. inversion H0.
  simpl. intros. apply Le.le_S_n in H0...
  Qed.

Lemma rc_write_is_rc:
  forall rc,
  is_rc rc ->
  forall n t,
    is_rc (rc_write n t rc).
Proof with auto.
  intros rc H.
  induction H; destruct n; simpl; constructor...
  Qed.

Lemma rc_write_length:
  forall rc,
  is_rc rc ->
  forall n t,
    rc_length (rc_write n t rc) = rc_length rc.
Proof with auto.
  intros rc H. induction H.
  destruct n; simpl; constructor...
  destruct n; simpl...
  Qed.

Lemma rc_write_correct_1:
  forall rc,
  is_rc rc ->
  forall n m t,
    lt m (rc_length rc) ->
    m <> n ->
    rc_read m (rc_write n t rc) = rc_read m rc.
Proof with auto.
  intros rc H. induction H.
  simpl. intros. inversion H.
  destruct n.
  destruct m... intros. exfalso...
  destruct m...
  simpl. intros. apply not_eq_n in H1...
  Qed.

Lemma rc_write_correct_2:
  forall rc,
  is_rc rc ->
  forall n t,
    lt n (rc_length rc) ->
    rc_read n (rc_write n t rc) = t.
Proof with auto.
  intros rc H. induction H.
  intros. inversion H.
  destruct n...
  simpl. intros...
  Qed.

End Records.

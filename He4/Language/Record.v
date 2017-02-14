Require Import He4.Language.Syntax.
Require Import He4.Lib.Lists.List.

Section Records.

Hint Resolve Lt.lt_S_n.

Fixpoint rc_create (n : nat) : term :=
  match n with
  | O => tvoid
  | S n' => trc tvoid (rc_create n')
  end.

Fixpoint rc_length (rc : term) : nat :=
  match rc with
  | trc _ rc' => S (rc_length rc')
  | _ => O
  end.

Fixpoint rc_read (n : nat) (rc : term) : term :=
  match n with
  | O =>
    match rc with
    | trc t1 _ => t1
    | _ => tvoid
    end
  | S n' =>
    match rc with
    | trc _ rc' => rc_read n' rc'
    | _ => tvoid
    end
  end.

Fixpoint rc_write (n : nat) (t rc : term) : term :=
  match n with
  | O =>
    match rc with
    | trc _ rc' => trc t rc'
    | _ => rc
    end
  | S n' =>
    match rc with
    | trc t1 rc' => trc t1 (rc_write n' t rc')
    | _ => rc
    end
  end.

Fixpoint rc_to_list (rc : term) : list term :=
  match rc with
  | trc t1 rc' => cons t1 (rc_to_list rc')
  | _ => nil
  end.

Fixpoint list_to_rc (l : list term) : term :=
  match l with
  | nil => tvoid
  | cons t' l' => trc t' (list_to_rc l')
  end.

Lemma rc_create_length:
  forall n,
  rc_length (rc_create n) = n.
Proof with auto.
  induction n; simpl...
  Qed.

Lemma rc_create_correct:
  forall n m,
  lt m n ->
  rc_read m (rc_create n) = tvoid.
Proof with auto.
  induction n. intros. inversion H.
  destruct m; simpl...
  Qed.

Lemma rc_read_overflow:
  forall rc m,
  le (rc_length rc) m ->
  rc_read m rc = tvoid.
Proof with auto.
  induction rc; try (destruct m; auto).
  simpl. intros. inversion H.
  simpl. intros. apply Le.le_S_n in H...
  Qed.

Lemma rc_write_length:
  forall rc n t,
  rc_length (rc_write n t rc) = rc_length rc.
Proof with auto.
  induction rc;
  try solve [destruct n; simpl; auto];
  try solve [destruct n0; auto].
  Qed.

Lemma rc_write_correct_1:
  forall rc n m t,
  lt m (rc_length rc) ->
  m <> n ->
  rc_read m (rc_write n t rc) = rc_read m rc.
Proof with auto.
  induction rc;
  try solve [destruct n; auto];
  try solve [destruct n0; auto].
  destruct n.
  destruct m; try solve [intros; exfalso; auto]...
  destruct m; simpl...
  Qed.

Lemma rc_write_correct_2:
  forall rc n t,
  lt n (rc_length rc) ->
  rc_read n (rc_write n t rc) = t.
Proof with auto.
  induction rc;
  try solve [simpl; intros; inversion H].
  destruct n; simpl; intros...
  Qed.

Lemma rc_to_list_length:
  forall rc,
  length (rc_to_list rc) = rc_length rc.
Proof with auto.
  induction rc...
  simpl...
  Qed.

Lemma rc_to_list_correct:
  forall rc m d1,
  lt m (rc_length rc) ->
  nth m (rc_to_list rc) d1 = rc_read m rc.
Proof with auto.
  induction rc;
  try solve [intros; inversion H].
  destruct m; simpl...
  Qed.

Lemma list_to_rc_length:
  forall l,
  rc_length (list_to_rc l) = length l.
Proof with auto.
  induction l...
  simpl...
  Qed.

Lemma list_to_rc_correct:
  forall l m d,
  lt m (length l) ->
  rc_read m (list_to_rc l) = nth m l d.
Proof.
  induction l;
  try solve [intros; inversion H].
  destruct m;
  try solve [simpl; intros; auto].
  Qed.

End Records.


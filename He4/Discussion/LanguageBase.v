Require Export He4.Discussion.ProgramState.

Section LanguageDefinitions.

Set Implicit Arguments.

Variable cl : Type.
Variable fn : Type.

Inductive tm : Type :=

  (* Base types *)
  | tvoid : tm
  | tnat : nat -> tm
  | tbool : bool -> tm

  (* Variables and references *)
  | tvar : nat -> tm
  | tref : nat -> tm
  | tassign : tm -> tm -> tm

  (* Control flow *)
  | tseq : tm -> tm -> tm

  (* Records *)
  | trc : tm -> tm -> tm

  (* Functions *)
  | tcall : fn -> tm -> tm
  | texec : fn -> tm
  | treturn : tm -> tm

  (* Classes *)
  | tnew : cl -> tm
  | tcl : cl -> tm -> tm.

Inductive value : tm -> Prop :=

  (* Base types *)
  | vvoid : value tvoid
  | vnat : forall n, value (tnat n)
  | vbool : forall b, value (tbool b)
  | vref : forall n, value (tref n)
  | vrc : forall t rc, value t -> value rc -> value (trc t rc)

  (* Classes *)
  | vcl : forall c t, value t -> value (tcl c t).

Definition stack := ProgramState.stack tm.
Definition sk_read_hd (n : nat) (sk : stack) : tm := ProgramState.sk_read_hd n sk tvoid.
Definition sk_resize_hd (n : nat) (sk : stack) : stack := ProgramState.sk_resize_hd n sk tvoid.
Definition empty_stack : stack := push nil nil.

Definition store := ProgramState.store tm.
Definition sr_read (n : nat) (sr : store) : tm := ProgramState.sr_read n sr tvoid.
Definition empty_store : store := sr_alloc tvoid nil. (* Position 0 represents the "null" reference *)

(** Records encoded as nested pair terms. *)

Hint Resolve Lt.lt_S_n.

Fixpoint rc_create (n : nat) : tm :=
  match n with
  | O => tvoid
  | S n' => trc tvoid (rc_create n')
  end.

Fixpoint rc_length (rc : tm) : nat :=
  match rc with
  | trc _ rc' => S (rc_length rc')
  | _ => O
  end.

Fixpoint rc_read (n : nat) (rc : tm) : tm :=
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

Fixpoint rc_write (n : nat) (t rc : tm) : tm :=
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

Fixpoint rc_to_list (rc : tm) : list tm :=
  match rc with
  | trc t1 rc' => cons t1 (rc_to_list rc')
  | _ => nil
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

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm (prod stack store)) -> (prod tm (prod stack store)) -> Prop :=
  | STvar :
    forall n sk sr,
    (tvar n) / (pair sk sr) ==> sk_read_hd n sk / (pair sk sr)

  | STassign_r :
    forall n t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tassign (tvar n) t0 / st ==> tassign (tvar n) t0' / st'
  | STassign :
    forall n v0 sk sr,
    value v0 ->
    tassign (tvar n) v0 / (pair sk sr) ==> tvoid / (pair (sk_write_hd n v0 sk) sr)

  | STseq_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tseq t t0 / st ==> tseq t' t0 / st'
  | STseq :
    forall t0 st,
    tseq tvoid t0 / st ==> t0 / st

  | STrc_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    trc t t0 / st ==> trc t' t0 / st'
  | STrc_r :
    forall v t0 t0' st st',
    value v ->
    t0 / st ==> t0' / st' ->
    trc v t0 / st ==> trc v t0' / st'

  | STcall_r :
    forall f t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tcall f t0 / st ==> tcall f t0' / st'
  | STcall :
    forall f v0 sk sr,
    value v0 ->
    tcall f v0 / (pair sk sr) ==> treturn (texec f) / (pair (push (rc_to_list v0) sk) sr)

  | STreturn_r :
    forall t t' st st',
    t / st ==> t' / st' ->
    treturn t / st ==> treturn t' / st'
  | STreturn :
    forall v sk sr,
    value v ->
    treturn v / (pair sk sr) ==> v / (pair (pop sk) sr)

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).

Unset Implicit Arguments.

Lemma value_does_not_step:
  forall t,
  value t ->
  forall st t' st',
    ~(t / st ==> t' / st').
Proof with eauto.
  intros t Hval.
  induction Hval;
  try solve [intros st t' st' Hcontra; inversion Hcontra].
  intros st t' st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval1 in H0. inversion H0.
  apply IHHval2 in H5. inversion H5.
  Qed.

Lemma step_deterministic:
  forall x y,
  step x y ->
  forall z,
    step x z ->
    z = y.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [apply IHHxy in H3; inversion H3; subst; auto];
  try solve [auto].
  destruct (value_does_not_step t0 H3 (pair sk sr) t0' st')...
  destruct (value_does_not_step v0 H (pair sk sr) t0' st')...
  inversion Hxy.
  inversion H3.
  destruct (value_does_not_step t H3 st t' st')...
  destruct (value_does_not_step v H st t' st'0)...
  apply IHHxy in H5; inversion H5; subst...
  destruct (value_does_not_step t0 H3 (pair sk sr) t0' st')...
  destruct (value_does_not_step v0 H (pair sk sr) t0' st')...
  apply IHHxy in H2; inversion H2; subst...
  destruct (value_does_not_step t H2 (pair sk sr) t' st')...
  destruct (value_does_not_step v H (pair sk sr) t' st')...
  Qed.

End LanguageDefinitions.

Module ObjectOrientedNotations.

Notation "'|(' ')|'" := tvoid (at level 10, format "'|(' ')|'") : oo_scope.

Notation "'|(' t ')|'" := (trc t tvoid) (at level 10, format "'|(' t ')|'") : oo_scope.

Notation "'|(' t ',' .. ',' t0 ')|'" :=
  (trc t .. (trc t0 tvoid) ..) (at level 10, format "'|(' t ','  .. ','  t0 ')|'") : oo_scope.

Notation "t '#' f t0" :=
  (tcall f (trc t t0)) (at level 20, left associativity, format "t  '#'  f t0") : oo_scope.

Notation "t ; t0" :=
  (tseq t t0) (at level 80, right associativity, format "'[v' t ';' '/' t0 ']'").

Notation "t '::=' t0" :=
  (tassign t t0) (at level 30, right associativity) : oo_scope.

Delimit Scope oo_scope with oo.

End ObjectOrientedNotations.

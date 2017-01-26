Module NatRangeIterator.

Require Import He4.Discussion.ProgramState.

Inductive f1 : Type :=
  | F1get_first : f1.

Inductive f2 : Type :=
  | F2set_first : f2.

(* Classes *)
Inductive cl : Type :=
  | CLNatRangeIterator : cl.

Inductive ty : Type :=

  (* Base types *)
  | Tvoid : ty
  | Tnat : ty
  | Tbool : ty
  | Tref : ty -> ty

  (* Classes *)
  | Tcl : cl -> ty.

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

  (* Named functions *)
  | tf1 : f1 -> tm -> tm
  | tf2 : f2 -> tm -> tm -> tm

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

Definition tempty := tvoid.

Section Stacks.
Definition stack := ProgramState.stack tm.
Definition sk_read_hd (n : nat) (sk : stack) : tm := ProgramState.sk_read_hd n sk tempty.
Definition sk_resize_hd (n : nat) (sk : stack) : stack := ProgramState.sk_resize_hd n sk tempty.
Definition empty_stack : stack := push nil nil.
End Stacks.

Section Stores.
Definition store := ProgramState.store tm.
Definition sr_read (n : nat) (sr : store) : tm := ProgramState.sr_read n sr tempty.
Definition empty_store : store := sr_alloc tempty nil. (* Position 0 represents the "null" reference *)
End Stores.

Section Records.

(** Records encoded as nested pair terms. *)

Hint Resolve Lt.lt_S_n.

Inductive is_rc : tm -> Prop :=
  | RC_tempty : is_rc tempty
  | RC_trc : forall t rc, is_rc rc -> is_rc (trc t rc).

Fixpoint rc_create (n : nat) : tm :=
  match n with
  | O => tempty
  | S n' => trc tempty (rc_create n')
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
    | _ => tempty
    end
  | S n' =>
    match rc with
    | trc _ rc' => rc_read n' rc'
    | _ => tempty
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

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm (prod stack store)) -> (prod tm (prod stack store)) -> Prop :=
  | STvar :
    forall n sk sr,
    (tvar n) / (pair sk sr) ==> sk_read_hd n sk / (pair sk sr)

  | STassign_r :
    forall n t2 t2' st st',
    t2 / st ==> t2' / st' ->
    tassign (tvar n) t2 / st ==> tassign (tvar n) t2' / st'
  | STassign :
    forall n v sk sr,
    value v ->
    tassign (tvar n) v / (pair sk sr) ==> tvoid / (pair (sk_write_hd n v sk) sr)

  | STseq_l :
    forall t1 t1' t2 st st',
    t1 / st ==> t1' / st' ->
    tseq t1 t2 / st ==> tseq t1' t2 / st'
  | STseq :
    forall t2 st,
    tseq tvoid t2 / st ==> t2 / st

  | STrc_l :
    forall t1 t1' rc st st',
    t1 / st ==> t1' / st' ->
    trc t1 rc / st ==> trc t1' rc / st'
  | STrc_r :
    forall v1 rc rc' st st',
    value v1 ->
    rc / st ==> rc' / st' ->
    trc v1 rc / st ==> trc v1 rc' / st'

  | STf1_1 :
    forall f1 t1 t1' st st',
    t1 / st ==> t1' / st' ->
    tf1 f1 t1 / st ==> tf1 f1 t1' / st'

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).






  | STf2_1 :
    forall f2 t1 t1' t2 st st',
    t1 / st ==> t1' / st' ->
    tf2 f2 t1 t2 / st ==> tf2 f2 t1' t2 / st'
  | STf2_2 :
    forall f2 v1 t2 t2' st st',
    value v1 ->
    t2 / st ==> t2' / st' ->
    tf2 f2 v1 t2 / st ==> tf2 f2 v1 t2' / st'

  (* Classes *)
  | STnew_NatRangeIterator :
    sr' = alloc (pair (Tclass CLNatRangeIterator)  ) sr ->
    tnew CLNatRangeIterator / (pair sk sr) ==>

Notation "t ',get_first()'" :=
  (tf1_get_first t) (at level 0, format "t ',get_first()'") : oo_scope.

Notation "t1 ',set_first(' t2 ')'" :=
  (tf2_set_first t1 t2) (at level 0, format "t1 ',set_first(' t2 ')'") : oo_scope.

Notation "t1 ',test(' t2 , t3 ')'" :=
  (tf3_test t1 t2 t3) (at level 0, format "t1 ',test(' t2 ,  t3 ')'") : oo_scope.

Delimit Scope oo_scope with oo.

Example ex_comma_notation1 :
  ((tbool false),get_first(),get_first())%oo = tf1_get_first (tf1_get_first (tbool false)).
Proof. reflexivity. Qed.

Example ex_comma_notation2 :
  ((tbool false),set_first(tnat 3),get_first())%oo = tf1_get_first (tf2_set_first (tbool false) (tnat 3)).
Proof. reflexivity. Qed.

Example ex_comma_notation3 :
  ((tbool false),test(tnat 3, tnat 4))%oo = tf3_test (tbool false) (tnat 3) (tnat 4).
Proof. reflexivity. Qed.

Notation "t1 ;; t2" :=
  (tseq t1 t2) (at level 80, right associativity).

End NatRangeIterator.

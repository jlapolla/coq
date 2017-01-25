Require Export Coq.Lists.List.

Set Implicit Arguments.

Section ListOperations.

Variable A : Type.

Fixpoint replace (n : nat) (a : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a' l' =>
    match n with
    | O => cons a l'
    | S n' => cons a' (replace n' a l')
    end
  end.

(** TODO: Fill in Lemmas *)

Fixpoint repeat (x : A) (n : nat) : list A :=
  match n with
  | O => nil
  | S k => cons x (repeat x k)
  end.

Lemma repeat_length:
  forall n x,
  length (repeat x n) = n.
Proof with auto.
  induction n...
  intros. simpl. rewrite IHn...
  Qed.

Lemma repeat_correct:
  forall n m x default,
  lt m n ->
  nth m (repeat x n) default = x.
Proof with auto.
  induction n. intros. inversion H.
  destruct m...
  intros. simpl. apply Lt.lt_S_n in H...
  Qed.

(** TODO: Fill in Lemmas *)

End ListOperations.

Section Stacks.

Variable A : Type.

Definition stack_frame := list A.

Definition stack := list stack_frame.

Definition push := cons.

Definition pop := tl.

Function sk_write (n : nat) (a : A) (sk : stack) : stack :=
  match sk with
  | nil => nil
  | cons sf' sk' => cons (replace n a sf') sk'
  end.

Function sk_read (n : nat) (sk : stack) (default : A) : A :=
  match sk with
  | nil => default
  | cons sf' sk' => nth n sf' default
  end.

Fixpoint sf_resize (n : nat) (sf : stack_frame) (default : A) : stack_frame :=
  match n with
  | O => nil
  | S n' =>
    match sf with
    | nil => cons default (sf_resize n' sf default)
    | cons a' sf' => cons a' (sf_resize n' sf' default)
    end
  end.

Lemma sf_resize_length:
  forall n sf default,
  length (sf_resize n sf default) = n.
Proof with auto.
  induction n...
  destruct sf; simpl...
  Qed.

Lemma sf_resize_nil:
  forall n default,
  sf_resize n nil default = repeat default n.
Proof with auto.
  induction n...
  intros. simpl. rewrite IHn...
  Qed.

Lemma sf_resize_correct_1:
  forall sf n m d1 d2,
  lt m n ->
  lt m (length sf) ->
  nth m (sf_resize n sf d1) d2 = nth m sf d2.
Proof with auto.
  induction sf.
  destruct n; try (intros; inversion H0).
  destruct n. intros. inversion H.
  destruct m...
  intros. simpl. simpl in H0.
  apply Lt.lt_S_n in H. apply Lt.lt_S_n in H0.
  apply IHsf...
  Qed.

Lemma sf_resize_correct_2:
  forall sf n m d1 d2,
  lt m n ->
  le (length sf) m ->
  nth m (sf_resize n sf d1) d2 = d1.
Proof with auto.
  induction sf.
  destruct n. intros. inversion H.
  destruct m... intros. simpl.
  intros. rewrite sf_resize_nil.
  rewrite repeat_correct...
  apply Lt.lt_S_n in H...
  destruct n. intros. inversion H.
  destruct m. intros. inversion H0.
  simpl. intros.
  apply Lt.lt_S_n in H. apply Le.le_S_n in H0...
  Qed.

Definition sk_resize (n : nat) (sk : stack) (default : A) : stack :=
  push (sf_resize n (hd nil sk) default) (pop sk).

(** TODO: Fill in Lemmas *)

End Stacks.

Section Stores.

Variable A : Type.

Definition store := list A.

Definition alloc (a : A) (sr : store) :=
  app sr (cons a nil).

Definition sr_write := replace.

Definition sr_read := nth.

(** TODO: Fill in Lemmas *)

End Stores.

Require Export Coq.Lists.List.

Set Implicit Arguments.

Section ListOperations.

Hint Resolve Lt.lt_S_n.

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

Lemma replace_length:
  forall n l a,
  length (replace n a l) = length l.
Proof with auto.
  induction n.
  destruct l...
  destruct l...
  simpl. intros. apply f_equal. apply IHn...
  Qed.

(* TODO: Move not_eq_n to another library. *)

Lemma not_eq_n:
  forall n m : nat,
  S n <> S m ->
  n <> m.
Proof.
  auto.
  Qed.

Lemma replace_correct_1:
  forall l n m d a,
  m < length l ->
  m <> n ->
  nth m (replace n a l) d = nth m l d.
Proof with auto.
  induction l. intros. inversion H.
  destruct n.
  destruct m... intros. exfalso...
  destruct m...
  simpl. intros. apply not_eq_n in H0...
  Qed.

Lemma replace_correct_2:
  forall l n d a,
  n < length l ->
  nth n (replace n a l) d = a.
Proof with auto.
  induction l. intros. inversion H.
  destruct n...
  simpl. intros...
  Qed.

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
  intros. simpl...
  Qed.

(** TODO: Fill in Lemmas *)

Fixpoint resize (n : nat) (l : list A) (default : A) : list A :=
  match n with
  | O => nil
  | S n' =>
    match l with
    | nil => cons default (resize n' l default)
    | cons a' l' => cons a' (resize n' l' default)
    end
  end.

Lemma resize_length:
  forall n l default,
  length (resize n l default) = n.
Proof with auto.
  induction n...
  destruct l; simpl...
  Qed.

Lemma resize_nil:
  forall n default,
  resize n nil default = repeat default n.
Proof with auto.
  induction n...
  intros. simpl. rewrite IHn...
  Qed.

Lemma resize_correct_1:
  forall l n m d1 d2,
  lt m n ->
  lt m (length l) ->
  nth m (resize n l d1) d2 = nth m l d2.
Proof with auto.
  induction l.
  destruct n; try (intros; inversion H0).
  destruct n. intros. inversion H.
  destruct m...
  simpl...
  Qed.

Lemma resize_correct_2:
  forall l n m d1 d2,
  lt m n ->
  le (length l) m ->
  nth m (resize n l d1) d2 = d1.
Proof with auto.
  induction l.
  destruct n. intros. inversion H.
  destruct m... intros. simpl.
  intros. rewrite resize_nil.
  rewrite repeat_correct...
  destruct n. intros. inversion H.
  destruct m. intros. inversion H0.
  simpl. intros. apply Le.le_S_n in H0...
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

Definition sk_resize (n : nat) (sk : stack) (default : A) : stack :=
  push (resize n (hd nil sk) default) (pop sk).

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

Require Import Coq.Lists.List.

Set Implicit Arguments.

Section Lists.

Hint Resolve Lt.lt_S_n List.nth_indep.

Variable A : Type.

Fixpoint replace (n : nat) (a : A) (l : list A) {struct l} : list A :=
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
  forall l n m d1 d2 a,
  m < length l ->
  m <> n ->
  nth m (replace n a l) d1 = nth m l d2.
Proof with auto.
  induction l; try solve [intros; inversion H].
  destruct n; try solve [destruct m; simpl; auto].
  destruct m; try solve [intros; exfalso; auto].
  simpl...
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
  forall l n m d1 d2 d3,
  lt m n ->
  lt m (length l) ->
  nth m (resize n l d1) d2 = nth m l d3.
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

End Lists.


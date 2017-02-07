Require Import He4.Language.Record.
Require Import He4.Lists.List.
Require Import Coq.Lists.List.
Require Import He4.Language.CallStack.
Require Import He4.Language.Term.
Require Import He4.Language.Stack.
Require Import He4.Language.Store.

(** * Types *)

Inductive state : Type :=
  | Cstate: stack -> call_stack -> store -> state.

(** * Functions *)
(** ** State accessors *)

Definition get_stack (st : state) : stack :=
  match st with
  | Cstate sk _ _ => sk
  end.

Definition get_call_stack (st : state) : call_stack :=
  match st with
  | Cstate _ csk _ => csk
  end.

Definition get_store (st : state) : store :=
  match st with
  | Cstate _ _ sr => sr
  end.

Definition set_stack (sk : stack) (st : state) : state :=
  match st with
  | Cstate _ csk sr => Cstate sk csk sr
  end.

Definition set_call_stack (csk : call_stack) (st : state) : state :=
  match st with
  | Cstate sk _ sr => Cstate sk csk sr
  end.

Definition set_store (sr : store) (st : state) : state :=
  match st with
  | Cstate sk csk _ => Cstate sk csk sr
  end.

(** ** Function call *)

Section FunctionCalls.

Fixpoint args_to_call_frame (args : list tm) : call_frame :=
  match args with
  | nil => nil
  | cons t args' =>
    match t with
    | trefpass t' =>
      match t' with
      | tvar n => cons (Some n) (args_to_call_frame args')
      | _ => cons None (args_to_call_frame args')
      end
    | _ => cons None (args_to_call_frame args')
    end
  end.

Fixpoint args_to_stack_frame (args : list tm) (context : stack_frame) : stack_frame :=
  match args with
  | nil => nil
  | cons t args' =>
    match t with
    | trefpass t' =>
      match t' with
      | tvar n => cons (nth n context tvoid) (args_to_stack_frame args' context)
      | _ => cons t (args_to_stack_frame args' context)
      end
    | _ => cons t (args_to_stack_frame args' context)
    end
  end.

Fixpoint return_refpass_args (cf : call_frame) (source target : stack_frame) : stack_frame :=
  match cf with
  | nil => target
  | cons c cf' =>
    match c with
    | None => return_refpass_args cf' (tl source) target
    | Some n => return_refpass_args cf' (tl source) (replace n (hd tvoid source) target)
    end
  end.

Definition push_call (args : tm) (st : state) : state :=
  set_call_stack (
    CallStack.push (
      args_to_call_frame (rc_to_list args)
    ) (get_call_stack st)
  ) ( set_stack (
        push (
          args_to_stack_frame (rc_to_list args) (hd nil (get_stack st))
        ) (get_stack st)
      ) st
    ).

Definition pop_call (st : state) : state :=
  set_call_stack (
    CallStack.pop (get_call_stack st)
  ) ( set_stack (
        push (
          return_refpass_args (hd nil (get_call_stack st)) (hd nil (get_stack st)) (nth 1 (get_stack st) nil)
        ) (pop (pop (get_stack st)))
      ) st
    ).

Hint Resolve Lt.lt_S_n List.nth_indep.

Lemma args_to_call_frame_length:
  forall args,
  length (args_to_call_frame args) = length args.
Proof with auto.
  induction args...
  destruct a; simpl...
  destruct a; simpl...
  Qed.

Lemma args_to_call_frame_correct_1:
  forall args m d1 d2,
  lt m (length args) ->
  (forall n, nth m args d1 <> trefpass (tvar n)) ->
  nth m (args_to_call_frame args) d2 = None.
Proof with auto.
  induction args; try solve [intros; inversion H].
  destruct m; simpl; intros d1 d2 Hlen Hstruct.
  destruct a; simpl...
  destruct a; simpl...
  exfalso. apply (Hstruct n)...
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  Qed.

Lemma args_to_call_frame_correct_2:
  forall args m n d1 d2,
  lt m (length args) ->
  nth m args d1 = trefpass (tvar n) ->
  nth m (args_to_call_frame args) d2 = Some n.
Proof with auto.
  induction args; try solve [intros; inversion H].
  destruct m; simpl; intros n d1 d2 Hlen Hstruct.
  destruct a; try solve [inversion Hstruct].
  destruct a; try solve [inversion Hstruct].
  inversion Hstruct; subst...
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  Qed.

Lemma args_to_stack_frame_length:
  forall args context,
  length (args_to_stack_frame args context) = length args.
Proof with auto.
  induction args...
  destruct a; simpl...
  destruct a; simpl...
  Qed.

Lemma args_to_stack_frame_correct_1:
  forall args m context d1 d2 d3,
  lt m (length args) ->
  (forall n, nth m args d1 <> trefpass (tvar n)) ->
  nth m (args_to_stack_frame args context) d2 = nth m args d3.
Proof with auto.
  induction args; try solve [intros; inversion H].
  destruct m; simpl; intros context d1 d2 d3 Hlen Hstruct.
  destruct a; simpl...
  destruct a; simpl...
  exfalso. apply (Hstruct n)...
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  Qed.

Lemma args_to_stack_frame_correct_2:
  forall args m n context d1 d2,
  lt m (length args) ->
  nth m args d1 = trefpass (tvar n) ->
  nth m (args_to_stack_frame args context) d2 = nth n context tvoid.
Proof with auto.
  induction args; try solve [intros; inversion H].
  destruct m; simpl; intros n context d1 d2 Hlen Hstruct.
  destruct a; try solve [inversion Hstruct].
  destruct a; try solve [inversion Hstruct].
  inversion Hstruct; simpl...
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  destruct a; try solve [simpl; apply IHargs with d1; auto].
  Qed.

Lemma return_refpass_args_length:
  forall cf target source,
  length (return_refpass_args cf source target) = length target.
Proof with auto using replace_length.
  induction cf...
  destruct target.
  destruct a; intros; simpl return_refpass_args...
  destruct a; try solve [intros; simpl; rewrite IHcf; auto].
  destruct n; intros; simpl; rewrite IHcf; simpl...
  Qed.

Lemma return_refpass_args_correct_1:
  forall cf target n source d1 d2 d3,
  (forall m, lt m (length cf) -> nth m cf d1 <> Some n) ->
  lt n (length target) ->
  nth n (return_refpass_args cf source target) d2 = nth n target d3.
Proof with auto.
  induction cf. simpl...
  (* cf <> nil *)
  destruct target. intros. inversion H0.
  (* target <> nil *)
  destruct a.
  (* cf = Some n0 :: cf' *)
    intros n0. destruct (EqNat.beq_nat n0 n) eqn:Hnvals.
    (* n0 = n *)
      apply EqNat.beq_nat_true_iff in Hnvals. subst.
      intros. exfalso. apply (H 0).
        simpl. apply Lt.lt_0_Sn.
        reflexivity.
    (* n0 <> n*)
      apply EqNat.beq_nat_false_iff in Hnvals.
      destruct n; destruct n0.
      (* n0 = 0 /\ n = 0 *)
        exfalso. apply Hnvals. reflexivity.
      (* n0 = S n0' /\ n = 0 *)
        intros. simpl return_refpass_args. rewrite IHcf with (d1 := d1) (d3 := d3).
          reflexivity.
          intros. apply (H (S m)). simpl. apply Lt.lt_n_S. assumption.
          simpl. assumption.
      (* n0 = 0 /\ n = S n' *)
        intros. simpl return_refpass_args. rewrite IHcf with (d1 := d1) (d3 := d3).
          reflexivity.
          intros. apply (H (S m)). simpl. apply Lt.lt_n_S. assumption.
          simpl. rewrite replace_length. assumption.
      (* n0 = S n0' /\ n = S n' *)
        intros. simpl return_refpass_args. rewrite IHcf with (d1 := d1) (d3 := d3).
          simpl. rewrite replace_correct_1 with (d2 := d3).
            reflexivity.
            apply Lt.lt_S_n. assumption.
            apply not_eq_n. assumption.
        intros. apply (H (S m)).
          simpl. apply Lt.lt_n_S. assumption.
        simpl. rewrite replace_length. assumption.
  (* cf = None :: cf' *)
    intros. simpl return_refpass_args. rewrite IHcf with (d1 := d1) (d3 := d3).
      reflexivity.
      intros. apply (H (S m)). simpl. apply Lt.lt_n_S. assumption.
      simpl. assumption.
  Qed.

Definition refpass_unique (cf : call_frame) : Prop :=
  forall m m' n d1 d2,
  lt m (length cf) ->
  nth m cf d1 = Some n ->
  lt m' (length cf) ->
  nth m' cf d2 = Some n ->
  m' = m.

Lemma refpass_unique_nil:
  refpass_unique nil.
Proof with auto.
  unfold refpass_unique.
  intros. inversion H.
  Qed.

Lemma refpass_unique_cons:
  forall cf a,
  refpass_unique (cons a cf) ->
  refpass_unique cf.
Proof with auto.
  induction cf. intros. apply refpass_unique_nil.
  unfold refpass_unique. intros.
  apply (H (S m) (S m') n d1 d2) in H3.
    inversion H3. reflexivity.
    simpl. apply Lt.lt_n_S. assumption.
    simpl. destruct m; assumption.
    simpl. apply Lt.lt_n_S. assumption.
  Qed.

Lemma return_refpass_args_correct_2:
  forall source cf target n m d1 d2,
  refpass_unique cf ->
  lt m (length cf) ->
  nth m cf d1 = Some n ->
  lt n (length target) ->
  nth n (return_refpass_args cf source target) d2 = nth m source tvoid.
Proof with auto.
  induction source.
  (* source = nil *)
    induction cf. intros. inversion H0.
    (* cf <> nil *)
    destruct target. intros. inversion H2.
    (* target <> nil *)
    destruct a.
    (* cf = Some n0 :: cf' *)
      intros n0. destruct (EqNat.beq_nat n0 n) eqn:Hnvals.
      (* n0 = n *)
        apply EqNat.beq_nat_true_iff in Hnvals. subst.
        intros.
        assert (m = 0) as H3.
        {
          unfold refpass_unique in H.
          apply (H 0 m n d1 d1).
            simpl. apply Lt.lt_0_Sn.
            reflexivity.
            assumption.
            assumption.
        }
        subst.
        destruct n.
        (* n = 0 *)
          simpl return_refpass_args.
          rewrite return_refpass_args_correct_1 with (d1 := d1) (d3 := d2).
            reflexivity.
            intros m H3 H4. unfold refpass_unique in H.
              simpl length in H, H0.
              apply (H 0 (S m) 0 d1 d1) in H4; try solve [assumption].
                inversion H4.
                apply Lt.lt_n_S. assumption.
            simpl. apply Lt.lt_0_Sn.
        (* n = S n' *)
          simpl return_refpass_args.
          rewrite return_refpass_args_correct_1 with (d1 := d1) (d3 := d2).
            simpl. rewrite replace_correct_2.
              reflexivity.
              apply Lt.lt_S_n. assumption.
            intros m H3 H4. unfold refpass_unique in H.
              simpl length in H, H0.
              apply (H 0 (S m) (S n) d1 d1) in H4; try solve [assumption].
                inversion H4.
                apply Lt.lt_n_S. assumption.
            simpl. rewrite replace_length. assumption.
      (* n0 <> n *)
        apply EqNat.beq_nat_false_iff in Hnvals.
        destruct n0; destruct n.
        (* n0 = 0 /\ n = 0 *)
          exfalso. apply Hnvals. reflexivity.
        (* n0 = 0 /\ n = S n *)
          destruct m.
          (* m = 0 *)
            intros. inversion H1.
          (* m = S m' *)
            intros. simpl return_refpass_args.
            rewrite IHcf with (m := m) (d1 := d1).
              destruct m; reflexivity.
              apply refpass_unique_cons in H. assumption.
              simpl in H0. apply Lt.lt_S_n. assumption.
              assumption.
              simpl. rewrite replace_length. assumption.
        (* n0 = S n0' /\ n = 0 *)
          destruct m.
          (* m = 0 *)
            intros. inversion H1.
          (* m = S m' *)
            intros. simpl return_refpass_args.
            rewrite IHcf with (m := m) (d1 := d1).
              destruct m; reflexivity.
              apply refpass_unique_cons in H. assumption.
              simpl in H0. apply Lt.lt_S_n. assumption.
              assumption.
              assumption.
        (* n0 = S n0' /\ n = S n' *)
          destruct m.
          (* m = 0 *)
            intros. inversion H1; subst. exfalso. apply Hnvals. reflexivity.
          (* m = S m' *)
            intros. simpl return_refpass_args.
            rewrite IHcf with (m := m) (d1 := d1).
              destruct m; reflexivity.
              apply refpass_unique_cons in H. assumption.
              simpl in H0. apply Lt.lt_S_n. assumption.
              assumption.
              simpl. rewrite replace_length. assumption.
    (* cf = None :: cf' *)
      destruct m.
      (* m = 0 *)
        intros. inversion H1.
      (* m = S m' *)
        intros. simpl return_refpass_args.
        rewrite IHcf with (m := m) (d1 := d1).
          destruct m; reflexivity.
          apply refpass_unique_cons in H. assumption.
          simpl in H0. apply Lt.lt_S_n. assumption.
          assumption.
          simpl. assumption.
  (* source <> nil *)
    destruct cf. intros. inversion H0.
    (* cf <> nil *)
    destruct target. intros. inversion H2.
    (* target <> nil *)
    destruct o.
    (* cf = Some n0 :: cf' *)
      intros n0. destruct (EqNat.beq_nat n0 n) eqn:Hnvals.
      (* n0 = n *)
        apply EqNat.beq_nat_true_iff in Hnvals. subst.
        intros.
        assert (m = 0) as H3.
        {
          unfold refpass_unique in H.
          apply (H 0 m n d1 d1).
            simpl. apply Lt.lt_0_Sn.
            reflexivity.
            assumption.
            assumption.
        }
        subst.
        destruct n.
        (* n = 0 *)
          simpl return_refpass_args.
          rewrite return_refpass_args_correct_1 with (d1 := d1) (d3 := d2).
            reflexivity.
            intros m H3 H4. unfold refpass_unique in H.
              simpl length in H, H0.
              apply (H 0 (S m) 0 d1 d1) in H4; try solve [assumption].
                inversion H4.
                apply Lt.lt_n_S. assumption.
            simpl. apply Lt.lt_0_Sn.
        (* n = S n' *)
          simpl return_refpass_args.
          rewrite return_refpass_args_correct_1 with (d1 := d1) (d3 := d2).
            simpl. rewrite replace_correct_2.
              reflexivity.
              apply Lt.lt_S_n. assumption.
            intros m H3 H4. unfold refpass_unique in H.
              simpl length in H, H0.
              apply (H 0 (S m) (S n) d1 d1) in H4; try solve [assumption].
                inversion H4.
                apply Lt.lt_n_S. assumption.
            simpl. rewrite replace_length. assumption.
      (* n0 <> n *)
        apply EqNat.beq_nat_false_iff in Hnvals.
        destruct n0; destruct n.
        (* n0 = 0 /\ n = 0 *)
          exfalso. apply Hnvals. reflexivity.
        (* n0 = 0 /\ n = S n *)
          destruct m.
          (* m = 0 *)
            intros. inversion H1.
          (* m = S m' *)
            intros. simpl.
            rewrite IHsource with (m := m) (d1 := d1).
              reflexivity.
              apply refpass_unique_cons in H. assumption.
              simpl in H0. apply Lt.lt_S_n. assumption.
              assumption.
              simpl. rewrite replace_length. assumption.
        (* n0 = S n0' /\ n = 0 *)
          destruct m.
          (* m = 0 *)
            intros. inversion H1.
          (* m = S m' *)
            intros. simpl.
            rewrite IHsource with (m := m) (d1 := d1).
              destruct m; reflexivity.
              apply refpass_unique_cons in H. assumption.
              simpl in H0. apply Lt.lt_S_n. assumption.
              assumption.
              assumption.
        (* n0 = S n0' /\ n = S n' *)
          destruct m.
          (* m = 0 *)
            intros. inversion H1; subst. exfalso. apply Hnvals. reflexivity.
          (* m = S m' *)
            intros. simpl.
            rewrite IHsource with (m := m) (d1 := d1).
              destruct m; reflexivity.
              apply refpass_unique_cons in H. assumption.
              simpl in H0. apply Lt.lt_S_n. assumption.
              assumption.
              simpl. rewrite replace_length. assumption.
    (* cf = None :: cf' *)
      destruct m.
      (* m = 0 *)
        intros. inversion H1.
      (* m = S m' *)
        intros. simpl.
        rewrite IHsource with (m := m) (d1 := d1).
          destruct m; reflexivity.
          apply refpass_unique_cons in H. assumption.
          simpl in H0. apply Lt.lt_S_n. assumption.
          assumption.
          simpl. assumption.
  Qed.

Lemma push_call_length:
  forall st args,
  length (get_call_stack (push_call args st)) = S (length (get_call_stack st)) /\
  length (get_stack (push_call args st)) = S (length (get_stack st)).
Proof.
  induction st. intros. simpl.
  split; reflexivity.
  Qed.

(** Tail of [call_stack] is unchanged. *)

Lemma push_call_correct_1:
  forall st m args d1 d2,
  lt m (length (get_call_stack st)) ->
  nth (S m) (get_call_stack (push_call args st)) d1 = nth m (get_call_stack st) d2.
Proof.
  induction st. intros m tm d1 d2. simpl. intros.
  apply nth_indep. assumption.
  Qed.

(** Tail of [stack] is unchanged. *)

Lemma push_call_correct_2:
  forall st m args d1 d2,
  lt m (length (get_stack st)) ->
  nth (S m) (get_stack (push_call args st)) d1 = nth m (get_stack st) d2.
Proof.
  induction st. intros m tm d1 d2. simpl. intros.
  apply nth_indep. assumption.
  Qed.

(** Head of [call_stack] is changed. *)

Lemma push_call_correct_3:
  forall st args d,
  hd d (get_call_stack (push_call args st)) = args_to_call_frame (rc_to_list args).
Proof.
  induction st. reflexivity.
  Qed.

(** Head of [stack] is changed. *)

Lemma push_call_correct_4:
  forall st args d,
  hd d (get_stack (push_call args st)) = args_to_stack_frame (rc_to_list args) (hd nil (get_stack st)).
Proof.
  induction st. reflexivity.
  Qed.

(** [store] is unchanged. *)

Lemma push_call_correct_5:
  forall st args,
  get_store (push_call args st) = get_store st.
Proof.
  induction st. intros. reflexivity.
  Qed.

Lemma pop_call_length_1:
  forall st n,
  length (get_call_stack st) = S n ->
  length (get_call_stack (pop_call st)) = n.
Proof.
  induction st. intros n. simpl.
  destruct c. intros. inversion H.
  simpl. intros. injection H. intros. assumption.
  Qed.

Lemma pop_call_length_2:
  forall st n,
  length (get_stack st) = S (S n) ->
  length (get_stack (pop_call st)) = S n.
Proof.
  induction st. intros n. simpl.
  destruct s. simpl. intros. discriminate H.
  destruct s1. simpl. intros. discriminate H.
  simpl. intros. injection H. intros. rewrite H0. reflexivity.
  Qed.

(** Tail of [call_stack] is unchanged. *)

Lemma pop_call_correct_1:
  forall st m d1 d2,
  lt (S m) (length (get_call_stack st)) ->
  nth m (get_call_stack (pop_call st)) d1 = nth (S m) (get_call_stack st) d2.
Proof.
  induction st. intros m d1 d2. simpl.
  destruct c. intros. inversion H.
  simpl. intros. apply nth_indep. apply Lt.lt_S_n. assumption.
  Qed.

(** Tail of [stack] is unchanged. *)

Lemma pop_call_correct_2:
  forall st m d1 d2,
  lt (S (S m)) (length (get_stack st)) ->
  nth (S m) (get_stack (pop_call st)) d1 = nth (S (S m)) (get_stack st) d2.
Proof.
  induction st. intros m d1 d2. simpl.
  destruct s. intros. inversion H.
  destruct s1. intros. simpl in H. apply Lt.lt_S_n in H. inversion H.
  simpl. intros. apply nth_indep. do 2 apply Lt.lt_S_n. assumption.
  Qed.

(** Head of [stack] is changed. *)

Lemma pop_call_correct_3:
  forall st d,
  hd d (get_stack (pop_call st)) = return_refpass_args (hd nil (get_call_stack st)) (hd nil (get_stack st)) (nth 1 (get_stack st) nil).
Proof.
  induction st. reflexivity.
  Qed.

(** [store] is unchanged. *)

Lemma pop_call_correct_4:
  forall st,
  get_store (pop_call st) = get_store st.
Proof.
  induction st. reflexivity.
  Qed.

End FunctionCalls.

(** ** Stack functions *)

Definition write_sk_hd (n : nat) (a : tm) (st : state) : state :=
  set_stack (write_hd n a (get_stack st)) st.

Definition read_sk_hd (n : nat) (st : state) : tm :=
  read_hd n (get_stack st).

Definition resize_sk_hd (n : nat) (st : state) : state :=
  set_stack (resize_hd n (get_stack st)) st.

(** ** Store functions *)

Definition alloc_sr (a : tm) (st : state) : state :=
  set_store (alloc a (get_store st)) st.

Definition write_sr (n : nat) (t : tm) (st : state) : state :=
  set_store (write n t (get_store st)) st.

Definition read_sr (n : nat) (st : state) : tm :=
  read n (get_store st).

(** ** Function unfolding

    [Arguments] statement with [/] tells tactic [simpl] to unfold these
    functions when arguments before the [/] are provided [[1]].

    [[1]] #<a href="https://coq.inria.fr/distrib/8.4pl4/refman/Reference-Manual010.html##sec395">
           https://coq.inria.fr/distrib/8.4pl4/refman/Reference-Manual010.html##sec395</a># *)

Arguments get_stack st /.
Arguments get_call_stack st /.
Arguments get_store st /.
Arguments set_stack sk st /.
Arguments set_call_stack csk st /.
Arguments set_store sr st /.
Arguments args_to_call_frame args /.
Arguments args_to_stack_frame args context /.
Arguments return_refpass_args cf source target /.
Arguments push_call args st /.
Arguments pop_call st /.
Arguments write_sk_hd n a st /.
Arguments read_sk_hd n st /.
Arguments resize_sk_hd n st /.
Arguments alloc_sr a st /.
Arguments write_sr n t st /.
Arguments read_sr n st /.

(** * Constants *)

Definition init_state : state := Cstate init_stack init_call_stack init_store.

(** * Notations *)

Module StateNotations.

Notation "'\stack' sk '\call_stack' csk '\store' sr" :=
  (Cstate sk csk sr) (at level 80, format "'[' '[v  ' \stack '/' '[' sk ']' ']' '//' '[v  ' \call_stack '/' '[' csk ']' ']' '//' '[v  ' \store '/' '[' sr ']' ']' ']'") : state_scope.

End StateNotations.


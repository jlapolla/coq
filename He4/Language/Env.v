Require Export He4.Language.Record.
Require Export He4.Language.State.
Require Export He4.Language.Step.
Require Export He4.Language.StepProp.
Require Export He4.Language.Term.
Require Export He4.Language.Value.
Require Import He4.Strings.String.
Import ObjectOrientedNotations.
Delimit Scope oo_scope with oo.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39).

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39).

Ltac reduce_value :=
  match goal with
  | |- value _ => constructor
  end.

Ltac reduce_read_stack :=
  match goal with
  | |- read_sk_hd _ _ = _ => reflexivity
  end.

Ltac reduce_read_store :=
  match goal with
  | |- read_sr _ _ = _ => reflexivity
  end.

Ltac reduce_tnot :=
  match goal with
  | |- step (pair (tnot ?t) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STnot_r
    | true =>
      match t with
      | tbool _ => eapply STnot
      end
    end
  end.

Ltac reduce_tand :=
  match goal with
  | |- step (pair (tand ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STand_l
    | true =>
      match t with
      | tbool true => eapply STand_true
      | tbool false => eapply STand_false
      end
    end
  end.

Ltac reduce_tor :=
  match goal with
  | |- step (pair (tor ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STor_l
    | true =>
      match t with
      | tbool false => eapply STor_false
      | tbool true => eapply STor_true
      end
    end
  end.

Ltac reduce_tplus :=
  match goal with
  | |- step (pair (tplus ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STplus_l
    | true =>
      match eval cbv in (valueb t0) with
      | false => eapply STplus_r
      | true =>
        match eval cbv in (pair t t0) with
        | pair (tnat _) (tnat _) => eapply STplus_nat
        end
      end
    end
  end.

Ltac reduce_tminus :=
  match goal with
  | |- step (pair (tminus ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STminus_l
    | true =>
      match eval cbv in (valueb t0) with
      | false => eapply STminus_r
      | true =>
        match eval cbv in (pair t t0) with
        | pair (tnat _) (tnat _) => eapply STminus_nat
        end
      end
    end
  end.

Ltac reduce_tmult :=
  match goal with
  | |- step (pair (tmult ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STmult_l
    | true =>
      match eval cbv in (valueb t0) with
      | false => eapply STmult_r
      | true =>
        match eval cbv in (pair t t0) with
        | pair (tnat _) (tnat _) => eapply STmult_nat
        end
      end
    end
  end.

Ltac reduce_teq :=
  match goal with
  | |- step (pair (teq ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STeq_l
    | true =>
      match eval cbv in (valueb t0) with
      | false => eapply STeq_r
      | true =>
        match eval cbv in (pair t t0) with
        | pair tvoid tvoid => eapply STeq_void
        | pair (tnat _) (tnat _) => eapply STeq_nat
        | pair (tbool _) (tbool _) => eapply STeq_bool
        | pair (tref _) (tref _) => eapply STeq_ref
        | pair (trc _ _) (trc _ _) => eapply STeq_rc
        | pair (tcl _ _) (tcl _ _) => eapply STeq_cl
        end
      end
    end
  end.

Ltac reduce_tvar :=
  match goal with
  | |- step (pair (tvar _) _) _ => eapply STvar
  end.

Ltac reduce_tassign :=
  match goal with
  | |- step (pair (tassign (tvar _) ?t0) _) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STassign_r
    | true => eapply STassign
    end
  end.

Ltac reduce_tseq :=
  match goal with
  | |- step (pair (tseq ?t _) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STseq_l
    | true => eapply STseq
    end
  end.

Ltac reduce_tif :=
  match goal with
  | |- step (pair (tif ?t _ _) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STif_l
    | true =>
      match t with
      | tbool false => eapply STif_false
      | tbool true => eapply STif_true
      end
    end
  end.

Ltac reduce_twhile :=
  match goal with
  | |- step (pair (twhile _ _) _) _ => eapply STwhile
  end.

Ltac reduce_trc :=
  match goal with
  | |- step (pair (trc ?t ?t0) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STrc_l
    | true =>
      match eval cbv in (valueb t0) with
      | false => eapply STrc_r
      end
    end
  end.

Ltac reduce_tcall :=
  match goal with
  | |- step (pair (tcall _ ?t0) _) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STcall_r
    | true => eapply STcall
    end
  end.

Ltac reduce_treturn :=
  match goal with
  | |- step (pair (treturn ?t) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STreturn_r
    | true => eapply STreturn
    end
  end.

Ltac reduce_tcl :=
  match goal with
  | |- step (pair (tcl _ ?t) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STcl_r
    end
  end.

Ltac reduce_tnew :=
  match goal with
  | |- step (pair (tnew _ _) _) _ => eapply STnew
  end.

Ltac reduce_tfield_r :=
  match goal with
  | |- step (pair (tfield_r _ ?t0) ?st) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STfield_r_r
    | true =>
      match t0 with
      | tref ?n0 =>
        match eval cbv in (read_sr n0 st) with
        | tcl _ _ => eapply STfield_r
        end
      end
    end
  end.

Ltac reduce_tfield_w :=
  match goal with
  | |- step (pair (tfield_w _ ?t0 ?t1) ?st) _ =>
    match eval cbv in (valueb t1) with
    | false => eapply STfield_w_r
    | true =>
      match eval cbv in (valueb t0) with
      | false => eapply STfield_w_l
      | true =>
        match t1 with
        | tref ?n0 =>
          match eval cbv in (read_sr n0 st) with
          | tcl _ _ => eapply STfield_w
          end
        end
      end
    end
  end.

Ltac reduce_tvnew :=
  match goal with
  | |- step (pair (tvnew _ _) _) _ => eapply STvnew
  end.

Ltac reduce_tvfield_r :=
  match goal with
  | |- step (pair (tvfield_r _ ?t0) ?st) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STvfield_r_r
    | true =>
      match t0 with
      | tcl _ _ => eapply STvfield_r
      end
    end
  end.

Ltac reduce_step :=
     reduce_value
  || reduce_read_stack
  || reduce_read_store
  || reduce_tnot
  || reduce_tand
  || reduce_tor
  || reduce_tplus
  || reduce_tminus
  || reduce_tmult
  || reduce_teq
  || reduce_tvar
  || reduce_tassign
  || reduce_tseq
  || reduce_tif
  || reduce_twhile
  || reduce_trc
  || reduce_tcall
  || reduce_treturn
  || reduce_tcl
  || reduce_tnew
  || reduce_tfield_r
  || reduce_tfield_w
  || reduce_tvnew
  || reduce_tvfield_r
.

Ltac reduce :=
  match goal with
  | |- multi step ?t ?t => apply Relation_Operators.rt1n_refl
  | |- multi step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [repeat reduce_step | instantiate; simpl; fold multi]
  end.

Section Examples.

Let ex_reduce_tnot_tm := ((
    !!tbool true
  )%oo).
Let ex_reduce_tnot:
  forall st,
  ex_reduce_tnot_tm / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_tnot_tm. intros. repeat reduce. Qed.

Let ex_reduce_tand_tm := ((
    !tbool false \&& !tbool true \&& tbool true
  )%oo).
Let ex_reduce_tand:
  forall st,
  ex_reduce_tand_tm / st ==>* tbool false / st.
Proof.
  unfold ex_reduce_tand_tm. intros. repeat reduce. Qed.

Let ex_reduce_tor_tm := ((
    !tbool true \|| !tbool false \|| tbool false
  )%oo).
Let ex_reduce_tor:
  forall st,
  ex_reduce_tor_tm / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_tor_tm. intros. repeat reduce. Qed.

Let ex_reduce_tplus_tm := ((
    (tnat 3 \+ tnat 4) \+ (tnat 5 \+ tnat 6)
  )%oo).
Let ex_reduce_tplus:
  forall st,
  ex_reduce_tplus_tm / st ==>* tnat 18 / st.
Proof.
  unfold ex_reduce_tplus_tm. intros. repeat reduce. Qed.

Let ex_reduce_tminus_tm := ((
    (tnat 3 \+ tnat 4) \- (tnat 1 \+ tnat 2)
  )%oo).
Let ex_reduce_tminus:
  forall st,
  ex_reduce_tminus_tm / st ==>* tnat 4 / st.
Proof.
  unfold ex_reduce_tminus_tm. intros. repeat reduce. Qed.

Let ex_reduce_tmult_tm := ((
    (tnat 3 \+ tnat 4) \* (tnat 1 \+ tnat 2)
  )%oo).
Let ex_reduce_tmult:
  forall st,
  ex_reduce_tmult_tm / st ==>* tnat 21 / st.
Proof.
  unfold ex_reduce_tmult_tm. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_1 := ((
    !tbool true == !tbool false
  )%oo).
Let ex_reduce_teq_1:
  forall st,
  ex_reduce_teq_tm_1 / st ==>* tbool false / st.
Proof.
  unfold ex_reduce_teq_tm_1. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_2 := ((
    tvoid == tvoid
  )%oo).
Let ex_reduce_teq_2:
  forall st,
  ex_reduce_teq_tm_2 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_2. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_3 := ((
    tnat 0 == tnat 0
  )%oo).
Let ex_reduce_teq_3:
  forall st,
  ex_reduce_teq_tm_3 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_3. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_4 := ((
    tbool true == tbool true
  )%oo).
Let ex_reduce_teq_4:
  forall st,
  ex_reduce_teq_tm_4 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_4. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_5 := ((
    tref 0 == tref 0
  )%oo).
Let ex_reduce_teq_5:
  forall st,
  ex_reduce_teq_tm_5 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_5. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_6 := ((
    trc (tbool true) tvoid == trc (tbool true) tvoid
  )%oo).
Let ex_reduce_teq_6:
  forall st,
  ex_reduce_teq_tm_6 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_6. intros. repeat reduce. Qed.

Let ex_reduce_teq_tm_7 := ((
    tcl "Foo" tvoid == tcl "Foo" tvoid
  )%oo).
Let ex_reduce_teq_7:
  forall st,
  ex_reduce_teq_tm_7 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_7. intros. repeat reduce. Qed.

Let ex_reduce_tvar_tm := ((
    tvar 0
  )%oo).
Let ex_reduce_tvar:
  let st := write_sk_hd 0 (tbool true) (resize_sk_hd 1 init_state) in
  ex_reduce_tvar_tm / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_tvar_tm. repeat reduce. Qed.

Let ex_reduce_tassign_tm := ((
    tvar 0 ::= tnat 1 \+ tnat 1
  )%oo).
Let ex_reduce_tassign:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  ex_reduce_tassign_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_reduce_tassign_tm. repeat reduce. Qed.

Let ex_reduce_tseq_tm := ((
    tvar 0 ::= tnat 1 \+ tnat 1;
    tnat 3 \+ tvar 0
  )%oo).
Let ex_reduce_tseq:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  ex_reduce_tseq_tm / st ==>* tnat 5 / st'.
Proof.
  unfold ex_reduce_tseq_tm. repeat reduce. Qed.

Let ex_reduce_tif_tm := ((
    \if !tbool true
    \then
      tnat 1
    \else
      \if tbool true
      \then
        tnat 2
      \else
        tnat 3
      \fi
    \fi
  )%oo).
Let ex_reduce_tif:
  forall st,
  ex_reduce_tif_tm / st ==>* tnat 2 / st.
Proof.
  unfold ex_reduce_tif_tm. intros. repeat reduce. Qed.

Let ex_reduce_twhile_tm := (
  let x := tvar 1 in
  let y := tvar 2 in
  (
    y ::= tnat 1;
    \while !(x == tnat 0)
    \do
      y ::= x \* y;
      x ::= x \- tnat 1
    \done;
    y
  )%oo).
Let ex_reduce_twhile:
  let st := write_sk_hd 1 (tnat 3) (resize_sk_hd 3 init_state) in
  let st' := write_sk_hd 1 (tnat 0) (write_sk_hd 2 (tnat 6) st) in
  ex_reduce_twhile_tm / st ==>* tnat 6 / st'.
Proof.
  unfold ex_reduce_twhile_tm. repeat reduce. Qed.

Let ex_reduce_trc_tm := list_to_rc (cons (tnat 1 \+ tnat 2)%oo (cons (tnat 3 \+ tnat 4)%oo nil)).
Let ex_reduce_trc:
  forall st,
  ex_reduce_trc_tm / st ==>* list_to_rc (cons (tnat 3) (cons (tnat 7) nil)) / st.
Proof.
  unfold ex_reduce_trc_tm. intros. simpl. repeat reduce. Qed.

Let ex_reduce_tcall_tm := ((
    tcall "foo" (|(tnat 1 \+ tnat 1)|)
  )%oo).
Let ex_reduce_tcall:
  forall st,
  ex_reduce_tcall_tm / st ==>* treturn (texec "foo") / push_sf (cons (tnat 2) nil) st.
Proof.
  unfold ex_reduce_tcall_tm. intros. simpl. repeat reduce. Qed.

Let ex_reduce_treturn_tm := ((
    treturn (tnat 1 \+ tnat 1)
  )%oo).
Let ex_reduce_treturn:
  forall st,
  ex_reduce_treturn_tm / st ==>* tnat 2 / pop_sf st.
Proof.
  unfold ex_reduce_treturn_tm. intros. repeat reduce. Qed.

Let ex_reduce_tcl_tm := ((
    tcl "foo" (|(tnat 1 \+ tnat 1)|)
  )%oo).
Let ex_reduce_tcl:
  forall st,
  ex_reduce_tcl_tm / st ==>* tcl "foo" (trc (tnat 2) tvoid) / st.
Proof.
  unfold ex_reduce_tcl_tm. intros. repeat reduce. Qed.

Let ex_reduce_tnew_tm := ((
    tnew 2 "foo"
  )%oo).
Let ex_reduce_tnew:
  ex_reduce_tnew_tm / init_state ==>* tref 1 / alloc_sr (tcl "foo" (|(tvoid, tvoid)|))%oo init_state.
Proof.
  unfold ex_reduce_tnew_tm. repeat reduce. Qed.

Let ex_reduce_tfield_r_tm := ((
    (treturn (tref 1))@2
  )%oo).
Let ex_reduce_tfield_r:
  let st := push_sf nil (alloc_sr (tcl "foo" (|(tvoid, tnat 1, tnat 2)|))%oo init_state) in
  let st' := pop_sf st in
  ex_reduce_tfield_r_tm / st ==>* tnat 2 / st'.
Proof.
  unfold ex_reduce_tfield_r_tm. repeat reduce. Qed.

Let ex_reduce_tfield_w_tm := ((
    (treturn (tref 1)) <@ 1 <- (tnat 1 \+ tnat 1)
  )%oo).
Let ex_reduce_tfield_w:
  let st := push_sf nil (alloc_sr (tcl "foo" (|(tvoid, tvoid)|))%oo init_state) in
  let st' := write_sr 1 (tcl "foo" (|(tvoid, tnat 2)|))%oo (pop_sf st) in
  ex_reduce_tfield_w_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_reduce_tfield_w_tm. repeat reduce. Qed.

Let ex_reduce_tvnew_tm := ((
    tvnew 2 "foo"
  )%oo).
Let ex_reduce_tvnew:
  forall st,
  ex_reduce_tvnew_tm / st ==>* (tcl "foo" (|(tvoid, tvoid)|))%oo / st.
Proof.
  unfold ex_reduce_tvnew_tm. intros. repeat reduce. Qed.

Let ex_reduce_tvfield_r_tm := ((
    tcl "foo" (|(tvoid, tnat 1, tnat 1 \+ tnat 1)|)?@2
  )%oo).
Let ex_reduce_tvfield_r:
  forall st,
  ex_reduce_tvfield_r_tm / st ==>* tnat 2 / st.
Proof.
  unfold ex_reduce_tvfield_r_tm. intros. repeat reduce. Qed.

(*
Let ex_reduce_tvfield_w_tm := ((
    (tvar 0) <?@ 1 <- (tnat 1 \+ tnat 1)
  )%oo).
Let ex_reduce_tvfield_w:
  let st := write_sk_hd 0 (tcl "foo" (|(tvoid, tvoid)|))%oo (resize_sk_hd 1 init_state) in
  let st' := write_sk_hd 0 (tcl "foo" (|(tvoid, tnat 2)|))%oo st in
  ex_reduce_tvfield_w_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_reduce_tvfield_w_tm. repeat reduce. Qed.
*)

End Examples.

Definition main : tm := (
  let x := tvar 1 in
  let y := tvar 2 in
  (
    x ::= tnat 1 \+ tnat 2;
    y ::= tnat 1;
    \while !(x == tnat 0)
    \do
      y ::= x \* y;
      x ::= x \- tnat 1
    \done;
    y
  )%oo).


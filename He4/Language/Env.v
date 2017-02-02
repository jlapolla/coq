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
  | |- step (pair (trc ?t ?t0) _) _ => fail (* TODO *)
  end.

Ltac reduce_tcall :=
  match goal with
  | |- step (pair (tcall _ ?t0) _) _ => fail (* TODO *)
  end.

Ltac reduce_treturn :=
  match goal with
  | |- step (pair (treturn ?t) _) _ => fail (* TODO *)
  end.

Ltac reduce_tcl :=
  match goal with
  | |- step (pair (tcl _ ?t) _) _ => fail (* TODO *)
  end.

Ltac reduce_tnew :=
  match goal with
  | |- step (pair (tnew _ _) _) _ => eapply STnew
  end.

Ltac reduce_step :=
     reduce_value
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


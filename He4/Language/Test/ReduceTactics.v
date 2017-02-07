Require Import He4.Language.Record.
Require Import He4.Language.State.
Require Import He4.Language.Step.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.Value.
Require Import He4.Strings.String.
Require Import He4.Language.ReduceTactics.
Import ObjectOrientedNotations.
Delimit Scope oo_scope with oo.
Import StateNotations.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Section Examples.
Open Scope state_scope.

Definition ex_reduce_tnot_tm := ((
    !!tbool true
  )%oo).
Example ex_reduce_tnot:
  forall st,
  ex_reduce_tnot_tm / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_tnot_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tand_tm := ((
    !tbool false \&& !tbool true \&& tbool true
  )%oo).
Example ex_reduce_tand:
  forall st,
  ex_reduce_tand_tm / st ==>* tbool false / st.
Proof.
  unfold ex_reduce_tand_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tor_tm := ((
    !tbool true \|| !tbool false \|| tbool false
  )%oo).
Example ex_reduce_tor:
  forall st,
  ex_reduce_tor_tm / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_tor_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tplus_tm := ((
    (tnat 3 \+ tnat 4) \+ (tnat 5 \+ tnat 6)
  )%oo).
Example ex_reduce_tplus:
  forall st,
  ex_reduce_tplus_tm / st ==>* tnat 18 / st.
Proof.
  unfold ex_reduce_tplus_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tminus_tm := ((
    (tnat 3 \+ tnat 4) \- (tnat 1 \+ tnat 2)
  )%oo).
Example ex_reduce_tminus:
  forall st,
  ex_reduce_tminus_tm / st ==>* tnat 4 / st.
Proof.
  unfold ex_reduce_tminus_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tmult_tm := ((
    (tnat 3 \+ tnat 4) \* (tnat 1 \+ tnat 2)
  )%oo).
Example ex_reduce_tmult:
  forall st,
  ex_reduce_tmult_tm / st ==>* tnat 21 / st.
Proof.
  unfold ex_reduce_tmult_tm. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_1 := ((
    !tbool true \== !tbool false
  )%oo).
Example ex_reduce_teq_1:
  forall st,
  ex_reduce_teq_tm_1 / st ==>* tbool false / st.
Proof.
  unfold ex_reduce_teq_tm_1. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_2 := ((
    tvoid \== tvoid
  )%oo).
Example ex_reduce_teq_2:
  forall st,
  ex_reduce_teq_tm_2 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_2. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_3 := ((
    tnat 0 \== tnat 0
  )%oo).
Example ex_reduce_teq_3:
  forall st,
  ex_reduce_teq_tm_3 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_3. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_4 := ((
    tbool true \== tbool true
  )%oo).
Example ex_reduce_teq_4:
  forall st,
  ex_reduce_teq_tm_4 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_4. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_5 := ((
    tref 0 \== tref 0
  )%oo).
Example ex_reduce_teq_5:
  forall st,
  ex_reduce_teq_tm_5 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_5. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_6 := ((
    trc (tbool true) tvoid \== trc (tbool true) tvoid
  )%oo).
Example ex_reduce_teq_6:
  forall st,
  ex_reduce_teq_tm_6 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_6. intros. repeat reduce. Qed.

Definition ex_reduce_teq_tm_7 := ((
    tcl "Foo" tvoid \== tcl "Foo" tvoid
  )%oo).
Example ex_reduce_teq_7:
  forall st,
  ex_reduce_teq_tm_7 / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_teq_tm_7. intros. repeat reduce. Qed.

Definition ex_reduce_tvar_tm := ((
    tvar 0
  )%oo).
Example ex_reduce_tvar:
  let st := write_sk_hd 0 (tbool true) (resize_sk_hd 1 init_state) in
  ex_reduce_tvar_tm / st ==>* tbool true / st.
Proof.
  unfold ex_reduce_tvar_tm. repeat reduce. Qed.

Definition ex_reduce_tassign_tm := ((
    tvar 0 ::= tnat 1 \+ tnat 1
  )%oo).
Example ex_reduce_tassign:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  ex_reduce_tassign_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_reduce_tassign_tm. repeat reduce. Qed.

Definition ex_reduce_tseq_tm := ((
    tvar 0 ::= tnat 1 \+ tnat 1;
    tnat 3 \+ tvar 0
  )%oo).
Example ex_reduce_tseq:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  ex_reduce_tseq_tm / st ==>* tnat 5 / st'.
Proof.
  unfold ex_reduce_tseq_tm. repeat reduce. Qed.

Definition ex_reduce_tif_tm := ((
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
Example ex_reduce_tif:
  forall st,
  ex_reduce_tif_tm / st ==>* tnat 2 / st.
Proof.
  unfold ex_reduce_tif_tm. intros. repeat reduce. Qed.

Definition ex_reduce_twhile_tm := (
  let x := tvar 1 in
  let y := tvar 2 in
  (
    y ::= tnat 1;
    \while !(x \== tnat 0)
    \do
      y ::= x \* y;
      x ::= x \- tnat 1
    \done;
    y
  )%oo).
Example ex_reduce_twhile:
  let st := write_sk_hd 1 (tnat 3) (resize_sk_hd 3 init_state) in
  let st' := write_sk_hd 1 (tnat 0) (write_sk_hd 2 (tnat 6) st) in
  ex_reduce_twhile_tm / st ==>* tnat 6 / st'.
Proof.
  unfold ex_reduce_twhile_tm. repeat reduce. Qed.

Definition ex_reduce_trc_tm := list_to_rc (cons (tnat 1 \+ tnat 2)%oo (cons (tnat 3 \+ tnat 4)%oo nil)).
Example ex_reduce_trc:
  forall st,
  ex_reduce_trc_tm / st ==>* list_to_rc (cons (tnat 3) (cons (tnat 7) nil)) / st.
Proof.
  unfold ex_reduce_trc_tm. intros. simpl. repeat reduce. Qed.

Definition ex_reduce_tcall_tm := ((
    tcall "foo" (<(tnat 1 \+ tnat 1)>)
  )%oo).
Example ex_reduce_tcall:
  forall st,
  ex_reduce_tcall_tm / st ==>* treturn (texec "foo") / push_call (trc (tnat 2) tvoid) st.
Proof.
  unfold ex_reduce_tcall_tm. intros. simpl. repeat reduce. Qed.

Definition ex_reduce_treturn_tm := ((
    treturn (tnat 1 \+ tnat 1)
  )%oo).
Example ex_reduce_treturn:
  forall st,
  ex_reduce_treturn_tm / st ==>* tnat 2 / pop_call st.
Proof.
  unfold ex_reduce_treturn_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tcl_tm := ((
    tcl "foo" (<(tnat 1 \+ tnat 1)>)
  )%oo).
Example ex_reduce_tcl:
  forall st,
  ex_reduce_tcl_tm / st ==>* tcl "foo" (trc (tnat 2) tvoid) / st.
Proof.
  unfold ex_reduce_tcl_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tnew_tm := ((
    tnew 2 "foo"
  )%oo).
Example ex_reduce_tnew:
  ex_reduce_tnew_tm / init_state ==>* tref 1 / alloc_sr (tcl "foo" (<(tvoid, tvoid)>))%oo init_state.
Proof.
  unfold ex_reduce_tnew_tm. repeat reduce. Qed.

Definition ex_reduce_tfield_r_tm := ((
    (treturn (tref 1))@2
  )%oo).
Example ex_reduce_tfield_r:
  let st := push_call tvoid (alloc_sr (tcl "foo" (<(tvoid, tnat 1, tnat 2)>))%oo init_state) in
  let st' := pop_call st in
  ex_reduce_tfield_r_tm / st ==>* tnat 2 / st'.
Proof.
  unfold ex_reduce_tfield_r_tm. repeat reduce. Qed.

Definition ex_reduce_tfield_w_tm := ((
    (treturn (tref 1)) <@ 1 <- (tnat 1 \+ tnat 1)
  )%oo).
Example ex_reduce_tfield_w:
  let st := push_call tvoid (alloc_sr (tcl "foo" (<(tvoid, tvoid)>))%oo init_state) in
  let st' := write_sr 1 (tcl "foo" (<(tvoid, tnat 2)>))%oo (pop_call st) in
  ex_reduce_tfield_w_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_reduce_tfield_w_tm. repeat reduce. Qed.

Definition ex_reduce_tvnew_tm := ((
    tvnew 2 "foo"
  )%oo).
Example ex_reduce_tvnew:
  forall st,
  ex_reduce_tvnew_tm / st ==>* (tcl "foo" (<(tvoid, tvoid)>))%oo / st.
Proof.
  unfold ex_reduce_tvnew_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tvfield_r_tm := ((
    tcl "foo" (<(tvoid, tnat 1, tnat 1 \+ tnat 1)>)?@2
  )%oo).
Example ex_reduce_tvfield_r:
  forall st,
  ex_reduce_tvfield_r_tm / st ==>* tnat 2 / st.
Proof.
  unfold ex_reduce_tvfield_r_tm. intros. repeat reduce. Qed.

Definition ex_reduce_tvfield_w_tm := ((
    (tvar 0) <?@ 1 <- (tnat 1 \+ tnat 1)
  )%oo).
Example ex_reduce_tvfield_w:
  let st := write_sk_hd 0 (tcl "foo" (<(tvoid, tvoid)>))%oo (resize_sk_hd 1 init_state) in
  let st' := write_sk_hd 0 (tcl "foo" (<(tvoid, tnat 2)>))%oo st in
  ex_reduce_tvfield_w_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_reduce_tvfield_w_tm. repeat reduce. Qed.

End Examples.

Definition main : tm := (
  let x := tvar 1 in
  let y := tvar 2 in
  (
    x ::= tnat 1 \+ tnat 2;
    y ::= tnat 1;
    \while !(x \== tnat 0)
    \do
      y ::= x \* y;
      x ::= x \- tnat 1
    \done;
    y
  )%oo).


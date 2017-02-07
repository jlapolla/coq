Require Import He4.Language.State.
Require Import He4.Language.Step.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.ReduceTactics.
Import ObjectOrientedNotations.
Import StateNotations.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Section Examples.
Open Scope oo_scope.
Open Scope state_scope.

Definition ex_tnot_tm := !!tbool true.
Example ex_tnot:
  forall st,
  ex_tnot_tm / st ==>* tbool true / st.
Proof.
  unfold ex_tnot_tm. intros. repeat reduce. Qed.

Definition ex_tand_tm := !tbool false \&& !tbool true \&& tbool true.
Example ex_tand:
  forall st,
  ex_tand_tm / st ==>* tbool false / st.
Proof.
  unfold ex_tand_tm. intros. repeat reduce. Qed.

Definition ex_tor_tm := !tbool true \|| !tbool false \|| tbool false.
Example ex_tor:
  forall st,
  ex_tor_tm / st ==>* tbool true / st.
Proof.
  unfold ex_tor_tm. intros. repeat reduce. Qed.

Definition ex_tplus_tm := (tnat 3 \+ tnat 4) \+ (tnat 5 \+ tnat 6).
Example ex_tplus:
  forall st,
  ex_tplus_tm / st ==>* tnat 18 / st.
Proof.
  unfold ex_tplus_tm. intros. repeat reduce. Qed.

Definition ex_tminus_tm := (tnat 3 \+ tnat 4) \- (tnat 1 \+ tnat 2).
Example ex_tminus:
  forall st,
  ex_tminus_tm / st ==>* tnat 4 / st.
Proof.
  unfold ex_tminus_tm. intros. repeat reduce. Qed.

Definition ex_tmult_tm := (tnat 3 \+ tnat 4) \* (tnat 1 \+ tnat 2).
Example ex_tmult:
  forall st,
  ex_tmult_tm / st ==>* tnat 21 / st.
Proof.
  unfold ex_tmult_tm. intros. repeat reduce. Qed.

Definition ex_teq_tm_1 := !tbool true \== !tbool false.
Example ex_teq_1:
  forall st,
  ex_teq_tm_1 / st ==>* tbool false / st.
Proof.
  unfold ex_teq_tm_1. intros. repeat reduce. Qed.

Definition ex_teq_tm_2 := tvoid \== tvoid.
Example ex_teq_2:
  forall st,
  ex_teq_tm_2 / st ==>* tbool true / st.
Proof.
  unfold ex_teq_tm_2. intros. repeat reduce. Qed.

Definition ex_teq_tm_3 := tnat 0 \== tnat 0.
Example ex_teq_3:
  forall st,
  ex_teq_tm_3 / st ==>* tbool true / st.
Proof.
  unfold ex_teq_tm_3. intros. repeat reduce. Qed.

Definition ex_teq_tm_4 := tbool true \== tbool true.
Example ex_teq_4:
  forall st,
  ex_teq_tm_4 / st ==>* tbool true / st.
Proof.
  unfold ex_teq_tm_4. intros. repeat reduce. Qed.

Definition ex_teq_tm_5 := tref 0 \== tref 0.
Example ex_teq_5:
  forall st,
  ex_teq_tm_5 / st ==>* tbool true / st.
Proof.
  unfold ex_teq_tm_5. intros. repeat reduce. Qed.

Definition ex_teq_tm_6 := trc (tbool true) tvoid \== trc (tbool true) tvoid.
Example ex_teq_6:
  forall st,
  ex_teq_tm_6 / st ==>* tbool true / st.
Proof.
  unfold ex_teq_tm_6. intros. repeat reduce. Qed.

Definition ex_teq_tm_7 := tcl "Foo" tvoid \== tcl "Foo" tvoid.
Example ex_teq_7:
  forall st,
  ex_teq_tm_7 / st ==>* tbool true / st.
Proof.
  unfold ex_teq_tm_7. intros. repeat reduce. Qed.

Definition ex_tvar_tm := tvar 0.
Example ex_tvar:
  let st := write_sk_hd 0 (tbool true) (resize_sk_hd 1 init_state) in
  ex_tvar_tm / st ==>* tbool true / st.
Proof.
  unfold ex_tvar_tm. repeat reduce. Qed.

Definition ex_tassign_tm := tvar 0 ::= tnat 1 \+ tnat 1.
Example ex_tassign:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  ex_tassign_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_tassign_tm. repeat reduce. Qed.

Definition ex_tseq_tm :=
    tvar 0 ::= tnat 1 \+ tnat 1;
    tnat 3 \+ tvar 0.
Example ex_tseq:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  ex_tseq_tm / st ==>* tnat 5 / st'.
Proof.
  unfold ex_tseq_tm. repeat reduce. Qed.

Definition ex_tif_tm :=
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
    \fi.
Example ex_tif:
  forall st,
  ex_tif_tm / st ==>* tnat 2 / st.
Proof.
  unfold ex_tif_tm. intros. repeat reduce. Qed.

Definition ex_twhile_tm :=
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
  ).
Example ex_twhile:
  let st := write_sk_hd 1 (tnat 3) (resize_sk_hd 3 init_state) in
  let st' := write_sk_hd 1 (tnat 0) (write_sk_hd 2 (tnat 6) st) in
  ex_twhile_tm / st ==>* tnat 6 / st'.
Proof.
  unfold ex_twhile_tm. repeat reduce. Qed.

Definition ex_trc_tm := <(tnat 1 \+ tnat 2, tnat 3 \+ tnat 4)>.
Example ex_trc:
  forall st,
  ex_trc_tm / st ==>* <(tnat 3, tnat 7)> / st.
Proof.
  unfold ex_trc_tm. intros. simpl. repeat reduce. Qed.

Definition ex_tcall_tm := tcall "foo" (<(tnat 1 \+ tnat 1)>).
Example ex_tcall:
  forall st,
  ex_tcall_tm / st ==>* treturn (texec "foo") / push_call (trc (tnat 2) tvoid) st.
Proof.
  unfold ex_tcall_tm. intros. simpl. repeat reduce. Qed.

Definition ex_treturn_tm := treturn (tnat 1 \+ tnat 1).
Example ex_treturn:
  forall st,
  ex_treturn_tm / st ==>* tnat 2 / pop_call st.
Proof.
  unfold ex_treturn_tm. intros. repeat reduce. Qed.

Definition ex_tcl_tm := tcl "foo" (<(tnat 1 \+ tnat 1)>).
Example ex_tcl:
  forall st,
  ex_tcl_tm / st ==>* tcl "foo" (trc (tnat 2) tvoid) / st.
Proof.
  unfold ex_tcl_tm. intros. repeat reduce. Qed.

Definition ex_tnew_tm := tnew 2 "foo".
Example ex_tnew:
  ex_tnew_tm / init_state ==>* tref 1 / alloc_sr (tcl "foo" (<(tvoid, tvoid)>)) init_state.
Proof.
  unfold ex_tnew_tm. repeat reduce. Qed.

Definition ex_tfield_r_tm := (treturn (tref 1))@2.
Example ex_tfield_r:
  let st := push_call tvoid (alloc_sr (tcl "foo" (<(tvoid, tnat 1, tnat 2)>)) init_state) in
  let st' := pop_call st in
  ex_tfield_r_tm / st ==>* tnat 2 / st'.
Proof.
  unfold ex_tfield_r_tm. repeat reduce. Qed.

Definition ex_tfield_w_tm := (treturn (tref 1)) <@ 1 <- (tnat 1 \+ tnat 1).
Example ex_tfield_w:
  let st := push_call tvoid (alloc_sr (tcl "foo" (<(tvoid, tvoid)>)) init_state) in
  let st' := write_sr 1 (tcl "foo" (<(tvoid, tnat 2)>)) (pop_call st) in
  ex_tfield_w_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_tfield_w_tm. repeat reduce. Qed.

Definition ex_tvnew_tm := tvnew 2 "foo".
Example ex_tvnew:
  forall st,
  ex_tvnew_tm / st ==>* (tcl "foo" (<(tvoid, tvoid)>)) / st.
Proof.
  unfold ex_tvnew_tm. intros. repeat reduce. Qed.

Definition ex_tvfield_r_tm := tcl "foo" (<(tvoid, tnat 1, tnat 1 \+ tnat 1)>)?@2.
Example ex_tvfield_r:
  forall st,
  ex_tvfield_r_tm / st ==>* tnat 2 / st.
Proof.
  unfold ex_tvfield_r_tm. intros. repeat reduce. Qed.

Definition ex_tvfield_w_tm := (tvar 0) <?@ 1 <- (tnat 1 \+ tnat 1).
Example ex_tvfield_w:
  let st := write_sk_hd 0 (tcl "foo" (<(tvoid, tvoid)>)) (resize_sk_hd 1 init_state) in
  let st' := write_sk_hd 0 (tcl "foo" (<(tvoid, tnat 2)>)) st in
  ex_tvfield_w_tm / st ==>* tvoid / st'.
Proof.
  unfold ex_tvfield_w_tm. repeat reduce. Qed.

End Examples.


Require Import He4.Language.State.
Require Import He4.Language.Execution.
Require Import He4.Language.ExecutionProp.
Require Import He4.Language.Syntax.
Require Import He4.Language.ReduceTactics.
Import ObjectOrientedNotations.
Import StateNotations.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>' '//' t2 '//' / '//' st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'//' '[' t1 '//' / '//' st1 '//' '==>*' '//' t2 '//' / '//' st2 ']'").

Section Examples.
Open Scope oo_scope.
Open Scope state_scope.

Ltac rewrite_nth :=
  match goal with
  | H: List.nth ?n ?sf tvoid = _ |- context [List.nth ?n ?sf tvoid] => rewrite H
  end.

Ltac reduce :=
  match goal with
  | |- multi exec_step _ _ => solve [apply Relation_Operators.rt1n_refl]
  | |- multi exec_step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [repeat reduce_exec_step | instantiate; simpl; repeat rewrite_nth; fold multi]
  end.

Example ex_tnot:
  forall st,
  (!!tbool true) / st ==>* (tbool true) / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tand:
  forall st,
  (!tbool false \&& !tbool true \&& tbool true) / st ==>* tbool false / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tor:
  forall st,
  (!tbool true \|| !tbool false \|| tbool false) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tplus:
  forall st,
  ((tnat 3 \+ tnat 4) \+ (tnat 5 \+ tnat 6)) / st ==>* tnat 18 / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tminus:
  forall st,
  ((tnat 3 \+ tnat 4) \- (tnat 1 \+ tnat 2)) / st ==>* tnat 4 / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tmult:
  forall st,
  ((tnat 3 \+ tnat 4) \* (tnat 1 \+ tnat 2)) / st ==>* tnat 21 / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_1:
  forall st,
  (!tbool true \== !tbool false) / st ==>* tbool false / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_2:
  forall st,
  (tvoid \== tvoid) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_3:
  forall st,
  (tnat 0 \== tnat 0) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_4:
  forall st,
  (tbool true \== tbool true) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_5:
  forall st,
  (tref 0 \== tref 0) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_6:
  forall st,
  (<(tbool true)> \== <(tbool true)>) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_teq_7:
  forall st,
  (tcl "Foo" tvoid \== tcl "Foo" tvoid) / st ==>* tbool true / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tvar:
  let st := write_sk_hd 0 (tbool true) (resize_sk_hd 1 init_state) in
  tvar 0 / st ==>* tbool true / st.
Proof.
  simpl. repeat reduce. Qed.

Example ex_tassign:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
  (tvar 0 ::= tnat 1 \+ tnat 1) / st ==>* tvoid / st'.
Proof.
  simpl. repeat reduce. Qed.

Example ex_tseq:
  let st := resize_sk_hd 1 init_state in
  let st' := write_sk_hd 0 (tnat 2) st in
    (
      tvar 0 ::= tnat 1 \+ tnat 1;
      tnat 3 \+ tvar 0
    ) / st
    ==>*
    tnat 5 / st'.
Proof.
  simpl. repeat reduce. Qed.

Example ex_tif:
  forall st,
  (
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
  ) / st
  ==>*
  tnat 2 / st.
Proof.
  simpl. intros st. repeat reduce. Qed.

Example ex_twhile:
  let st := write_sk_hd 1 (tnat 3) (resize_sk_hd 3 init_state) in
  let st' := write_sk_hd 1 (tnat 0) (write_sk_hd 2 (tnat 6) st) in
  (
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
    )
  ) / st
  ==>*
  tnat 6 / st'.
Proof.
  simpl. repeat reduce. Qed.

Example ex_trc:
  forall st,
  (<(tnat 1 \+ tnat 2, tnat 3 \+ tnat 4)>) / st ==>* <(tnat 3, tnat 7)> / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tcall:
  forall st,
  ((tnat 1 \+ tnat 1) # "foo"|()|)
  /
  st
  ==>*
  treturn (texec "foo") / push_call <(tnat 2)> st.
Proof.
  intros st. simpl. repeat reduce. Qed.

Example ex_treturn:
  forall st,
  (treturn (tnat 1 \+ tnat 1)) / st ==>* tnat 2 / pop_call st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tcl:
  forall st,
  (tcl "foo" (<(tnat 1 \+ tnat 1)>)) / st ==>* tcl "foo" (trc (tnat 2) tvoid) / st.
Proof.
  intros st. repeat reduce. Qed.

Example ex_tnew:
  (tnew 2 "foo") / init_state ==>* tref 1 / alloc_sr (tcl "foo" (<(tvoid, tvoid)>)) init_state.
Proof.
  simpl. repeat reduce. Qed.

Example ex_tfield_r:
  let st := push_call tvoid (alloc_sr (tcl "foo" (<(tvoid, tnat 1, tnat 2)>)) init_state) in
  let st' := pop_call st in
  ((treturn (tref 1))@2) / st ==>* tnat 2 / st'.
Proof.
  simpl. repeat reduce. Qed.

Example ex_tfield_w:
  let st := push_call tvoid (alloc_sr (tcl "foo" (<(tvoid, tvoid)>)) init_state) in
  let st' := write_sr 1 (tcl "foo" (<(tvoid, tnat 2)>)) (pop_call st) in
  ((treturn (tref 1)) <@ 1 <- (tnat 1 \+ tnat 1)) / st ==>* tvoid / st'.
Proof.
  simpl. repeat reduce. Qed.

Example ex_tvnew:
  forall st,
  (tvnew 2 "foo") / st ==>* (tcl "foo" (<(tvoid, tvoid)>)) / st.
Proof.
  simpl. intros st. repeat reduce. Qed.

Example ex_tvfield_r:
  forall st,
  (tcl "foo" (<(tvoid, tnat 1, tnat 1 \+ tnat 1)>)?@2) / st ==>* tnat 2 / st.
Proof.
  simpl. intros st. repeat reduce. Qed.

Example ex_tvfield_w:
  let st := write_sk_hd 0 (tcl "foo" (<(tvoid, tvoid)>)) (resize_sk_hd 1 init_state) in
  let st' := write_sk_hd 0 (tcl "foo" (<(tvoid, tnat 2)>)) st in
  ((tvar 0) <?@ 1 <- (tnat 1 \+ tnat 1)) / st ==>* tvoid / st'.
Proof.
  simpl. repeat reduce. Qed.

End Examples.


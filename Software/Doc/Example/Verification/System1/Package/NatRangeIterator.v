Require Import Software.Lib.Relations.Relations.
Require Import Software.Doc.Example.Specification.Package.NatRangeIterator.
Require Import Software.Doc.Example.System.System1Execution.
Require Import Software.Doc.Example.System.System1Tactics.
Require Import Software.Doc.Example.System.System1Verification.
Require Import Software.Language.State.
Require Import Software.Language.Syntax.
Import ObjectOrientedNotations.

Open Scope oo_scope.
Open Scope exec_scope.

Notation "ref '/' st1 '-->' st2" := (transition exec_step ref st1 st2)
  (at level 40, st1 at level 39, format "'[' ref  /  st1  '-->'  st2 ']'").

Notation "ref '/' st1 '-->+' st2" := (clos_refl_trans_1n state (transition exec_step ref) st1 st2)
  (at level 40, st1 at level 39, format "'[' ref  /  st1  '-->+'  st2 ']'").

Notation "ref '/' st1 '-->*' st2" := (clos_refl_trans_term state (transition exec_step ref) st1 st2)
  (at level 40, st1 at level 39, format "'[' ref  /  st1  '-->*'  st2 ']'").

Definition a : term := tref 1.
Definition config_state : state :=
Cstate
  (nil :: nil)%list
  (nil :: nil)%list
  (tvoid :: tcl "NatRangeIterator" <(tbool true, tnat 3, tnat 2)> :: nil)%list
.

Lemma config_state_valid :
  (tnat 2 # "NatRangeIterator_make"|(tnat 3)|) / init_state ==>* a / config_state.
Proof.
  unfold a, config_state.
  repeat reduce.
  eapply Relation_Operators.rt1n_refl.
  Qed.

Ltac invert_termination :=
  match goal with
  | H: clos_refl_trans_term exec_state exec_step ?x ?y1, H0: clos_refl_trans_term exec_state exec_step ?x ?y2 |- _ =>
    assert (y2 = y1);
    [apply (clos_refl_trans_term_is_function exec_state exec_step is_function_exec_step x y1 y2 H H0) |]
  end.

Lemma all_states_wf_config_state :
  all_states_wf exec_step a config_state.
Proof.
  unfold all_states_wf. intros.
  remember config_state as x eqn:Hx.
  induction H; intros; subst x.
  - unfold wf, config_state.
    exists 1. exists true. exists 3. exists 2.
    unfold wf_fun. simpl. repeat split; try solve [reflexivity].
    intros Hcontra. inversion Hcontra.
  - induction H.
    + assert (a # "off"|()| / config_state ==>* tbool true / config_state).
      { unfold a, config_state. repeat reduce. apply Relation_Operators.rt1n_refl. }
      invert_termination. inversion H2. subst result y. clear H1 H2.
      apply IHclos_refl_trans_1n. reflexivity.
    + assert (a # "after"|()| / config_state ==>* tbool false / config_state).
      { unfold a, config_state. repeat reduce. apply Relation_Operators.rt1n_refl. }
      invert_termination. inversion H2. subst result y. clear H1 H2.
      apply IHclos_refl_trans_1n. reflexivity.
    + remember (Cstate (nil :: nil)%list (nil :: nil)%list (tvoid :: tcl "NatRangeIterator" <(tbool false, tnat 3, tnat 2)> :: nil)%list)
        as st2.
      assert (a # "forth"|()| / config_state ==>* tvoid / st2).
      { rewrite Heqst2. unfold a, config_state. repeat reduce. apply Relation_Operators.rt1n_refl. }
      invert_termination. inversion H3. subst result y. clear H2 H3.

(**

We can proceed in one of two ways:

- Explore all reachable states by calling 'forth' until we are 'after', and show that
  each state reached is well-formed.
- Create an induction principle on 'forth' that somehow gets us out of explicit state
  search. Basically we have to prove that calling forth results in a well formed state, based ONLY
  on the assumption that the current state is well-formed.

Ultimately, we come upon the problem of proof again: in order to prove something without
resorting to enumerating all reachable states, we must have an induction principle.

*)
  Abort.

Lemma proof_get_at_start :
  get_at_start exec_step.
Proof.
  unfold get_at_start. intros.
  unfold wf_fun in H.
  destruct H. destruct H0. subst x.
  destruct st as [sk rpsk sr].
  simpl in H1.
  (* Rule out empty stack *)
  destruct sk as [| sf sk].
  { exfalso. apply H1. reflexivity. }
  reduce_clos_refl_trans_term.
  eapply Relation_Operators.rt1n_trans.
    reduce_tcall.
    reduce_value.
    reduce_value.
    reduce_value.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_exec_step.
    reduce_called_on_class.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_tfield_r.
    reduce_tvar.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_tfield_r.
    reduce_read_store.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_value.
  simpl.
  apply Relation_Operators.rt1n_refl.
  Qed.

Lemma proof_get_at_start' :
  get_at_start exec_step.
Proof.
  unfold get_at_start. intros.
    unfold wf_fun in H.
  destruct H. destruct H0. subst x.
  destruct st as [sk rpsk sr].
  simpl in H1.
  (* Rule out empty stack *)
  destruct sk as [| sf sk].
  { exfalso. apply H1. reflexivity. }
  repeat reduce.
  apply Relation_Operators.rt1n_refl.
  Qed.

Lemma proof_get_count :
  get_count exec_step.
Proof.
  unfold get_count. intros.
    unfold wf_fun in H.
  destruct H. destruct H0. subst x.
  destruct st as [sk rpsk sr].
  simpl in H1.
  (* Rule out empty stack *)
  destruct sk as [| sf sk].
  { exfalso. apply H1. reflexivity. }
  repeat reduce.
  apply Relation_Operators.rt1n_refl.
  Qed.

Lemma proof_get_first :
  get_first exec_step.
Proof.
  unfold get_first. intros.
    unfold wf_fun in H.
  destruct H. destruct H0. subst x.
  destruct st as [sk rpsk sr].
  simpl in H1.
  (* Rule out empty stack *)
  destruct sk as [| sf sk].
  { exfalso. apply H1. reflexivity. }
  repeat reduce.
  apply Relation_Operators.rt1n_refl.
  Qed.

Lemma proof_set_at_start :
  set_at_start exec_step.
Proof.
  unfold set_at_start. intros.
    unfold wf_fun in H.
  destruct H. destruct H1. subst x.
  destruct st as [sk rpsk sr].
  simpl in H2.
  (* Rule out empty stack *)
  destruct sk as [| sf sk].
  { exfalso. apply H2. reflexivity. }
  reduce_clos_refl_trans_term.
  eapply Relation_Operators.rt1n_trans.
    eapply STcall.
    repeat reduce_value.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_exec_step.
    reduce_called_on_class.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_tfield_w.
    reduce_tvar.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
    reduce_tfield_w.
    reduce_value.
    reduce_tvar.
  simpl.
  eapply Relation_Operators.rt1n_trans.
    reduce_treturn.
  Abort.

Close Scope exec_scope.
Close Scope oo_scope.


Require Import Software.Lib.Relations.Relations.
Require Import Software.Doc.Example.System.System1Execution.
Require Import Software.Language.DynamicBinding.
Require Import Software.Language.State.
Require Import Software.Language.Syntax.
Require Import Software.Language.Value.

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
  | H: List.nth ?r ?sr tvoid = _ |- read_sr ?r (Cstate _ _ ?sr) = _ =>
    simpl;
    rewrite H;
    reflexivity
  end.

Ltac reduce_called_on_class :=
  match goal with
  (* Using hypothesis *)
  | |- called_on_class _ ?st =>
    match eval cbv in (read_sk_hd 0 st) with
    | tref ?r =>
      match goal with
      | H: List.nth r ?sr tvoid = tcl ?c ?t |- called_on_class ?c (Cstate _ _ ?sr) =>
        exists r;
        split;
        [reflexivity | exists t; assumption]
      | H: read_sr r (Cstate _ _ ?sr) = tcl ?c ?t |- called_on_class ?c (Cstate _ _ ?sr) =>
        exists r;
        split;
        [reflexivity | exists t; assumption]
      end
    end
  (* Direct computation *)
  | |- called_on_vclass _ _ =>
    apply called_on_vclassb_true_iff;
    reflexivity
  (* Direct computation *)
  | |- called_on_class _ _ =>
    apply called_on_classb_true_iff;
    reflexivity
  end.

Ltac reduce_tnot :=
  match goal with
  | |- exec_step (Cexec_state (tnot ?t) _) _ =>
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
  | |- exec_step (Cexec_state (tand ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (tor ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (tplus ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (tminus ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (tmult ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (teq ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (tvar _) _) _ => eapply STvar
  end.

Ltac reduce_tassign :=
  match goal with
  | |- exec_step (Cexec_state (tassign (tvar _) ?t0) _) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STassign_r
    | true => eapply STassign
    end
  end.

Ltac reduce_tseq :=
  match goal with
  | |- exec_step (Cexec_state (tseq ?t _) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STseq_l
    | true => eapply STseq
    end
  end.

Ltac reduce_tif :=
  match goal with
  | |- exec_step (Cexec_state (tif ?t _ _) _) _ =>
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
  | |- exec_step (Cexec_state (twhile _ _) _) _ => eapply STwhile
  end.

Ltac reduce_trc :=
  match goal with
  | |- exec_step (Cexec_state (trc ?t ?t0) _) _ =>
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
  | |- exec_step (Cexec_state (tcall _ ?t0) _) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STcall_r
    | true => eapply STcall
    end
  end.

Ltac reduce_treturn :=
  match goal with
  | |- exec_step (Cexec_state (treturn ?t) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STreturn_r
    | true => eapply STreturn
    end
  end.

Ltac reduce_tcl :=
  match goal with
  | |- exec_step (Cexec_state (tcl _ ?t) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STcl_r
    end
  end.

Ltac reduce_tnew :=
  match goal with
  | |- exec_step (Cexec_state (tnew _ _) _) _ => eapply STnew
  end.

Ltac reduce_tfield_r :=
  match goal with
  | |- exec_step (Cexec_state (tfield_r _ ?t0) ?st) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STfield_r_r
    | true =>
      match t0 with
      | tref ?n0 =>
        match eval cbv in (read_sr n0 st) with
        | tcl _ _ => eapply STfield_r
        | _ =>
          match goal with
          | H: List.nth n0 ?sr tvoid = tcl _ _ |- exec_step (Cexec_state (tfield_r _ _) (Cstate _ _ ?sr)) _ => eapply STfield_r
          | H: read_sr n0 (Cstate _ _ ?sr) = tcl _ _ |- exec_step (Cexec_state (tfield_r _ _) (Cstate _ _ ?sr)) _ => eapply STfield_r
          end
        end
      end
    end
  end.

Ltac reduce_tfield_w :=
  match goal with
  | |- exec_step (Cexec_state (tfield_w _ ?t0 ?t1) ?st) _ =>
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
  | |- exec_step (Cexec_state (tvnew _ _) _) _ => eapply STvnew
  end.

Ltac reduce_tvfield_r :=
  match goal with
  | |- exec_step (Cexec_state (tvfield_r _ ?t0) ?st) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STvfield_r_r
    | true =>
      match t0 with
      | tcl _ _ => eapply STvfield_r
      end
    end
  end.

Ltac reduce_tvfield_w :=
  match goal with
  | |- exec_step (Cexec_state (tvfield_w _ ?t0 ?t1) ?st) _ =>
    match eval cbv in (valueb t0) with
    | false => eapply STvfield_w_l
    | true =>
      match t1 with
      | tvar ?n0 =>
        match eval cbv in (read_sk_hd n0 st) with
        | tcl _ _ => eapply STvfield_w
        end
      end
    end
  end.

Ltac reduce_function class fn rule :=
  match goal with
  | |- exec_step (Cexec_state (texec fn) ?st) _ =>
    match eval cbv in (called_on_classb class st) with
    | true => eapply rule
    | _ =>
      match eval cbv in (read_sk_hd 0 st) with
      | tref ?r =>
        match goal with
        | H: List.nth r ?sr tvoid = tcl class _ |- exec_step (Cexec_state (texec fn) (Cstate _ _ ?sr)) _ => eapply rule
        | H: read_sr r (Cstate _ _ ?sr) = tcl class _ |- exec_step (Cexec_state (texec fn) (Cstate _ _ ?sr)) _ => eapply rule
        end
      end
    end
  end.

Ltac reduce_static_function fn rule :=
  match goal with
  | |- exec_step (Cexec_state (texec fn) _) _ => eapply rule
  end.

Ltac rewrite_nth :=
  match goal with
  | H: List.nth ?n ?sf tvoid = _ |- context [List.nth ?n ?sf tvoid] => rewrite H
  end.

Open Scope string_scope.

Ltac reduce_exec_step :=
     reduce_value
  || reduce_read_stack
  || reduce_read_store
  || reduce_called_on_class
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
  || reduce_tvfield_w
  || reduce_static_function "NatRangeIterator_make" STexec_NatRangeIterator_make
  || reduce_function "NatRangeIterator" "get_at_start" STexec_NatRangeIterator_get_at_start
  || reduce_function "NatRangeIterator" "get_count" STexec_NatRangeIterator_get_count
  || reduce_function "NatRangeIterator" "get_first" STexec_NatRangeIterator_get_first
  || reduce_function "NatRangeIterator" "set_at_start" STexec_NatRangeIterator_set_at_start
  || reduce_function "NatRangeIterator" "set_count" STexec_NatRangeIterator_set_count
  || reduce_function "NatRangeIterator" "set_first" STexec_NatRangeIterator_set_first
  || reduce_function "NatRangeIterator" "off" STexec_NatRangeIterator_off
  || reduce_function "NatRangeIterator" "after" STexec_NatRangeIterator_after
  || reduce_function "NatRangeIterator" "forth" STexec_NatRangeIterator_forth
  || reduce_function "NatRangeIterator" "item" STexec_NatRangeIterator_item
.

Close Scope string_scope.

Ltac reduce_clos_refl_trans_term :=
  match goal with
  | |- clos_refl_trans_term exec_state exec_step _ _ =>
    apply rtt_term;
    [
      unfold not_in_domain;
      intros;
      match goal with
      | H: exec_step _ _ |- False =>
        inversion H
      end
   |]
  end.

Ltac reduce :=
  match goal with
  | |- clos_refl_trans_1n exec_step _ _ => solve [apply Relation_Operators.rt1n_refl]
  | |- clos_refl_trans_1n exec_step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [repeat reduce_exec_step | instantiate; simpl; repeat rewrite_nth; fold (clos_refl_trans_1n exec_step)]
  end.


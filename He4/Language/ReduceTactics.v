Require Import He4.Language.State.
Require Import He4.Language.Step.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Require Import He4.Language.Value.

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

Ltac reduce_tvfield_w :=
  match goal with
  | |- step (pair (tvfield_w _ ?t0 ?t1) ?st) _ =>
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
  || reduce_tvfield_w
.

Ltac reduce :=
  match goal with
  | |- multi step ?t ?t => apply Relation_Operators.rt1n_refl
  | |- multi step _ _ => 
    eapply Relation_Operators.rt1n_trans;
    [repeat reduce_step | instantiate; simpl; fold multi]
  end.


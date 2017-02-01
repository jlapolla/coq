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

Ltac reduce_multi :=
  match goal with
  | |- multi step _ _ => eapply Relation_Operators.rt1n_trans
  end.

Ltac reduce_tnot :=
  match goal with
  | |- step (pair (tnot ?t) _) _ =>
    match eval cbv in (valueb t) with
    | false => eapply STnot_r
    | true =>
      match t with
      | tbool _ => eapply STnot
      | _ => fail
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
      | tbool false => eapply STand_false_l
      | tbool true =>
        match eval cbv in (valueb t0) with
        | false => eapply STand_r
        | true =>
          match t0 with
          | tbool false => eapply STand_false_r
          | tbool true => eapply STand_true
          | _ => fail
          end
        end
      | _ => fail
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
      | tbool true => eapply STor_true_l
      | tbool false =>
        match eval cbv in (valueb t0) with
        | false => eapply STor_r
        | true =>
          match t0 with
          | tbool true => eapply STor_true_r
          | tbool false => eapply STor_false
          | _ => fail
          end
        end
      | _ => fail
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
        | _ => fail
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
        | _ => fail
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
        | _ => fail
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
  | |- step (pair (tassign (tvar _) ?t0) _) _ => fail (* TODO *)
  end.

Ltac reduce_tseq :=
  match goal with
  | |- step (pair (tseq ?t _) _) _ =>
    match t with
    | tvoid => eapply STseq
    | _ => eapply STseq_l
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
        | pair (tnat n) (tnat n0) =>
          match eqb n n0 with
          | false => eapply STeq_nat_false
          | true => eapply STeq_nat_true
          end
        | pair (tbool b) (tbool b0) =>
          match eval cbv in (pair b b0) with
          | pair true true => eapply STeq_bool_true
          | pair false false => eapply STeq_bool_true
          | _ => eapply STeq_bool_false
          end
        | pair (tref n) (tref n0) =>
          match eqb n n0 with
          | false => eapply STeq_ref_false
          | true => eapply STeq_ref_true
          end
        | pair (trc _ _) (trc _ _) => eapply STeq_rc
        | pair (tcl c t) (tcl c0 t0) =>
          match String.eqb c c0 with
          | false => eapply STeq_cl_false
          | true => eapply STeq_cl
          end
        | pair _ _ => fail
        end
      end
    end
  end.


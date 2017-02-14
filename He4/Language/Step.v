Require Import He4.Strings.String.
Require Import He4.Language.Term.
Require Import He4.Language.State.
Require Import He4.Language.Value.
Require Import He4.Language.Record.
Require Import He4.Language.StepProp.

Section Steps.

Let beq_nat : nat -> nat -> bool := NPeano.Nat.eqb.
Let beq_bool : bool -> bool -> bool := Bool.eqb.
Let beq_string : String.string -> String.string -> bool := String.eqb.

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : step_relation :=
  | STnot_r :
    forall t t' st st',
    t / st ==> t' / st' ->
    tnot t / st ==> tnot t' / st'
  | STnot :
    forall b st,
    tnot (tbool b) / st ==> tbool (negb b) / st

  | STand_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tand t t0 / st ==> tand t' t0 / st'
  | STand_true :
    forall t0 st,
    tand (tbool true) t0 / st ==> t0 / st
  | STand_false :
    forall t0 st,
    tand (tbool false) t0 / st ==> tbool false / st

  | STor_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tor t t0 / st ==> tor t' t0 / st'
  | STor_false :
    forall t0 st,
    tor (tbool false) t0 / st ==> t0 / st
  | STor_true :
    forall t0 st,
    tor (tbool true) t0 / st ==> tbool true / st

  | STplus_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tplus t t0 / st ==> tplus t' t0 / st'
  | STplus_r :
    forall t t0 t0' st st',
    value t ->
    t0 / st ==> t0' / st' ->
    tplus t t0 / st ==> tplus t t0' / st'
  | STplus_nat :
    forall n n0 st,
    tplus (tnat n) (tnat n0) / st ==> tnat (plus n n0) / st

  | STminus_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tminus t t0 / st ==> tminus t' t0 / st'
  | STminus_r :
    forall t t0 t0' st st',
    value t ->
    t0 / st ==> t0' / st' ->
    tminus t t0 / st ==> tminus t t0' / st'
  | STminus_nat :
    forall n n0 st,
    tminus (tnat n) (tnat n0) / st ==> tnat (minus n n0) / st

  | STmult_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tmult t t0 / st ==> tmult t' t0 / st'
  | STmult_r :
    forall t t0 t0' st st',
    value t ->
    t0 / st ==> t0' / st' ->
    tmult t t0 / st ==> tmult t t0' / st'
  | STmult_nat :
    forall n n0 st,
    tmult (tnat n) (tnat n0) / st ==> tnat (mult n n0) / st

  | STeq_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    teq t t0 / st ==> teq t' t0 / st'
  | STeq_r :
    forall t t0 t0' st st',
    value t ->
    t0 / st ==> t0' / st' ->
    teq t t0 / st ==> teq t t0' / st'
  | STeq_void :
    forall st,
    teq tvoid tvoid / st ==> tbool true / st
  | STeq_nat :
    forall n n0 st,
    teq (tnat n) (tnat n0) / st ==> tbool (beq_nat n n0) / st
  | STeq_bool :
    forall b b0 st,
    teq (tbool b) (tbool b0) / st ==> tbool (beq_bool b b0) / st
  | STeq_ref :
    forall n n0 st,
    teq (tref n) (tref n0) / st ==> tbool (beq_nat n n0) / st
  | STeq_rc :
    forall t t0 t1 t2 st,
    value (trc t t0) ->
    value (trc t1 t2) ->
    teq (trc t t0) (trc t1 t2) / st ==> tand (teq t t1) (teq t0 t2) / st
  | STeq_cl :
    forall c t0 c1 t2 st,
    value (tcl c t0) ->
    value (tcl c1 t2) ->
    teq (tcl c t0) (tcl c1 t2) / st ==> tand (tbool (beq_string c c1)) (teq t0 t2) / st

  | STvar :
    forall n st,
    (tvar n) / st ==> read_sk_hd n st / st

  | STassign_r :
    forall n t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tassign (tvar n) t0 / st ==> tassign (tvar n) t0' / st'
  | STassign :
    forall n v0 st,
    value v0 ->
    tassign (tvar n) v0 / st ==> tvoid / write_sk_hd n v0 st

  | STseq_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tseq t t0 / st ==> tseq t' t0 / st'
  | STseq :
    forall t0 st,
    tseq tvoid t0 / st ==> t0 / st

  | STif_l :
    forall t t' t0 t1 st st',
    t / st ==> t' / st' ->
    tif t t0 t1 / st ==> tif t' t0 t1 / st'
  | STif_false :
    forall t0 t1 st,
    tif (tbool false) t0 t1 / st ==> t1 / st
  | STif_true :
    forall t0 t1 st,
    tif (tbool true) t0 t1 / st ==> t0 / st

  | STwhile :
    forall t t0 st,
    twhile t t0 / st ==> tif t (tseq t0 (twhile t t0)) tvoid / st

  | STrc_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    trc t t0 / st ==> trc t' t0 / st'
  | STrc_r :
    forall v t0 t0' st st',
    value v ->
    t0 / st ==> t0' / st' ->
    trc v t0 / st ==> trc v t0' / st'

  | STcall_r :
    forall f t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tcall f t0 / st ==> tcall f t0' / st'
  | STcall :
    forall f v0 st,
    value v0 ->
    tcall f v0 / st ==> treturn (texec f) / push_call v0 st

  | STreturn_r :
    forall t t' st st',
    t / st ==> t' / st' ->
    treturn t / st ==> treturn t' / st'
  | STreturn :
    forall v st,
    value v ->
    treturn v / st ==> v / pop_call st

  | STcl_r :
    forall c t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tcl c t0 / st ==> tcl c t0' / st'

  | STnew :
    forall n c0 st,
    tnew n c0 / st ==> tref (length (get_store st)) / alloc_sr (tcl c0 (rc_create n)) st

  | STfield_r_r :
    forall n t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tfield_r n t0 / st ==> tfield_r n t0' / st'
  | STfield_r :
    forall n n0 c t0 st,
    read_sr n0 st = tcl c t0 ->
    tfield_r n (tref n0) / st ==> rc_read n t0 / st

  | STfield_w_r :
    forall n t0 t1 t1' st st',
    t1 / st ==> t1' / st' ->
    tfield_w n t0 t1 / st ==> tfield_w n t0 t1' / st'
  | STfield_w_l :
    forall n t0 t0' v1 st st',
    value v1 ->
    t0 / st ==> t0' / st' ->
    tfield_w n t0 v1 / st ==> tfield_w n t0' v1 / st'
  | STfield_w :
    forall n n0 t0 v0 c st,
    value v0 ->
    read_sr n0 st = tcl c t0 ->
    tfield_w n v0 (tref n0) / st ==> tvoid / write_sr n0 (tcl c (rc_write n v0 t0)) st

  | STvnew :
    forall n c0 st,
    tvnew n c0 / st ==> tcl c0 (rc_create n) / st

  | STvfield_r_r :
    forall n t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tvfield_r n t0 / st ==> tvfield_r n t0' / st'
  | STvfield_r :
    forall n c t0 st,
    value (tcl c t0) ->
    tvfield_r n (tcl c t0) / st ==> rc_read n t0 / st

  | STvfield_w_l :
    forall n t0 t0' t1 st st',
    t0 / st ==> t0' / st' ->
    tvfield_w n t0 t1 / st ==> tvfield_w n t0' t1 / st'
  | STvfield_w :
    forall n n0 t0 v0 c st,
    value v0 ->
    read_sk_hd n0 st = tcl c t0 ->
    tvfield_w n v0 (tvar n0) / st ==> tvoid / write_sk_hd n0 (tcl c (rc_write n v0 t0)) st

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (Cexec_state t1 st1) (Cexec_state t2 st2)).

Lemma value_irreducible__step:
  value_irreducible step.
Proof with auto.
  intros t Hval.
  induction Hval;
  try solve [intros t' st st' Hcontra; inversion Hcontra].
  intros t' st st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval1 in H0. inversion H0.
  apply IHHval2 in H5. inversion H5.
  intros t' st st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval in H0. inversion H0.
  Qed.

Ltac value_step_impossible :=
  match goal with
  | H: value ?t, H0: step (Cexec_state ?t ?st) (Cexec_state ?t' ?st') |- _ =>
    solve [destruct (value_irreducible__step t H t' st st'); assumption]
  end.

Ltac step_impossible :=
  match goal with
  | H: step _ _ |- _ =>
    solve [inversion H]
  end.

Ltac step_inductive :=
  match goal with
  | H: forall z, step ?x z -> z = ?y, H0: step ?x ?a |- _ = _ =>
    solve [apply H in H0; inversion H0; auto]
  end.

Ltac rewrite_invert :=
  match goal with
  | H: ?x = ?y, H0: ?x = ?z |- _ = _ =>
    solve [rewrite H in H0; inversion H0; reflexivity]
  end.

Ltac equality_contradiction :=
  match goal with
  | H: ?x = ?x -> False |- _ =>
    solve [exfalso; apply H; reflexivity]
  end.

Lemma deterministic__step:
  deterministic step.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [value_step_impossible];
  try solve [auto];
  try solve [step_inductive];
  try solve [rewrite_invert];
  try solve [equality_contradiction];
  try solve [step_impossible].
  Qed.

End Steps.


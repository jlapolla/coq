Require Export Coq.Strings.String.
Require Export He4.Language.Term.
Require Export Coq.Lists.List.
Require Export He4.Lists.List.
Require Export He4.Language.ProgramState.
Require Export He4.Language.Value.
Require Export He4.Language.Record.

Section LanguageDefinitions.

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm state) -> (prod tm state) -> Prop :=
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
  | STand_r :
    forall t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tand (tbool true) t0 / st ==> tand (tbool true) t0' / st'
  | STand_false_l :
    forall t0 st,
    tand (tbool false) t0 / st ==> tbool false / st
  | STand_false_r :
    forall st,
    tand (tbool true) (tbool false) / st ==> tbool false / st
  | STand_true :
    forall st,
    tand (tbool true) (tbool true) / st ==> tbool true / st

  | STor_l :
    forall t t' t0 st st',
    t / st ==> t' / st' ->
    tor t t0 / st ==> tor t' t0 / st'
  | STor_r :
    forall t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tor (tbool false) t0 / st ==> tor (tbool false) t0' / st'
  | STor_true_l :
    forall t0 st,
    tor (tbool true) t0 / st ==> tbool true / st
  | STor_true_r :
    forall st,
    tor (tbool false) (tbool true) / st ==> tbool true / st
  | STor_false :
    forall st,
    tor (tbool false) (tbool false) / st ==> tbool false / st

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
  | STeq_nat_false :
    forall n n0 st,
    (n = n0 -> False) ->
    teq (tnat n) (tnat n0) / st ==> tbool false / st
  | STeq_nat_true :
    forall n st,
    teq (tnat n) (tnat n) / st ==> tbool true / st
  | STeq_bool_false :
    forall b b0 st,
    (b = b0 -> False) ->
    teq (tbool b) (tbool b0) / st ==> tbool false / st
  | STeq_bool_true :
    forall b st,
    teq (tbool b) (tbool b) / st ==> tbool true / st
  | STeq_ref_false :
    forall n n0 st,
    (n = n0 -> False) ->
    teq (tref n) (tref n0) / st ==> tbool false / st
  | STeq_ref_true :
    forall n st,
    teq (tref n) (tref n) / st ==> tbool true / st
  | STeq_rc :
    forall t t0 t1 t2 st,
    value (trc t t0) ->
    value (trc t1 t2) ->
    teq (trc t t0) (trc t1 t2) / st ==> tand (teq t t1) (teq t0 t2) / st
  | STeq_cl_false :
    forall c t0 c1 t2 st,
    value (tcl c t0) ->
    value (tcl c1 t2) ->
    (c = c1 -> False) ->
    teq (tcl c t0) (tcl c1 t2) / st ==> tbool false / st
  | STeq_cl :
    forall c t0 t2 st,
    value (tcl c t0) ->
    value (tcl c t2) ->
    teq (tcl c t0) (tcl c t2) / st ==> teq t0 t2 / st

  | STvar :
    forall n sk sr,
    (tvar n) / (pair sk sr) ==> sk_read_hd n sk / (pair sk sr)

  | STassign_r :
    forall n t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tassign (tvar n) t0 / st ==> tassign (tvar n) t0' / st'
  | STassign :
    forall n v0 sk sr,
    value v0 ->
    tassign (tvar n) v0 / (pair sk sr) ==> tvoid / (pair (sk_write_hd n v0 sk) sr)

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
    forall f v0 sk sr,
    value v0 ->
    tcall f v0 / (pair sk sr) ==> treturn (texec f) / (pair (push (rc_to_list v0) sk) sr)

  | STreturn_r :
    forall t t' st st',
    t / st ==> t' / st' ->
    treturn t / st ==> treturn t' / st'
  | STreturn :
    forall v sk sr,
    value v ->
    treturn v / (pair sk sr) ==> v / (pair (pop sk) sr)

  | STcl_r :
    forall c t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tcl c t0 / st ==> tcl c t0' / st'

  | STnew :
    forall n c0 sk sr,
    tnew n c0 / pair sk sr ==> tref (length sr) / pair sk (sr_alloc (tcl c0 (rc_create n)) sr)

  | STdefault :
    forall n c0 st,
    tdefault n c0 / st ==> tcl c0 (rc_create n) / st

  | STfield_r_r :
    forall n t0 t0' st st',
    t0 / st ==> t0' / st' ->
    tfield_r n t0 / st ==> tfield_r n t0' / st'
  | STfield_r_ref :
    forall n n0 c t0 sk sr,
    sr_read n0 sr = tcl c t0 ->
    tfield_r n (tref n0) / pair sk sr ==> rc_read n t0 / pair sk sr
  | STfield_r_cl :
    forall n c t0 st,
    value (tcl c t0) ->
    tfield_r n (tcl c t0) / st ==> rc_read n t0 / st

  | STfield_w_r :
    forall n t0 t1 t1' st st',
    (forall n0, t1 <> tvar n0) ->
    t1 / st ==> t1' / st' ->
    tfield_w n t0 t1 / st ==> tfield_w n t0 t1' / st'
  | STfield_w_l :
    forall n n0 t0 t0' v1 st st',
    value v1 \/ v1 = tvar n0 ->
    t0 / st ==> t0' / st' ->
    tfield_w n t0 v1 / st ==> tfield_w n t0' v1 / st'
  | STfield_w_var :
    forall n n0 t0 v0 c sk sr,
    value v0 ->
    sk_read_hd n0 sk = tcl c t0 ->
    tfield_w n v0 (tvar n0) / pair sk sr ==> tvoid / pair (sk_write_hd n0 (tcl c (rc_write n v0 t0)) sk) sr
  | STfield_w_var_ref :
    forall n n0 n1 v0 sk sr,
    value v0 ->
    sk_read_hd n0 sk = tref n1 ->
    tfield_w n v0 (tvar n0) / pair sk sr ==> tfield_w n v0 (tref n1) / pair sk sr
  | STfield_w_ref :
    forall n n0 t0 v0 c sk sr,
    value v0 ->
    sr_read n0 sr = tcl c t0 ->
    tfield_w n v0 (tref n0) / pair sk sr ==> tvoid / pair sk (sr_write n0 (tcl c (rc_write n v0 t0)) sr)

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).

Lemma value_does_not_step:
  forall t,
  value t ->
  forall st t' st',
    ~(t / st ==> t' / st').
Proof with auto.
  intros t Hval.
  induction Hval;
  try solve [intros st t' st' Hcontra; inversion Hcontra].
  intros st t' st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval1 in H0. inversion H0.
  apply IHHval2 in H5. inversion H5.
  intros st t' st' Hcontra.
  inversion Hcontra; subst.
  apply IHHval in H0. inversion H0.
  Qed.

Ltac value_step_impossible :=
  match goal with
  | H: value ?t, H0: step (pair ?t ?st) (pair ?t' ?st') |- _ =>
    solve [destruct (value_does_not_step t H st t' st'); assumption]
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

Lemma step_deterministic:
  forall x y,
  step x y ->
  forall z,
    step x z ->
    z = y.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [value_step_impossible];
  try solve [auto];
  try solve [step_inductive];
  try solve [rewrite_invert];
  try solve [equality_contradiction];
  try solve [step_impossible].
  (* STfield_w_r and STfield_w_l *)
  destruct H5 as [H5 | H5].
  { value_step_impossible. }
  { exfalso. apply (H n1). assumption. }
  (* STfield_w_r and STfield_w_var *)
  exfalso. apply (H n1). reflexivity.
  (* STfield_w_r and STfield_w_var_ref *)
  exfalso. apply (H n1). reflexivity.
  (* STfield_w_l and STfield_w_r *)
  destruct H as [H | H].
  { value_step_impossible. }
  { exfalso. apply (H5 n0). assumption. }
  (* STfield_w_var and STfield_w_r *)
  exfalso. apply (H6 n0). reflexivity.
  (* STfield_w_var_ref and STfield_w_r *)
  exfalso. apply (H6 n0). reflexivity.
  Qed.

End LanguageDefinitions.


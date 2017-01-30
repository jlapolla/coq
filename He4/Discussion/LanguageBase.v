Require Export He4.Discussion.ProgramState.

Section LanguageDefinitions.

Variable cl : Type.
Variable fn : Type.

Inductive tm : Type :=

  (* Base types *)
  | tvoid : tm
  | tnat : nat -> tm
  | tbool : bool -> tm

  (* Boolean operators *)
  | tnot : tm -> tm
  | tand : tm -> tm -> tm
  | tor : tm -> tm -> tm

  (* Numeric operators *)
  | tplus : tm -> tm -> tm
  | tminus : tm -> tm -> tm
  | tmult : tm -> tm -> tm

  (* Equality operators *)
  | teq : tm -> tm -> tm

  (* Variables and references *)
  | tvar : nat -> tm
  | tref : nat -> tm
  | tassign : tm -> tm -> tm

  (* Control flow *)
  | tseq : tm -> tm -> tm

  (* Records *)
  | trc : tm -> tm -> tm

  (* Functions *)
  | tcall : fn -> tm -> tm
  | texec : fn -> tm
  | treturn : tm -> tm

  (* Classes *)
  | tcl : cl -> tm -> tm
  | tnew : nat -> cl -> tm
  | tdefault : nat -> cl -> tm
  | tfield_r : nat -> tm -> tm
  | tfield_w : nat -> tm -> tm -> tm.

Inductive value : tm -> Prop :=

  (* Base types *)
  | vvoid : value tvoid
  | vnat : forall n, value (tnat n)
  | vbool : forall b, value (tbool b)
  | vref : forall n, value (tref n)
  | vrc : forall t rc, value t -> value rc -> value (trc t rc)

  (* Classes *)
  | vcl : forall c t, value t -> value (tcl c t).

Set Implicit Arguments.

Definition stack := ProgramState.stack tm.
Definition sk_read_hd (n : nat) (sk : stack) : tm := ProgramState.sk_read_hd n sk tvoid.
Definition sk_resize_hd (n : nat) (sk : stack) : stack := ProgramState.sk_resize_hd n sk tvoid.
Definition empty_stack : stack := push nil nil.

Definition store := ProgramState.store tm.
Definition sr_read (n : nat) (sr : store) : tm := ProgramState.sr_read n sr tvoid.
Definition empty_store : store := sr_alloc tvoid nil. (* Position 0 represents the "null" reference *)

(** Records encoded as nested pair terms. *)
Hint Resolve Lt.lt_S_n.

Fixpoint rc_create (n : nat) : tm :=
  match n with
  | O => tvoid
  | S n' => trc tvoid (rc_create n')
  end.

Fixpoint rc_length (rc : tm) : nat :=
  match rc with
  | trc _ rc' => S (rc_length rc')
  | _ => O
  end.

Fixpoint rc_read (n : nat) (rc : tm) : tm :=
  match n with
  | O =>
    match rc with
    | trc t1 _ => t1
    | _ => tvoid
    end
  | S n' =>
    match rc with
    | trc _ rc' => rc_read n' rc'
    | _ => tvoid
    end
  end.

Fixpoint rc_write (n : nat) (t rc : tm) : tm :=
  match n with
  | O =>
    match rc with
    | trc _ rc' => trc t rc'
    | _ => rc
    end
  | S n' =>
    match rc with
    | trc t1 rc' => trc t1 (rc_write n' t rc')
    | _ => rc
    end
  end.

Fixpoint rc_to_list (rc : tm) : list tm :=
  match rc with
  | trc t1 rc' => cons t1 (rc_to_list rc')
  | _ => nil
  end.

Fixpoint list_to_rc (l : list tm) : tm :=
  match l with
  | nil => tvoid
  | cons t' l' => trc t' (list_to_rc l')
  end.

Unset Implicit Arguments.

Lemma rc_create_length:
  forall n,
  rc_length (rc_create n) = n.
Proof with auto.
  induction n; simpl...
  Qed.

Lemma rc_create_correct:
  forall n m,
  lt m n ->
  rc_read m (rc_create n) = tvoid.
Proof with auto.
  induction n. intros. inversion H.
  destruct m; simpl...
  Qed.

Lemma rc_read_overflow:
  forall rc m,
  le (rc_length rc) m ->
  rc_read m rc = tvoid.
Proof with auto.
  induction rc; try (destruct m; auto).
  simpl. intros. inversion H.
  simpl. intros. apply Le.le_S_n in H...
  Qed.

Lemma rc_write_length:
  forall rc n t,
  rc_length (rc_write n t rc) = rc_length rc.
Proof with auto.
  induction rc;
  try solve [destruct n; simpl; auto];
  try solve [destruct n0; auto].
  Qed.

Lemma rc_write_correct_1:
  forall rc n m t,
  lt m (rc_length rc) ->
  m <> n ->
  rc_read m (rc_write n t rc) = rc_read m rc.
Proof with auto.
  induction rc;
  try solve [destruct n; auto];
  try solve [destruct n0; auto].
  destruct n.
  destruct m; try solve [intros; exfalso; auto]...
  destruct m; simpl...
  Qed.

Lemma rc_write_correct_2:
  forall rc n t,
  lt n (rc_length rc) ->
  rc_read n (rc_write n t rc) = t.
Proof with auto.
  induction rc;
  try solve [simpl; intros; inversion H].
  destruct n; simpl; intros...
  Qed.

Lemma rc_to_list_length:
  forall rc,
  length (rc_to_list rc) = rc_length rc.
Proof with auto.
  induction rc...
  simpl...
  Qed.

Lemma rc_to_list_correct:
  forall rc m d1,
  lt m (rc_length rc) ->
  nth m (rc_to_list rc) d1 = rc_read m rc.
Proof with auto.
  induction rc;
  try solve [intros; inversion H].
  destruct m; simpl...
  Qed.

Lemma list_to_rc_length:
  forall l,
  rc_length (list_to_rc l) = length l.
Proof with auto.
  induction l...
  simpl...
  Qed.

Lemma list_to_rc_correct:
  forall l m d,
  lt m (length l) ->
  rc_read m (list_to_rc l) = nth m l d.
Proof.
  induction l;
  try solve [intros; inversion H].
  destruct m;
  try solve [simpl; intros; auto].
  Qed.

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step_base : (prod tm (prod stack store)) -> (prod tm (prod stack store)) -> Prop :=
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

  where "t1 '/' st1 '==>' t2 '/' st2" := (step_base (pair t1 st1) (pair t2 st2)).

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
  | H: value ?t, H0: step_base (pair ?t ?st) (pair ?t' ?st') |- _ =>
    solve [destruct (value_does_not_step t H st t' st'); assumption]
  end.

Ltac step_base_impossible :=
  match goal with
  | H: step_base _ _ |- _ =>
    solve [inversion H]
  end.

Ltac step_base_inductive :=
  match goal with
  | H: forall z, step_base ?x z -> z = ?y, H0: step_base ?x ?a |- _ = _ =>
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

Lemma step_base_deterministic:
  forall x y,
  step_base x y ->
  forall z,
    step_base x z ->
    z = y.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [value_step_impossible];
  try solve [auto];
  try solve [step_base_inductive];
  try solve [rewrite_invert];
  try solve [equality_contradiction];
  try solve [step_base_impossible].
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

Arguments tvoid {cl} {fn}.
Arguments tnat {cl} {fn} n.
Arguments tbool {cl} {fn} b.
Arguments tnot {cl} {fn} b.
Arguments tand {cl} {fn} b b0.
Arguments tor {cl} {fn} b b0.
Arguments tplus {cl} {fn} n n0.
Arguments tminus {cl} {fn} n n0.
Arguments tmult {cl} {fn} n n0.
Arguments teq {cl} {fn} t t0.
Arguments tvar {cl} {fn} n.
Arguments tref {cl} {fn} n.
Arguments tassign {cl} {fn} t t0.
Arguments tseq {cl} {fn} t t0.
Arguments trc {cl} {fn} t t0.
Arguments tcall {cl} {fn} f t0.
Arguments texec {cl} {fn} f.
Arguments treturn {cl} {fn} t.
Arguments tcl {cl} {fn} c t0.
Arguments tnew {cl} {fn} n c0.
Arguments tdefault {cl} {fn} n c0.
Arguments tfield_r {cl} {fn} n t0.
Arguments tfield_w {cl} {fn} n t0 t1.

Module ObjectOrientedNotations.

Notation "'|(' ')|'" := tvoid (at level 20, format "'|(' ')|'") : oo_scope.

Notation "'|(' t ')|'" := (trc t tvoid) (at level 20, format "'|(' t ')|'") : oo_scope.

Notation "'|(' t ',' .. ',' t0 ')|'" :=
  (trc t .. (trc t0 tvoid) ..) (at level 20, format "'|(' t ','  .. ','  t0 ')|'") : oo_scope.

Notation "t '@' n0" :=
  (tfield_r n0 t) (at level 26, left associativity, format "t '@' n0") : oo_scope.

Notation "t '#' f t0" :=
  (tcall f (trc t t0)) (at level 26, left associativity, format "t  '#'  f t0") : oo_scope.

Notation "'!' t" :=
  (tnot t) (at level 35, right associativity, format "'!' t") : oo_scope.

Notation "t '\*' t0" :=
  (tmult t t0) (at level 40, left associativity, format "t  '\*'  t0") : oo_scope.

Notation "t '\+' t0" :=
  (tplus t t0) (at level 45, left associativity, format "t  '\+'  t0") : oo_scope.

Notation "t '\-' t0" :=
  (tminus t t0) (at level 45, left associativity, format "t  '\-'  t0") : oo_scope.

Notation "t '==' t0" :=
  (teq t t0) (at level 50, left associativity, format "t  '=='  t0") : oo_scope.

Notation "t \&& t0" :=
  (tand t t0) (at level 55, left associativity, format "t  '\&&'  t0") : oo_scope.

Notation "t '\||' t0" :=
  (tor t t0) (at level 61, left associativity, format "t  '\||'  t0") : oo_scope.

Notation "t '<@' n0 '<-' t1" :=
  (tfield_w n0 t1 t) (at level 70, format "t '<@' n0  '<-'  t1") : oo_scope.

Notation "t '::=' t0" :=
  (tassign t t0) (at level 70, right associativity) : oo_scope.

Notation "t ; t0" :=
  (tseq t t0) (at level 80, right associativity, format "'[v' t ';' '/' t0 ']'").

Section Examples.

(** *** Notation Examples

    We define a new set of terms, which are [tm]'s bound to a specific
    [cl] and [fn] type. *)

Variable cl : Type.
Variable fn : Type.

Let ivoid := @tvoid cl fn.
Let inat := @tnat cl fn.
Let ibool := @tbool cl fn.
Let inot := @tnot cl fn.
Let iand := @tand cl fn.
Let ior := @tor cl fn.
Let iplus := @tplus cl fn.
Let iminus := @tminus cl fn.
Let imult := @tmult cl fn.
Let ieq := @teq cl fn.
Let ivar := @tvar cl fn.
Let iref := @tref cl fn.
Let iassign := @tassign cl fn.
Let iseq := @tseq cl fn.
Let irc := @trc cl fn.
Let icall := @tcall cl fn.
Let iexec := @texec cl fn.
Let ireturn := @treturn cl fn.
Let icl := @tcl cl fn.
Let inew := @tnew cl fn.
Let idefault := @tdefault cl fn.
Let ifield_r := @tfield_r cl fn.
Let ifield_w := @tfield_w cl fn.

(** [FNget_first] is an example function name. *)

Variable FNget_first : fn.

Delimit Scope oo_scope with oo.

Example ex_oo_notation_1:
  (!(ibool true) \|| (ibool false) \&& (ibool false))%oo = ior (inot (ibool true)) (iand (ibool false) (ibool false)).
Proof. reflexivity. Abort.

Example ex_oo_notation_2:
  ((inat 1) \* (inat 2) \- (inat 3) \+ (inat 4) \* (inat 5))%oo = iplus (iminus (imult (inat 1) (inat 2)) (inat 3)) (imult (inat 4) (inat 5)).
Proof. reflexivity. Abort.

Example ex_oo_notation_3:
  |()|%oo = ivoid.
Proof. reflexivity. Abort.

Example ex_oo_notation_4:
  |(inat 2)|%oo = irc (inat 2) ivoid.
Proof. reflexivity. Abort.

Example ex_oo_notation_5:
  |(inat 1, inat 2, inat 4)|%oo = (irc (inat 1) (irc (inat 2) (irc (inat 4) ivoid))).
Proof. reflexivity. Abort.

Example ex_oo_notation_6:
  ((inat 1)#FNget_first|()| @ 2 #FNget_first|()|)%oo = icall FNget_first (irc (ifield_r 2 (icall FNget_first (irc (inat 1) ivoid))) ivoid).
Proof. reflexivity. Abort.

Example ex_oo_notation_6:
  ((inat 1)#FNget_first|()| <@ 2 <- (inat 2)#FNget_first|()|)%oo = ifield_w 2 (icall FNget_first (irc (inat 2) ivoid)) (icall FNget_first (irc (inat 1) ivoid)).
Proof. reflexivity. Abort.

Example ex_oo_notation_7:
  (inat 1#FNget_first|(inat 2#FNget_first|()|, inat 4)|)%oo = icall FNget_first (irc (inat 1) (irc (icall FNget_first (irc (inat 2) ivoid)) (irc (inat 4) ivoid))).
Proof. reflexivity. Abort.

Example ex_oo_notation_8:
  (inat 1#FNget_first|(inat 2)|#FNget_first|(inat 4)|)%oo = icall FNget_first (irc (icall FNget_first (irc (inat 1) (irc (inat 2) ivoid))) (irc (inat 4) ivoid)).
Proof. reflexivity. Abort.

Example ex_oo_notation_9:
  (ivar 1 ::= ivar 2 ::= inat 3)%oo = iassign (ivar 1) (iassign (ivar 2) (inat 3)).
Proof. reflexivity. Abort.

Example ex_oo_notation_10:
  (inat 4; inat 5; inat 6)%oo = iseq (inat 4) (iseq (inat 5) (inat 6)).
Proof. reflexivity. Abort.

Example ex_oo_notation_11:
  ((inat 1) == (inat 3) \|| (ibool true) == (ibool false))%oo = ior (ieq (inat 1) (inat 3)) (ieq (ibool true) (ibool false)).
Proof. reflexivity. Abort.

End Examples.

End ObjectOrientedNotations.

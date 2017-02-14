Require Import Coq.Relations.Relations.
Require Import He4.Language.Syntax.
Require Import He4.Language.Value.
Require Import He4.Language.State.

Definition exec_step_relation : Type := relation exec_state.
Definition multi : exec_step_relation -> exec_step_relation := clos_refl_trans_1n exec_state.

Module StepRelationNotations.

Notation "s \U s0" := (union exec_state s s0) (at level 85, right associativity).

End StepRelationNotations.

Section StepProps.

Variable exec_step : exec_step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition value_irreducible : Prop :=
  forall t,
  value t ->
  forall t' st st',
    t / st ==> t' / st' ->
    False.

Definition deterministic : Prop :=
  forall x y,
  exec_step x y ->
  forall z,
    exec_step x z ->
    z = y.

Definition deterministic_multi : Prop :=
  forall t v1 v2 st st1 st2,
  value v1 ->
  t / st ==>* v1 / st1 ->
  value v2 ->
  t / st ==>* v2 / st2 ->
  v2 = v1 /\ st2 = st1.

(** WARNING: For a non-deterministic term, [term_terminates] does not say the
    term _always_ terminates. It only says that it _can_ terminate.

    For a deterministic term, "can terminate" is equivalent to "always
    terminates". *)

Definition term_terminates (t : term) (st : state) : Prop :=
  exists v st',
  value v ->
  t / st ==>* v / st'.

Definition term_deterministic (t : term) (st : state) : Prop :=
  forall v1 v2 st1 st2,
  value v1 ->
  t / st ==>* v1 / st1 ->
  value v2 ->
  t / st ==>* v2 / st2 ->
  v2 = v1 /\ st2 = st1.

Definition term_preserves_state (t : term) (st : state) : Prop :=
  forall v st',
  value v ->
  t / st ==>* v / st' ->
  st' = st.

(** WARNING: Again, watch out for non-deterministic terms! *)
Definition term_preserves_term (t : term) (st : state) (preserved : term) : Prop :=
  forall v1 v2 st1 st2,
  value v1 ->
  t / st ==>* v1 / st1 ->
  value v2 ->
  preserved / st ==>* v2 / st2 ->
  exists st3, preserved / st1 ==>* v2 / st3.

Definition states_eq_wrt (t : term) (st1 st2 : state) : Prop :=
  forall v st1',
  value v ->
  t / st1 ==>* v / st1' ->
  exists st2', t / st2 ==>* v / st2'.

End StepProps.


Require Import Coq.Relations.Relations.
Require Import He4.Language.Term.
Require Import He4.Language.Value.
Require Import He4.Language.State.

Definition step_relation : Type := relation (prod tm state).
Definition multi : step_relation -> step_relation := clos_refl_trans_1n (prod tm state).

Module StepRelationNotations.

Notation "s \U s0" := (union (prod tm state) s s0) (at level 85, right associativity).

End StepRelationNotations.

Section StepProps.

Variable step : step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (pair t1 st1) (pair t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition value_irreducible : Prop :=
  forall t,
  value t ->
  forall t' st st',
    t / st ==> t' / st' ->
    False.

Definition deterministic : Prop :=
  forall x y,
  step x y ->
  forall z,
    step x z ->
    z = y.

Definition term_terminates (t : tm) (st : state) : Prop :=
  exists v st',
  value v ->
  t / st ==>* v / st'.

Definition term_deterministic (t : tm) (st : state) : Prop :=
  forall v1 v2 st1 st2,
  value v1 ->
  t / st ==>* v1 / st1 ->
  value v2 ->
  t / st ==>* v2 / st2 ->
  v2 = v1 /\ st2 = st1.

Definition term_preserves_state (t : tm) (st : state) : Prop :=
  forall v st',
  value v ->
  t / st ==>* v / st' ->
  st' = st.

Definition states_eq_wrt (t : tm) (st1 st2 : state) : Prop :=
  forall v st1',
  value v ->
  t / st1 ==>* v / st1' ->
  exists st2', t / st2 ==>* v / st2'.

End StepProps.


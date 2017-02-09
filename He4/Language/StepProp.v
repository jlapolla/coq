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

Definition states_eq_wrt (t : tm) (st1 st2 : state) : Prop :=
  forall v st1',
  value v ->
  t / st1 ==>* v / st1' ->
  exists st2', t / st2 ==>* v / st2'.

End StepProps.


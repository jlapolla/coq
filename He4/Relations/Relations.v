Require Import Coq.Relations.Relations.

Section Definitions.

Variable A : Type.
Variable R : relation A.

Definition in_domain (a : A) : Prop :=
  exists a', R a a'.

Definition in_range (a : A) : Prop :=
  exists a', R a' a.

Definition is_function : Prop :=
  forall x y1 y2,
  R x y1 ->
  R x y2 ->
  y2 = y1.

End Definitions.

Section Operators.

Variable A : Type.
Variable R : relation A.

(** Terminating reflexive transitive closure. *)

Inductive clos_refl_trans_term (x : A) : A -> Prop :=
  | rtt_term (y : A) : (forall z, R y z -> False) -> clos_refl_trans A R x y -> clos_refl_trans_term x y.

End Operators.

Section Properties.

Variable A : Type.
Variable R : relation A.

Lemma clos_refl_trans_term_is_function :
  is_function A R ->
  is_function A (clos_refl_trans_term A R).
Proof.
  intros. unfold is_function. intros.
  induction H0. induction H1.
  rename y0 into y1. rename y into y2.
  apply clos_rt_rt1n in H2.
  apply clos_rt_rt1n in H3.
  generalize dependent H0.
  generalize dependent H1.
  generalize dependent H.
  generalize dependent H2.
  generalize dependent y2.
  induction H3; subst.
  (* y1 = x *)
  - intros. inversion H2; subst.
    (* y2 = x *)
    + reflexivity.
    (* R x y /\ clos_refl_trans_1n A R y y2 *)
    + exfalso. apply (H1 y). assumption.
  (* R x y /\ clos_refl_trans_1n A R y z *) 
  - intros. inversion H2; subst.
    (* y2 = x *)
    + exfalso. apply (H4 y). assumption.
    (* R x y /\ clos_refl_trans_1n A R y y2 *)
    + apply IHclos_refl_trans_1n;
      clear IHclos_refl_trans_1n;
      try solve [assumption].
      apply (H0 x y y0 H) in H5.
      subst y0. assumption.
  Qed.

Lemma clos_refl_trans_termination_is_function:
  forall a b1 b2,
  is_function A R ->
  ~(in_domain A R b1) ->
  ~(in_domain A R b2) ->
  clos_refl_trans A R a b1 ->
  clos_refl_trans A R a b2 ->
  b2 = b1.
Proof.
  intros.
  apply clos_rt_rt1n in H2.
  apply clos_rt_rt1n in H3.
  generalize dependent H3. generalize dependent H1.
  generalize dependent H0. generalize dependent H.
  generalize dependent b2.
  induction H2.
  - intros. inversion H3; subst.
    + reflexivity.
    + exfalso. apply H0. exists y. assumption.
  - intros. inversion H4; subst.
    + exfalso. apply H3. exists y. assumption.
    + apply (H0 x y y0 H) in H5. subst y0.
      apply IHclos_refl_trans_1n; try solve [assumption].
  Qed.

End Properties.


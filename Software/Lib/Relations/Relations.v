Require Export Coq.Relations.Relations.

Section Definitions.

Variable A : Type.
Variable R : relation A.

Definition in_domain (x : A) : Prop :=
  exists y, R x y.

Definition in_range (y : A) : Prop :=
  exists x, R x y.

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

End Properties.


Module Iterator.

Section Iterators.

(** ** Signatures *)

(** Class *)

Variable A : Set.
Variable concrete_class : Set -> Set.

(** Invariant ("wf" = "well-formed") *)

Variable wf : concrete_class A -> Prop.

(** Queries *)

Variable off : concrete_class A -> bool -> Prop.
Variable after : concrete_class A -> bool -> Prop.
Variable item : concrete_class A -> A -> Prop.

(** Commands *)

Variable forth : concrete_class A -> concrete_class A -> Prop.

(** ** Derived properties *)

(** *** States *)

Definition at_start x : Prop := off x true /\ after x false.
Definition at_finish x : Prop := off x true /\ after x true.
Definition at_intermediate x : Prop := off x false /\ after x false.

(** ** Constraints *)

Definition wf_state :=
  forall x,
    wf x ->
    at_start x \/ at_intermediate x \/ at_finish x.

Definition off_deterministic :=
  forall x,
    wf x ->
    forall b,
      off x b ->
      forall b',
        off x b' ->
        b' = b.

Definition after_deterministic :=
  forall x,
    wf x ->
    forall b,
      after x b ->
      forall b',
        after x b' ->
        b' = b.

Definition item_deterministic :=
  forall x,
    wf x ->
    forall a,
      item x a ->
      forall a',
        item x a' ->
        a' = a.

(** *** Derived constraints *)

Definition wf_constraint :=
  forall x,
    wf x ->
    ~(off x false /\ after x true).

Lemma wf_state_iff_wf_constraint :
  off_deterministic ->
  after_deterministic ->
  (wf_state <-> wf_constraint).
Proof.
  unfold wf_state, wf_constraint, not, off_deterministic, after_deterministic. split.
  - intros H1 x H2 [H3 H4]. destruct (H1 x H2) as [[H5 H6] | [[H5 H6] | [H5 H6]]].
    + apply (H x H2 false H3 true) in H5. discriminate H5.
    + apply (H0 x H2 true H4 false) in H6. discriminate H6.
    + apply (H x H2 false H3 true) in H5. discriminate H5.
  - intros H1 x H2. unfold at_start, at_intermediate, at_finish.
  Abort.

(** Specification domains. *)

Function dom_off x : Prop := wf x.
Function dom_after x : Prop := wf x.
Function dom_item x : Prop := wf x /\ off x false.
Function dom_forth x : Prop := wf x /\ after x false.

(** Well-formed constraints *)

Definition after_T_off_F_not_wf :=
  forall x,
    after x true ->
    off x false ->
    ~(wf x).

(** Specification domains map. *)

Definition ex_dom_off :=
  forall x,
    dom_off x ->
    exists b, off x b.

Definition ex_dom_after :=
  forall x,
    dom_after x ->
    exists b, after x b.

Definition ex_dom_item :=
  forall x,
    dom_item x ->
    exists a, item x a.

Definition ex_dom_forth :=
  forall x,
    dom_forth x ->
    exists x', forth x x' /\ wf x'.

(** Semantic constraints. *)

Definition off_if_after :=
  forall x,
    after x true ->
    off x true.

Definition range_forth :=
  forall x x',
    forth x x' ->
    off x' false \/ after x' true.

(** Implied constraints *)

End Iterators.

End Iterator.
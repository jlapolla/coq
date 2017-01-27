Require Import He4.Discussion.LanguageBase.

Import ObjectOrientedNotations.
Delimit Scope oo_scope with oo.

Inductive cl : Type :=
  | CLNatRangeIterator : cl.

Inductive fn : Type :=
  | FNNatRangeIterator_make : fn
  | FNget_at_start : fn
  | FNget_count : fn
  | FNget_first : fn
  | FNset_at_start : fn
  | FNset_count : fn
  | FNset_first : fn
.

Definition tm := tm cl fn.

Definition tvoid := @tvoid cl fn.
Definition tnat := @tnat cl fn.
Definition tbool := @tbool cl fn.
Definition tnot := @tnot cl fn.
Definition tand := @tand cl fn.
Definition tor := @tor cl fn.
Definition tplus := @tplus cl fn.
Definition tminus := @tminus cl fn.
Definition tmult := @tmult cl fn.
Definition tvar := @tvar cl fn.
Definition tref := @tref cl fn.
Definition tassign := @tassign cl fn.
Definition tseq := @tseq cl fn.
Definition trc := @trc cl fn.
Definition tcall := @tcall cl fn.
Definition texec := @texec cl fn.
Definition treturn := @treturn cl fn.
Definition tcl := @tcl cl fn.
Definition tnew := @tnew cl fn.
Definition tdefault := @tdefault cl fn.
Definition tfield_r := @tfield_r cl fn.
Definition tfield_w := @tfield_w cl fn.

Definition stack := stack cl fn.
Definition store := store cl fn.

Definition rc_create := rc_create cl fn.

Definition called_on_class (c : cl) (sk : stack) (sr : store) : Prop :=
  exists n, sk_read_hd 0 sk = tref n /\ (exists t, sr_read n sr = tcl c t).

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm (prod stack store)) -> (prod tm (prod stack store)) -> Prop :=
  | STbase :
    forall x x',
    step_base cl fn x x' ->
    step x x'

  | STexec_NatRangeIterator_make :
    forall sk sr,
    texec FNNatRangeIterator_make / pair sk sr ==> (
    let first := tvar 0 in
    let count := tvar 1 in
    let this  := tvar 2 in
    (
      this ::= tnew 3 CLNatRangeIterator;
      this#FNset_at_start|(tbool true)|;
      this#FNset_first|(first)|;
      this#FNset_count|(count)|;
      this
    )%oo) / pair (sk_resize_hd 3 sk) sr
  | STexec_get_at_start :
    forall sk sr,
    called_on_class CLNatRangeIterator sk sr ->
    texec FNget_at_start / pair sk sr ==> (
    let this := tvar 0 in
    (
      this@0
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_get_count :
    forall sk sr,
    called_on_class CLNatRangeIterator sk sr ->
    texec FNget_count / pair sk sr ==> (
    let this := tvar 0 in
    (
      this@1
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_get_first :
    forall sk sr,
    called_on_class CLNatRangeIterator sk sr ->
    texec FNget_first / pair sk sr ==> (
    let this := tvar 0 in
    (
      this@2
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_set_at_start :
    forall sk sr,
    called_on_class CLNatRangeIterator sk sr ->
    texec FNset_at_start / pair sk sr ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@0 <- value
    )%oo) / pair (sk_resize_hd 2 sk) sr
  | STexec_set_count :
    forall sk sr,
    called_on_class CLNatRangeIterator sk sr ->
    texec FNset_count / pair sk sr ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@1 <- value
    )%oo) / pair (sk_resize_hd 2 sk) sr
  | STexec_set_first :
    forall sk sr,
    called_on_class CLNatRangeIterator sk sr ->
    texec FNset_first / pair sk sr ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@2 <- value
    )%oo) / pair (sk_resize_hd 2 sk) sr

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).


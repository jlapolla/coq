Require Import Software.Language.DynamicBinding.
Require Import Software.Language.State.
Require Import Software.Language.ExecutionProp.
Require Import Software.Language.Syntax.
Import ObjectOrientedNotations.

Section Steps.
Open Scope oo_scope.

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive exec_step : exec_step_relation :=
  | STexec_NatRangeIterator_make :
    forall st,
    texec "NatRangeIterator_make" / st ==> (
    let first := tvar 0 in
    let count := tvar 1 in
    let this  := tvar 2 in
    (
      this ::= tnew 3 "NatRangeIterator";
      this#"set_at_start"|(tbool true)|;
      this#"set_first"|(first)|;
      this#"set_count"|(count)|;
      this
    )) / resize_sk_hd 3 st
  | STexec_NatRangeIterator_get_at_start :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "get_at_start" / st ==> (
    let this := tvar 0 in
    (
      this@0
    )) / resize_sk_hd 1 st
  | STexec_NatRangeIterator_get_count :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "get_count" / st ==> (
    let this := tvar 0 in
    (
      this@1
    )) / resize_sk_hd 1 st
  | STexec_NatRangeIterator_get_first :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "get_first" / st ==> (
    let this := tvar 0 in
    (
      this@2
    )) / resize_sk_hd 1 st
  | STexec_NatRangeIterator_set_at_start :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "set_at_start" / st ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@0 <- value
    )) / resize_sk_hd 2 st
  | STexec_NatRangeIterator_set_count :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "set_count" / st ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@1 <- value
    )) / resize_sk_hd 2 st
  | STexec_NatRangeIterator_set_first :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "set_first" / st ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@2 <- value
    )) / resize_sk_hd 2 st
  | STexec_NatRangeIterator_off :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "off" / st ==> (
    let this := tvar 0 in
    (
      this#"get_count"|()| \== (tnat 0) \|| this#"get_at_start"|()|
    )) / resize_sk_hd 1 st
  | STexec_NatRangeIterator_after :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "after" / st ==> (
    let this := tvar 0 in
    (
      this#"get_count"|()| \== (tnat 0) \&& !this#"get_at_start"|()|
    )) / resize_sk_hd 1 st
  | STexec_NatRangeIterator_forth :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "forth" / st ==> (
    let this := tvar 0 in
    (
      \if this#"get_at_start"|()|
      \then
        this#"set_at_start"|(tbool false)|
      \else
        this#"set_first"|(this#"get_first"|()| \+ tnat 1)|;
        this#"set_count"|(this#"get_count"|()| \- tnat 1)|
      \fi
    )) / resize_sk_hd 1 st
  | STexec_NatRangeIterator_item :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "item" / st ==> (
    let this := tvar 0 in
    (
      this#"get_first"|()|
    )) / resize_sk_hd 1 st

  where "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2)).

Lemma value_irreducible__exec_step:
  value_irreducible exec_step.
Proof with auto.
  intros t Hval.
  induction Hval;
  try solve [intros t' st st' Hcontra; inversion Hcontra].
  Qed.

Lemma deterministic__exec_step:
  deterministic exec_step.
Proof with auto.
  intros x y Hxy.
  induction Hxy; intros z Hxz; inversion Hxz; subst;
  try solve [reflexivity].
  Qed.

End Steps.


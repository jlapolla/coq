Require Import He4.Language.Core.

Import ObjectOrientedNotations.
Delimit Scope oo_scope with oo.

Definition called_on_class (c : string) (st : state) : Prop :=
  exists n, read_sk_hd 0 st = tref n /\ (exists t, read_sr n st = tcl c t).

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm state) -> (prod tm state) -> Prop :=
  | STbase :
    forall x x',
    Step.step x x' ->
    step x x'

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
    )%oo) / resize_sk_hd 3 st
  | STexec_get_at_start :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "get_at_start" / st ==> (
    let this := tvar 0 in
    (
      this@0
    )%oo) / resize_sk_hd 1 st
  | STexec_get_count :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "get_count" / st ==> (
    let this := tvar 0 in
    (
      this@1
    )%oo) / resize_sk_hd 1 st
  | STexec_get_first :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "get_first" / st ==> (
    let this := tvar 0 in
    (
      this@2
    )%oo) / resize_sk_hd 1 st
  | STexec_set_at_start :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "set_at_start" / st ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@0 <- value
    )%oo) / resize_sk_hd 2 st
  | STexec_set_count :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "set_count" / st ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@1 <- value
    )%oo) / resize_sk_hd 2 st
  | STexec_set_first :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "set_first" / st ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@2 <- value
    )%oo) / resize_sk_hd 2 st
  | STexec_off :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "off" / st ==> (
    let this := tvar 0 in
    (
      this#"get_count"|()| == (tnat 0) \|| this#"get_at_start"|()|
    )%oo) / resize_sk_hd 1 st
  | STexec_after :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "after" / st ==> (
    let this := tvar 0 in
    (
      this#"get_count"|()| == (tnat 0) \&& !this#"get_at_start"|()|
    )%oo) / resize_sk_hd 1 st
  | STexec_forth :
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
    )%oo) / resize_sk_hd 1 st
  | STexec_item :
    forall st,
    called_on_class "NatRangeIterator" st ->
    texec "item" / st ==> (
    let this := tvar 0 in
    (
      this#"get_first"|()|
    )%oo) / resize_sk_hd 1 st

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).


Require Import He4.Discussion.LanguageBase.

Import ObjectOrientedNotations.
Delimit Scope oo_scope with oo.

Definition called_on_class (c : string) (sk : stack) (sr : store) : Prop :=
  exists n, sk_read_hd 0 sk = tref n /\ (exists t, sr_read n sr = tcl c t).

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm (prod stack store)) -> (prod tm (prod stack store)) -> Prop :=
  | STbase :
    forall x x',
    LanguageBase.step x x' ->
    step x x'

  | STexec_NatRangeIterator_make :
    forall sk sr,
    texec "NatRangeIterator_make" / pair sk sr ==> (
    let first := tvar 0 in
    let count := tvar 1 in
    let this  := tvar 2 in
    (
      this ::= tnew 3 "NatRangeIterator";
      this#"set_at_start"|(tbool true)|;
      this#"set_first"|(first)|;
      this#"set_count"|(count)|;
      this
    )%oo) / pair (sk_resize_hd 3 sk) sr
  | STexec_get_at_start :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "get_at_start" / pair sk sr ==> (
    let this := tvar 0 in
    (
      this@0
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_get_count :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "get_count" / pair sk sr ==> (
    let this := tvar 0 in
    (
      this@1
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_get_first :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "get_first" / pair sk sr ==> (
    let this := tvar 0 in
    (
      this@2
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_set_at_start :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "set_at_start" / pair sk sr ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@0 <- value
    )%oo) / pair (sk_resize_hd 2 sk) sr
  | STexec_set_count :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "set_count" / pair sk sr ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@1 <- value
    )%oo) / pair (sk_resize_hd 2 sk) sr
  | STexec_set_first :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "set_first" / pair sk sr ==> (
    let this := tvar 0 in
    let value := tvar 1 in
    (
      this<@2 <- value
    )%oo) / pair (sk_resize_hd 2 sk) sr
  | STexec_off :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "off" / pair sk sr ==> (
    let this := tvar 0 in
    (
      this#"get_count"|()| == (tnat 0) \|| this#"get_at_start"|()|
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_after :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "after" / pair sk sr ==> (
    let this := tvar 0 in
    (
      this#"get_count"|()| == (tnat 0) \&& !this#"get_at_start"|()|
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_forth :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "forth" / pair sk sr ==> (
    let this := tvar 0 in
    (
      \if this#"get_at_start"|()|
      \then
        this#"set_at_start"|(tbool false)|
      \else
        this#"set_first"|(this#"get_first"|()| \+ tnat 1)|;
        this#"set_count"|(this#"get_count"|()| \- tnat 1)|
      \fi
    )%oo) / pair (sk_resize_hd 1 sk) sr
  | STexec_item :
    forall sk sr,
    called_on_class "NatRangeIterator" sk sr ->
    texec "item" / pair sk sr ==> (
    let this := tvar 0 in
    (
      this#"get_first"|()|
    )%oo) / pair (sk_resize_hd 1 sk) sr

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).


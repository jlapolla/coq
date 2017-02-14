Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Syntax.
Import ObjectOrientedNotations.

Open Scope oo_scope.

Definition wf_ex (x : term) (st : state) : Prop :=
  exists var ref at_start count first,
      x = tvar var
  /\  read_sk_hd var st = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>.

Definition wf x var ref st at_start count first : Prop :=
      x = tvar var
  /\  read_sk_hd var st = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>.

Lemma wf_implies_wf_ex:
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  wf_ex x st.
Proof.
  Abort.

Section Specs.

Variable step : step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>' t2 / st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (multi step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1 / st1 '==>*' t2 / st2 ']'").

Definition get_at_start : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  (x # "get_at_start"|()|) / st ==>* (tbool at_start) / st.

Definition get_count : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  (x # "get_count"|()|) / st ==>* (tnat count) / st.

Definition get_first : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  (x # "get_first"|()|) / st ==>* (tnat first) / st.

Definition set_at_start : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  forall val,
  (x # "set_at_start"|(val)|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(val, tnat count, tnat first)>) st.

Definition set_count : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  forall val,
  (x # "set_count"|(val)|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool at_start, val, tnat first)>) st.

Definition set_first : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  forall val,
  (x # "set_first"|(val)|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool at_start, tnat count, val)>) st.

Definition off_true : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  count = 0 \/ at_start = true ->
  (x # "off"|()|) / st ==>* (tbool true) / st.

Definition off_false : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  lt 0 count /\ at_start = false ->
  (x # "off"|()|) / st ==>* (tbool false) / st.

Definition after_true : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  count = 0 /\ at_start = false ->
  (x # "after"|()|) / st ==>* (tbool true) / st.

Definition after_false : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  lt 0 count \/ at_start = true ->
  (x # "after"|()|) / st ==>* (tbool true) / st.

Definition forth_at_start : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  at_start = true ->
  (x # "forth"|()|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool false, tnat count, tnat first)>) st.

Definition forth : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  at_start = false ->
  (x # "forth"|()|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool at_start, tnat (count - 1), tnat (first + 1))>) st.

Definition item : Prop :=
  forall x var ref st at_start count first,
  wf x var ref st at_start count first ->
  (x # "item"|()|) / st ==>* (tnat first) / st.

End Specs.

Close Scope oo_scope.


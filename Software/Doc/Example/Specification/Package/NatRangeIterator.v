Require Import Software.Lib.Relations.Relations.
Require Import Software.Language.DynamicBinding.
Require Import Software.Language.ExecutionProp.
Require Import Software.Language.State.
Require Import Software.Language.Syntax.
Require Import Software.Language.Value.
Import ObjectOrientedNotations.

Section Specs.
Open Scope oo_scope.

Definition wf_fun x ref st at_start count first : Prop :=
      x = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>
  /\  get_stack st <> nil.

Definition wf (x : term) (st : state) : Prop :=
  exists ref at_start count first,
  wf_fun x ref st at_start count first.

Variable exec_step : exec_step_relation.

Notation "t1 '/' st1 '==>' t2 '/' st2" := (exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1  /  st1  '==>'  t2  /  st2 ']'").

Notation "t1 '/' st1 '==>+' t2 '/' st2" := (clos_refl_trans_1n exec_state exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1  /  st1  '==>+'  t2  /  st2 ']'").

Notation "t1 '/' st1 '==>*' t2 '/' st2" := (clos_refl_trans_term exec_state exec_step (Cexec_state t1 st1) (Cexec_state t2 st2))
  (at level 40, st1 at level 39, t2 at level 39, format "'[' t1  /  st1  '==>*'  t2  /  st2 ']'").

Inductive transition (ref : term) (st1 st2 : state) : Prop :=
  | tr_off : forall result,
      (ref # "off"|()|) / st1 ==>* result / st2 ->
      transition ref st1 st2
  | tr_after : forall result,
      (ref # "after"|()|) / st1 ==>* result / st2 ->
      transition ref st1 st2
  | tr_forth : forall st1a result,
      (ref # "after"|()|) / st1 ==>* (tbool false) / st1a ->
      (ref # "forth"|()|) / st1 ==>* result / st2 ->
      transition ref st1 st2
  | tr_item : forall st1a result,
      (ref # "off"|()|) / st1 ==>* (tbool false) / st1a ->
      (ref # "item"|()|) / st1 ==>* result / st2 ->
      transition ref st1 st2.

Notation "ref '::' st1 '-->' st2" := (transition ref st1 st2)
  (at level 40, st1 at level 39, format "'[' ref  '::'  st1  '-->'  st2 ']'").

Notation "ref '::' st1 '-->+' st2" := (clos_refl_trans_1n state (transition ref) st1 st2)
  (at level 40, st1 at level 39, format "'[' ref  '::'  st1  '-->+'  st2 ']'").

Notation "ref '::' st1 '-->*' st2" := (clos_refl_trans_term state (transition ref) st1 st2)
  (at level 40, st1 at level 39, format "'[' ref  '::'  st1  '-->*'  st2 ']'").

Definition all_states_wf x st1 : Prop :=
  forall st2,
  x :: st1 -->+ st2 ->
  wf x st2.

Definition get_at_start : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  (x # "get_at_start"|()|) / st ==>* (tbool at_start) / st.

Definition get_count : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  (x # "get_count"|()|) / st ==>* (tnat count) / st.

Definition get_first : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  (x # "get_first"|()|) / st ==>* (tnat first) / st.

Definition set_at_start : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  forall val,
  value val ->
  (x # "set_at_start"|(val)|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(val, tnat count, tnat first)>) st.

Definition set_count : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  forall val,
  value val ->
  (x # "set_count"|(val)|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool at_start, val, tnat first)>) st.

Definition set_first : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  forall val,
  value val ->
  (x # "set_first"|(val)|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool at_start, tnat count, val)>) st.

Definition off_true : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  count = 0 \/ at_start = true ->
  (x # "off"|()|) / st ==>* (tbool true) / st.

Definition off_false : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  lt 0 count /\ at_start = false ->
  (x # "off"|()|) / st ==>* (tbool false) / st.

Definition after_true : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  count = 0 /\ at_start = false ->
  (x # "after"|()|) / st ==>* (tbool true) / st.

Definition after_false : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  lt 0 count \/ at_start = true ->
  (x # "after"|()|) / st ==>* (tbool true) / st.

Definition forth_at_start : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  at_start = true ->
  (x # "forth"|()|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool false, tnat count, tnat first)>) st.

Definition forth : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  at_start = false ->
  (x # "forth"|()|) / st ==>* tvoid / write_sr ref (tcl "NatRangeIterator" <(tbool at_start, tnat (count - 1), tnat (first + 1))>) st.

Definition item : Prop :=
  forall x ref st at_start count first,
  wf_fun x ref st at_start count first ->
  (x # "item"|()|) / st ==>* (tnat first) / st.

End Specs.


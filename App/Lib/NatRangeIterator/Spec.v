Require Import He4.Language.DynamicBinding.
Require Import He4.Language.State.
Require Import He4.Language.StepProp.
Require Import He4.Language.Term.
Import ObjectOrientedNotations.

Section Specs.
Open Scope oo_scope.

Definition wf (var : tm) (st : state) : Prop :=
  exists n ref at_start count first,
      var = tvar n
  /\  read_sk_hd n st = tref ref
  /\  read_sr ref st = tcl "NatRangeIterator" <(tbool at_start, tnat count, tnat first)>.

End Specs.


Require Import Software.Lib.Relations.Relations.
Require Import Software.Doc.Example.Specification.Package.NatRangeIterator.
Require Import Software.Doc.Example.System.System1Execution.
Require Import Software.Doc.Example.System.System1Tactics.
Require Import Software.Doc.Example.System.System1Verification.
Require Import Software.Language.Syntax.
Import ObjectOrientedNotations.

Open Scope oo_scope.
Open Scope exec_scope.

Lemma get_at_start :
  get_at_start exec_step.
Proof.
  unfold get_at_start. intros.
  unfold wf_fun in H. destruct H. subst x.
  Abort.

Close Scope exec_scope.
Close Scope oo_scope.


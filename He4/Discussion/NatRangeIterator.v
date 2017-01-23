Module NatRangeIterator.

Inductive tm : Type :=
  | tvoid : tm
  | tnat : nat -> tm
  | tbool : bool -> tm
  | tvar : nat -> tm
  | tassign : tm -> tm -> tm
  | tref : tm -> tm
  | tderef : tm -> tm
  | tloc : nat -> tm
  | tseq : tm -> tm -> tm

  (* Classes *)
  | tNatRangeIterator : tm -> tm -> tm -> tm -> tm

  (* Named functions *)
  | tf1_get_first : tm -> tm
  | tf2_set_first : tm -> tm -> tm
  | tf1_get_count : tm -> tm
  | tf2_set_count : tm -> tm -> tm
  | tf1_off : tm -> tm
  | tf1_after : tm -> tm
  | tf1_forth : tm -> tm
  | tf1_item : tm -> tm
  | tf3_test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop := .

Notation "t ',get_first()'" :=
  (tf1_get_first t) (at level 0, format "t ',get_first()'") : oo_scope.

Notation "t1 ',set_first(' t2 ')'" :=
  (tf2_set_first t1 t2) (at level 0, format "t1 ',set_first(' t2 ')'") : oo_scope.

Notation "t1 ',test(' t2 , t3 ')'" :=
  (tf3_test t1 t2 t3) (at level 0, format "t1 ',test(' t2 ,  t3 ')'") : oo_scope.

Delimit Scope oo_scope with oo.

Example ex_comma_notation1 :
  ((tbool false),get_first(),get_first())%oo = tf1_get_first (tf1_get_first (tbool false)).
Proof. reflexivity. Qed.

Example ex_comma_notation2 :
  ((tbool false),set_first(tnat 3),get_first())%oo = tf1_get_first (tf2_set_first (tbool false) (tnat 3)).
Proof. reflexivity. Qed.

Example ex_comma_notation3 :
  ((tbool false),test(tnat 3, tnat 4))%oo = tf3_test (tbool false) (tnat 3) (tnat 4).
Proof. reflexivity. Qed.

Notation "t1 ;; t2" :=
  (tseq t1 t2) (at level 80, right associativity).

End NatRangeIterator.

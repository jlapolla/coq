Module NatRangeIterator.

Require Import He4.Discussion.ProgramState.

Inductive f1 : Type :=
  | F1get_first : f1.

Inductive f2 : Type :=
  | F2set_first : f2.

Inductive cl : Type :=
  | CLNatRangeIterator : cl.

Inductive ty : Type :=

  (* Base types *)
  | Tvoid : ty
  | Tnat : ty
  | Tbool : ty
  | Tref : ty -> ty

  (* Classes *)
  | Tclass : cl -> ty.

Inductive tm : Type :=

  (* Base types *)
  | tvoid : tm
  | tnat : nat -> tm
  | tbool : bool -> tm

  (* Variables and references *)
  | tvar : nat -> tm
  | tassign : tm -> tm -> tm
  | tref : nat -> tm

  (* Structures *)
  | tpair : tm -> tm -> tm

  (* Control flow *)
  | tseq : tm -> tm -> tm

  (* Named functions *)
  | tf1 : f1 -> tm -> tm
  | tf2 : f2 -> tm -> tm -> tm

  (* Classes *)
  | tnew : cl -> tm.

Inductive value : tm -> Prop :=

  (* Base types *)
  | vvoid : value tvoid
  | vnat : forall n, value (tnat n)
  | vbool : forall b, value (tbool b)
  | vref : forall n, value (tref n)
  | vpair :
    forall t1 t2,
    value t1 ->
    value t2 ->
    value (tpair t1 t2)

  (* Expanded classes (no reference type classes) *).

Definition stack := @ProgramState.stack (prod ty tm).
Definition store := @ProgramState.store (prod ty tm).
Definition sk_read (n : nat) (sk : stack) := ProgramState.sk_read n sk (pair Tvoid tvoid).
Definition sr_read (n : nat) (sr : store) := ProgramState.sr_read n sr (pair Tvoid tvoid).

(** We encode objects as nested [tpair] terms. This allows us to
    implement a garbage collector that walks the stack looking for
    references, then walks each referenced object in the store to find
    reachable references. At least, that's what I have in mind for the
    future. *)

Fixpoint rec_gen (n : nat) : tm :=
  match n with
  | O => tvoid
  | S n' => tpair tvoid (rec_gen n')
  end.

Compute rec_gen 2.

Fixpoint rec_write (n : nat) (v t : tm) : tm :=
  match n with
  | O =>
    match t with
    | tpair t0 t1 => tpair v t1
    | _ => v
    end
  | S n' =>
    match t with
    | tpair t0 t1 => tpair t0 (rec_write n' v t1)
    | _ => t
    end
  end.

Compute rec_gen 3.
Compute rec_write 0 (tbool true) (rec_gen 3).
Compute rec_write 1 (tbool true) (rec_gen 3).
Compute rec_write 2 (tbool false) (rec_write 3 (tbool true) (rec_gen 3)).
Compute rec_write 5 (tbool false) (rec_write 3 (tbool true) (rec_gen 3)).
Compute rec_write 2 (tbool true) (rec_gen 3).
Compute rec_write 3 (tbool true) (rec_gen 3).
Compute rec_write 4 (tbool true) (rec_gen 3).
Compute rec_write 5 (tbool true) (rec_gen 3).
Compute rec_gen 3.

Fixpoint rec_read (n : nat) (t : tm) : tm :=
  match n with
  | O =>
    match t with
    | tpair t0 t1 => t0
    | _ => t
    end
  | S n' =>
    match t with
    | tpair t0 t1 => rec_read n' t1
    | _ => tvoid
    end
  end.

Compute rec_gen 3.
Compute rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3)).
Compute rec_read 0 (rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3))).
Compute rec_read 1 (rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3))).
Compute rec_read 2 (rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3))).
Compute rec_read 3 (rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3))).
Compute rec_read 4 (rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3))).
Compute rec_read 5 (rec_write 3 (tbool true) (rec_write 2 (tbool false) (rec_gen 3))).


Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : (prod tm (prod stack store)) -> (prod tm (prod stack store)) -> Prop :=
  | STvar :
    forall n sk sr,
    (tvar n) / (pair sk sr) ==> snd (sk_read n sk) / (pair sk sr)

  | STassign_r :
    forall n t2 t2' st st',
    t2 / st ==> t2' / st' ->
    tassign (tvar n) t2 / st ==> tassign (tvar n) t2' / st'
  | STassign_nat :
    forall n m sk sr,
    tassign (tvar n) (tnat m) / (pair sk sr) ==> tvoid / (pair (sk_write n (pair Tnat (tnat m)) sk) sr)
  | STassign_bool :
    forall n b sk sr,
    tassign (tvar n) (tbool b) / (pair sk sr) ==> tvoid / (pair (sk_write n (pair Tbool (tbool b)) sk) sr)
  | STassign_ref :
    forall n r sk sr,
    tassign (tvar n) (tref r) / (pair sk sr) ==> tvoid / (pair (sk_write n (pair (Tref (fst (sr_read r sr))) (tref r)) sk) sr)

  | STpair_l :
    forall t1 t1' t2 st st',
    t1 / st ==> t1' / st' ->
    tpair t1 t2 / st ==> tpair t1' t2 / st'
  | STpair_r :
    forall v1 t2 t2' st st',
    value v1 ->
    t2 / st ==> t2' / st' ->
    tpair v1 t2 / st ==> tpair v1 t2' / st'

  | STseq_l :
    forall t1 t1' t2 st st',
    t1 / st ==> t1' / st' ->
    tseq t1 t2 / st ==> tseq t1' t2 / st'
  | STseq :
    forall t2 st,
    tseq tvoid t2 / st ==> t2 / st

  | STf1_1 :
    forall f1 t1 t1' st st',
    t1 / st ==> t1' / st' ->
    tf1 f1 t1 / st ==> tf1 f1 t1' / st'
  | STf2_1 :
    forall f2 t1 t1' t2 st st',
    t1 / st ==> t1' / st' ->
    tf2 f2 t1 t2 / st ==> tf2 f2 t1' t2 / st'
  | STf2_2 :
    forall f2 v1 t2 t2' st st',
    value v1 ->
    t2 / st ==> t2' / st' ->
    tf2 f2 v1 t2 / st ==> tf2 f2 v1 t2' / st'

  (* Classes *)
  | STnew_NatRangeIterator :
    sr' = alloc (pair (Tclass CLNatRangeIterator)  ) sr ->
    tnew CLNatRangeIterator / (pair sk sr) ==>

  where "t1 '/' st1 '==>' t2 '/' st2" := (step (pair t1 st1) (pair t2 st2)).

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

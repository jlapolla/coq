
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



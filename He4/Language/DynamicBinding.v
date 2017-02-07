Require Import Coq.Strings.String.
Require Import He4.Language.State.
Require Import He4.Language.Term.

Definition called_on_class (c : string) (st : state) : Prop :=
  exists n, read_sk_hd 0 st = tref n /\ (exists t, read_sr n st = tcl c t).

Definition called_on_classb (c : string) (st : state) : bool :=
  match read_sk_hd 0 st with
  | tref n =>
    match read_sr n st with
    | tcl c _ => true
    | _ => false
    end
  | _ => false
  end.

Definition called_on_vclass (c : string) (st : state) : Prop :=
  exists t, read_sk_hd 0 st = tcl c t.

Definition called_on_vclassb (c : string) (st : state) : bool :=
  match read_sk_hd 0 st with
  | tcl c _ => true
  | _ => false
  end.


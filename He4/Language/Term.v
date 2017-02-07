Require Import Coq.Strings.String.

Inductive tm : Type :=

  (* Base types *)
  | tvoid : tm
  | tnat : nat -> tm
  | tbool : bool -> tm

  (* Boolean operators *)
  | tnot : tm -> tm
  | tand : tm -> tm -> tm
  | tor : tm -> tm -> tm

  (* Numeric operators *)
  | tplus : tm -> tm -> tm
  | tminus : tm -> tm -> tm
  | tmult : tm -> tm -> tm

  (* Equality operators *)
  | teq : tm -> tm -> tm

  (* Variables and references *)
  | tvar : nat -> tm
  | tref : nat -> tm
  | tassign : tm -> tm -> tm

  (* Control flow *)
  | tseq : tm -> tm -> tm
  | tif : tm -> tm -> tm -> tm
  | twhile : tm -> tm -> tm

  (* Records *)
  | trc : tm -> tm -> tm

  (* Functions *)
  | tcall : string -> tm -> tm
  | texec : string -> tm
  | treturn : tm -> tm
  | trefpass : tm -> tm

  (* Classes *)
  | tcl : string -> tm -> tm

  (* Reference types *)
  | tnew : nat -> string -> tm
  | tfield_r : nat -> tm -> tm
  | tfield_w : nat -> tm -> tm -> tm

  (* Value types *)
  | tvnew : nat -> string -> tm
  | tvfield_r : nat -> tm -> tm
  | tvfield_w : nat -> tm -> tm -> tm.

Module ObjectOrientedNotations.

Notation "'<(' t ')>'" := (trc t tvoid) (format "'<(' t ')>'") : oo_scope.

Notation "'<(' t ',' .. ',' t0 ')>'" :=
  (trc t .. (trc t0 tvoid) ..) (format "'<(' t ','  .. ','  t0 ')>'") : oo_scope.

Notation "t '@' n0" :=
  (tfield_r n0 t) (at level 26, left associativity, format "t  '@'  n0") : oo_scope.

Notation "t '?@' n0" :=
  (tvfield_r n0 t) (at level 26, left associativity, format "t  '?@'  n0") : oo_scope.

Notation "t '#' f '|(' ')|'" :=
  (tcall f (trc t tvoid)) (at level 26, left associativity, format "t  '#'  f '|(' ')|'") : oo_scope.

Notation "t '#' f '|(' t0 ')|'" :=
  (tcall f (trc t t0)) (at level 26, left associativity, format "t  '#'  f '|(' t0 ')|'") : oo_scope.

Notation "t '#' f '|(' t0 ',' .. ',' t1 ')|'" :=
  (tcall f (trc t (trc t0 .. (trc t1 tvoid) ..))) (at level 26, left associativity, format "t  '#'  f '|(' t0 ','  .. ','  t1 ')|'") : oo_scope.

Notation "'!' t" :=
  (tnot t) (at level 35, right associativity, format "'!' t") : oo_scope.

Notation "'\ref' t" :=
  (trefpass t) (at level 35, right associativity, format "'\ref'  t") : oo_scope.

Notation "t '\*' t0" :=
  (tmult t t0) (at level 40, left associativity, format "t  '\*'  t0") : oo_scope.

Notation "t '\+' t0" :=
  (tplus t t0) (at level 45, left associativity, format "t  '\+'  t0") : oo_scope.

Notation "t '\-' t0" :=
  (tminus t t0) (at level 45, left associativity, format "t  '\-'  t0") : oo_scope.

Notation "t '==' t0" :=
  (teq t t0) (at level 50, left associativity, format "t  '=='  t0") : oo_scope.

Notation "t \&& t0" :=
  (tand t t0) (at level 55, left associativity, format "t  '\&&'  t0") : oo_scope.

Notation "t '\||' t0" :=
  (tor t t0) (at level 61, left associativity, format "t  '\||'  t0") : oo_scope.

Notation "t '<@' n0 '<-' t1" :=
  (tfield_w n0 t1 t) (at level 70, format "t '<@' n0  '<-'  t1") : oo_scope.

Notation "t '<?@' n0 '<-' t1" :=
  (tvfield_w n0 t1 t) (at level 70, format "t '<?@' n0  '<-'  t1") : oo_scope.

Notation "t '::=' t0" :=
  (tassign t t0) (at level 70, right associativity) : oo_scope.

Notation "t ; t0" :=
  (tseq t t0) (at level 80, right associativity, format "'[v' t ';' '/' t0 ']'") : oo_scope.

Notation "'\if' t '\then' t0 '\else' t1 '\fi'" :=
  (tif t t0 t1) (at level 80, right associativity, format "'[' '\if'  t '//' '[v  ' '\then' '/' '[' t0 ']' ']' '//' '[v  ' '\else' '/' '[' t1 ']' ']' '//' '\fi' ']'") : oo_scope.

Notation "'\while' t '\do' t0 '\done'" :=
  (twhile t t0) (at level 80, right associativity, format "'[' '\while'  t '//' '[v  ' '\do' '/' '[' t0 ']' ']' '//' '\done' ']'") : oo_scope.

End ObjectOrientedNotations.


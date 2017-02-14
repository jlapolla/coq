Require Import Software.Lib.Strings.String.

Inductive term : Type :=

  (* Base types *)
  | tvoid : term
  | tnat : nat -> term
  | tbool : bool -> term

  (* Boolean operators *)
  | tnot : term -> term
  | tand : term -> term -> term
  | tor : term -> term -> term

  (* Numeric operators *)
  | tplus : term -> term -> term
  | tminus : term -> term -> term
  | tmult : term -> term -> term

  (* Equality operators *)
  | teq : term -> term -> term

  (* Variables and references *)
  | tvar : nat -> term
  | tref : nat -> term
  | tassign : term -> term -> term

  (* Control flow *)
  | tseq : term -> term -> term
  | tif : term -> term -> term -> term
  | twhile : term -> term -> term

  (* Records *)
  | trc : term -> term -> term

  (* Functions *)
  | tcall : string -> term -> term
  | texec : string -> term
  | treturn : term -> term
  | trefpass : term -> term

  (* Classes *)
  | tcl : string -> term -> term

  (* Reference types *)
  | tnew : nat -> string -> term
  | tfield_r : nat -> term -> term
  | tfield_w : nat -> term -> term -> term

  (* Value types *)
  | tvnew : nat -> string -> term
  | tvfield_r : nat -> term -> term
  | tvfield_w : nat -> term -> term -> term.

Module ObjectOrientedNotations.

Notation "'<(' t ')>'" := (trc t tvoid) (format "'<(' t ')>'") : oo_scope.

Notation "'<(' t ',' .. ',' t0 ')>'" :=
  (trc t .. (trc t0 tvoid) ..) (format "'<(' t ','  .. ','  t0 ')>'") : oo_scope.

Notation "t '@' n0" :=
  (tfield_r n0 t) (at level 25, left associativity, format "t  '@'  n0") : oo_scope.

Notation "t '?@' n0" :=
  (tvfield_r n0 t) (at level 25, left associativity, format "t  '?@'  n0") : oo_scope.

Notation "t '#' f '|(' ')|'" :=
  (tcall f (trc t tvoid)) (at level 25, left associativity, format "t  '#'  f '|(' ')|'") : oo_scope.

Notation "t '#' f '|(' t0 ')|'" :=
  (tcall f (trc t t0)) (at level 25, left associativity, format "t  '#'  f '|(' t0 ')|'") : oo_scope.

Notation "t '#' f '|(' t0 ',' .. ',' t1 ')|'" :=
  (tcall f (trc t (trc t0 .. (trc t1 tvoid) ..))) (at level 25, left associativity, format "t  '#'  f '|(' t0 ','  .. ','  t1 ')|'") : oo_scope.

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

Notation "t '\==' t0" :=
  (teq t t0) (at level 50, left associativity, format "t  '\=='  t0") : oo_scope.

Notation "t \&& t0" :=
  (tand t t0) (at level 55, left associativity, format "t  '\&&'  t0") : oo_scope.

Notation "t '\||' t0" :=
  (tor t t0) (at level 65, left associativity, format "t  '\||'  t0") : oo_scope.

Notation "t '<@' n0 '<-' t1" :=
  (tfield_w n0 t1 t) (at level 70, format "t  '<@'  n0  '<-'  t1") : oo_scope.

Notation "t '<?@' n0 '<-' t1" :=
  (tvfield_w n0 t1 t) (at level 70, format "t  '<?@'  n0  '<-'  t1") : oo_scope.

Notation "t '::=' t0" :=
  (tassign t t0) (at level 70, right associativity) : oo_scope.

Notation "t ; t0" :=
  (tseq t t0) (at level 80, right associativity, format "'[' t ';' '//' t0 ']'") : oo_scope.

Notation "'\if' t '\then' t0 '\else' t1 '\fi'" :=
  (tif t t0 t1) (at level 80, right associativity, format "'[' '\if'  t '//' '[v  ' '\then' '/' '[' t0 ']' ']' '//' '[v  ' '\else' '/' '[' t1 ']' ']' '//' '\fi' ']'") : oo_scope.

Notation "'\while' t '\do' t0 '\done'" :=
  (twhile t t0) (at level 80, right associativity, format "'[' '\while'  t '//' '[v  ' '\do' '/' '[' t0 ']' ']' '//' '\done' ']'") : oo_scope.

End ObjectOrientedNotations.


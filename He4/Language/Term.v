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

Notation "'|(' ')|'" := tvoid (at level 20, format "'|(' ')|'") : oo_scope.

Notation "'|(' t ')|'" := (trc t tvoid) (at level 20, format "'|(' t ')|'") : oo_scope.

Notation "'|(' t ',' .. ',' t0 ')|'" :=
  (trc t .. (trc t0 tvoid) ..) (at level 20, format "'|(' t ','  .. ','  t0 ')|'") : oo_scope.

Notation "t '@' n0" :=
  (tfield_r n0 t) (at level 26, left associativity, format "t '@' n0") : oo_scope.

Notation "t '?@' n0" :=
  (tvfield_r n0 t) (at level 26, left associativity, format "t '?@' n0") : oo_scope.

Notation "t '#' f t0" :=
  (tcall f (trc t t0)) (at level 26, left associativity, format "t  '#'  f t0") : oo_scope.

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
  (tseq t t0) (at level 80, right associativity, format "'[v' t ';' '/' t0 ']'").

Notation "'\if' t '\then' t0 '\else' t1 '\fi'" :=
  (tif t t0 t1) (at level 80, right associativity, format "'[' '\if'  t '//' '[v  ' '\then' '/' '[' t0 ']' ']' '//' '[v  ' '\else' '/' '[' t1 ']' ']' '//' '\fi' ']'") : oo_scope.

Notation "'\while' t '\do' t0 '\done'" :=
  (twhile t t0) (at level 80, right associativity, format "'[' '\while'  t '//' '[v  ' '\do' '/' '[' t0 ']' ']' '//' '\done' ']'") : oo_scope.

Section Examples.

Delimit Scope oo_scope with oo.

Example ex_oo_notation_1:
  (!(tbool true) \|| (tbool false) \&& (tbool false))%oo = tor (tnot (tbool true)) (tand (tbool false) (tbool false)).
Proof. reflexivity. Abort.

Example ex_trefpass:
  (tnat 1#"get_first"|(\ref tnat 2, tnat 4)|)%oo = tcall "get_first" (trc (tnat 1) (trc (trefpass (tnat 2)) (trc (tnat 4) tvoid))).
Proof. reflexivity. Abort.

Example ex_oo_notation_2:
  ((tnat 1) \* (tnat 2) \- (tnat 3) \+ (tnat 4) \* (tnat 5))%oo = tplus (tminus (tmult (tnat 1) (tnat 2)) (tnat 3)) (tmult (tnat 4) (tnat 5)).
Proof. reflexivity. Abort.

Example ex_oo_notation_3:
  |()|%oo = tvoid.
Proof. reflexivity. Abort.

Example ex_oo_notation_4:
  |(tnat 2)|%oo = trc (tnat 2) tvoid.
Proof. reflexivity. Abort.

Example ex_oo_notation_5:
  |(tnat 1, tnat 2, tnat 4)|%oo = (trc (tnat 1) (trc (tnat 2) (trc (tnat 4) tvoid))).
Proof. reflexivity. Abort.

Example ex_oo_notation_6:
  ((tnat 1)#"get_first"|()| @ 2 #"get_first"|()|)%oo = tcall "get_first" (trc (tfield_r 2 (tcall "get_first" (trc (tnat 1) tvoid))) tvoid).
Proof. reflexivity. Abort.

Example ex_tvfield_r:
  ((tnat 1)#"get_first"|()| ?@ 2 #"get_first"|()|)%oo = tcall "get_first" (trc (tvfield_r 2 (tcall "get_first" (trc (tnat 1) tvoid))) tvoid).
Proof. reflexivity. Abort.

Example ex_oo_notation_6:
  ((tnat 1)#"get_first"|()| <@ 2 <- (tnat 2)#"get_first"|()|)%oo = tfield_w 2 (tcall "get_first" (trc (tnat 2) tvoid)) (tcall "get_first" (trc (tnat 1) tvoid)).
Proof. reflexivity. Abort.

Example ex_tvfield_w:
  ((tnat 1)#"get_first"|()| <?@ 2 <- (tnat 2)#"get_first"|()|)%oo = tvfield_w 2 (tcall "get_first" (trc (tnat 2) tvoid)) (tcall "get_first" (trc (tnat 1) tvoid)).
Proof. reflexivity. Abort.

Example ex_oo_notation_7:
  (tnat 1#"get_first"|(tnat 2#"get_first"|()|, tnat 4)|)%oo = tcall "get_first" (trc (tnat 1) (trc (tcall "get_first" (trc (tnat 2) tvoid)) (trc (tnat 4) tvoid))).
Proof. reflexivity. Abort.

Example ex_oo_notation_8:
  (tnat 1#"get_first"|(tnat 2)|#"get_first"|(tnat 4)|)%oo = tcall "get_first" (trc (tcall "get_first" (trc (tnat 1) (trc (tnat 2) tvoid))) (trc (tnat 4) tvoid)).
Proof. reflexivity. Abort.

Example ex_oo_notation_9:
  (tvar 1 ::= tvar 2 ::= tnat 3)%oo = tassign (tvar 1) (tassign (tvar 2) (tnat 3)).
Proof. reflexivity. Abort.

Example ex_oo_notation_10:
  (tnat 4; tnat 5; tnat 6)%oo = tseq (tnat 4) (tseq (tnat 5) (tnat 6)).
Proof. reflexivity. Abort.

Example ex_oo_notation_11:
  ((tnat 1) == (tnat 3) \|| (tbool true) == (tbool false))%oo = tor (teq (tnat 1) (tnat 3)) (teq (tbool true) (tbool false)).
Proof. reflexivity. Abort.

Example ex_oo_notation_12:
  (\if (tref 1) # "get_first"|()| == (tnat 0) \then (tvar 1) ::= (tnat 4) \else (tvar 1) ::= (tnat 5) \fi)%oo =
  tif
  (teq (tcall "get_first" (trc (tref 1) tvoid)) (tnat 0))
  (tassign (tvar 1) (tnat 4))
  (tassign (tvar 1) (tnat 5)).
Proof. reflexivity. Abort.

Example ex_oo_notation_13:
  (\while (tref 1) # "get_first"|()| == (tnat 0) \do (tvar 1) ::= (tvar 1) \- (tnat 1) \done)%oo = 
  twhile
  (teq (tcall "get_first" (trc (tref 1) tvoid)) (tnat 0))
  (tassign (tvar 1) (tminus (tvar 1) (tnat 1))).
Proof. reflexivity. Abort.

End Examples.

End ObjectOrientedNotations.


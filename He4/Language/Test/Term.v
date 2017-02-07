Require Import He4.Language.Term.
Import ObjectOrientedNotations.

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

Example ex_oo_notation_4:
  <(tnat 2)>%oo = trc (tnat 2) tvoid.
Proof. reflexivity. Abort.

Example ex_oo_notation_5:
  <(tnat 1, tnat 2, tnat 4)>%oo = (trc (tnat 1) (trc (tnat 2) (trc (tnat 4) tvoid))).
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


Require Import He4.Language.Syntax.
Import ObjectOrientedNotations.

Section Examples.

Open Scope oo_scope.

Example ex_trc_single:
  <(tnat 2)> = trc (tnat 2) tvoid.
Proof. reflexivity. Qed.

Example ex_trc_single_nested:
  let elem1 := <(tnat 2)> in
  <(<(tnat 2)>)> = <(elem1)>.
Proof. simpl. reflexivity. Qed.

Example ex_trc_multi:
  <(tnat 1, tnat 2, tnat 4)> =
    (trc (tnat 1)
    (trc (tnat 2)
    (trc (tnat 4)
      tvoid))).
Proof. reflexivity. Qed.

Example ex_trc_multi_nested:
  let elem1 := tnat 1 in
  let elem2 := <(tnat 2)> in
  let elem3 := <(tnat 4, tnat 8)> in
  <(tnat 1, <(tnat 2)>, <(tnat 4, tnat 8)>)> = <(elem1, elem2, elem3)>.
Proof. simpl. reflexivity. Qed.

Example ex_tfield_r_single:
  (tref 0) @ 2 = tfield_r 2 (tref 0).
Proof. reflexivity. Qed.

Example ex_tfield_r_multi:
  let result1 := (tref 0) @ 2 in
  (tref 0) @ 2 @ 4 = result1 @ 4.
Proof. simpl. reflexivity. Qed.

Example ex_tvfield_r_single:
  (tvar 1) ?@ 2 = tvfield_r 2 (tvar 1).
Proof. reflexivity. Qed.

Example ex_tvfield_r_multi:
  let result1 := (tvar 1) ?@ 2 in
  (tvar 1) ?@ 2 ?@ 4 = result1 ?@ 4.
Proof. simpl. reflexivity. Qed.

Example ex_tcall_chain_no_arguments_single:
  (tref 0) # "foo"|()| = tcall "foo" (trc (tref 0) tvoid).
Proof. reflexivity. Qed.

Example ex_tcall_chain_no_arguments_multi:
  let result1 := (tref 0) # "foo"|()| in
  (tref 0) # "foo"|()| # "bar"|()| = result1 # "bar"|()|.
Proof. simpl. reflexivity. Qed.

Example ex_tcall_chain_one_argument_single:
  (tref 0) # "foo"|(tnat 1)| = tcall "foo" (trc (tref 0) (trc (tnat 1) tvoid)).
Proof. reflexivity. Qed.

Example ex_tcall_chain_one_argument_multi:
  let result1 := (tref 0) # "foo"|(tnat 1)| in
  (tref 0) # "foo"|(tnat 1)| # "bar"|(tnat 2)| = result1 # "bar"|(tnat 2)|.
Proof. simpl. reflexivity. Qed.

Example ex_tcall_chain_one_argument_nested:
  let result1 := (tref 1) # "foo"|(tnat 1)| in
  (tref 0) # "foo"|((tref 1) # "foo"|(tnat 1)|)| = (tref 0) # "foo" |(result1)|.
Proof. simpl. reflexivity. Qed.

Example ex_tcall_chain_n_arguments_single:
  (tref 0) # "foo"|(tnat 1, tnat 2, tnat 3)| = tcall "foo" (trc (tref 0) (trc (tnat 1) (trc (tnat 2) (trc (tnat 3) tvoid)))).
Proof. reflexivity. Qed.

Example ex_tcall_chain_n_arguments_multi:
  let result1 := (tref 0) # "foo"|(tnat 1, tnat 2, tnat 3)| in
  (tref 0) # "foo"|(tnat 1, tnat 2, tnat 3)| # "bar"|(tnat 1, tnat 2, tnat 3)| = result1 # "bar"|(tnat 1, tnat 2, tnat 3)|.
Proof. simpl. reflexivity. Qed.

Example ex_tcall_chain_n_arguments_nested:
  let result1 := (tref 1) # "foo"|(tnat 1, tnat 2, tnat 3)| in
  (tref 0) # "foo"|(tnat 1, tnat 2, (tref 1) # "foo"|(tnat 1, tnat 2, tnat 3)|)| = (tref 0) # "foo"|(tnat 1, tnat 2, result1)|.
Proof. simpl. reflexivity. Qed.

Example ex_tnot_single:
  !tbool false = tnot (tbool false).
Proof. reflexivity. Qed.

Example ex_tnot_multi:
  let result1 := !tbool false in
  !!tbool false = !result1.
Proof. simpl. reflexivity. Qed.

Example ex_trefpass_single:
  \ref (tvar 1) = trefpass (tvar 1).
Proof. reflexivity. Qed.

Example ex_trefpass_multi:
  let result1 := \ref (tvar 1) in
  \ref \ref (tvar 1) = \ref result1.
Proof. simpl. reflexivity. Qed.

Example ex_tmult_single:
  tnat 1 \* tnat 2 = tmult (tnat 1) (tnat 2).
Proof. reflexivity. Qed.

Example ex_tmult_multi:
  let result1 := tnat 1 \* tnat 2 in
  tnat 1 \* tnat 2 \* tnat 3 = result1 \* tnat 3.
Proof. simpl. reflexivity. Qed.

Example ex_tplus_single:
  tnat 1 \+ tnat 2 = tplus (tnat 1) (tnat 2).
Proof. reflexivity. Qed.

Example ex_tplus_multi:
  let result1 := tnat 1 \+ tnat 2 in
  tnat 1 \+ tnat 2 \+ tnat 3 = result1 \+ tnat 3.
Proof. simpl. reflexivity. Qed.

Example ex_tminus_single:
  tnat 1 \- tnat 2 = tminus (tnat 1) (tnat 2).
Proof. reflexivity. Qed.

Example ex_tminus_multi:
  let result1 := tnat 1 \- tnat 2 in
  tnat 1 \- tnat 2 \- tnat 3 = result1 \- tnat 3.
Proof. simpl. reflexivity. Qed.

Example ex_teq_single:
  tvar 1 \== tvar 2 = teq (tvar 1) (tvar 2).
Proof. reflexivity. Qed.

Example ex_teq_multi:
  let result1 := tvar 1 \== tvar 2 in
  tvar 1 \== tvar 2 \== tvar 3 = result1 \== tvar 3.
Proof. simpl. reflexivity. Qed.

Example ex_tand_single:
  tvar 1 \&& tvar 2 = tand (tvar 1) (tvar 2).
Proof. reflexivity. Qed.

Example ex_tand_multi:
  let result1 := tvar 1 \&& tvar 2 in
  tvar 1 \&& tvar 2 \&& tvar 3 = result1 \&& tvar 3.
Proof. simpl. reflexivity. Qed.

Example ex_tor_single:
  tvar 1 \|| tvar 2 = tor (tvar 1) (tvar 2).
Proof. reflexivity. Qed.

Example ex_tor_multi:
  let result1 := tvar 1 \|| tvar 2 in
  tvar 1 \|| tvar 2 \|| tvar 3 = result1 \|| tvar 3.
Proof. simpl. reflexivity. Qed.

Example ex_tfield_w_single:
  tvar 1 <@ 2 <- tvar 3 = tfield_w 2 (tvar 3) (tvar 1).
Proof. reflexivity. Qed.

Example ex_tvfield_w_single:
  tvar 1 <?@ 2 <- tvar 3 = tvfield_w 2 (tvar 3) (tvar 1).
Proof. reflexivity. Qed.

Example ex_tassign_single:
  (tvar 1 ::= tvar 2) = tassign (tvar 1) (tvar 2).
Proof. reflexivity. Qed.

Example ex_tassign_multi:
  let tresult1 := tvar 2 ::= tvar 3 in
  (tvar 1 ::= tvar 2 ::= tvar 3) = (tvar 1 ::= tresult1).
Proof. simpl. reflexivity. Qed.

Example ex_tseq_single:
  (tvar 1 ::= tnat 1; tvar 2 ::= tnat 2) = tseq (tassign (tvar 1) (tnat 1)) (tassign (tvar 2) (tnat 2)).
Proof. reflexivity. Qed.

Example ex_tseq_multi:
  let result1 := tvar 2 ::= tnat 2; tvar 3 ::= tnat 3 in
  (tvar 1 ::= tnat 1; tvar 2 ::= tnat 2; tvar 3 ::= tnat 3) = (tvar 1 ::= tnat 1; result1).
Proof. simpl. reflexivity. Qed.

Example ex_tif_single:
  \if tbool true \then tbool false \else tbool true \fi = tif (tbool true) (tbool false) (tbool true).
Proof. reflexivity. Qed.

Example ex_tif_nested:
  let nested := \if tvar 1 \then tvoid \else tvoid \fi in
  \if tbool true \then \if tvar 1 \then tvoid \else tvoid \fi \else tbool true \fi = \if tbool true \then nested \else tbool true \fi.
Proof. simpl. reflexivity. Qed.

Example ex_twhile_single:
  \while tvar 1 \do tvoid \done = twhile (tvar 1) tvoid.
Proof. reflexivity. Qed.

Example ex_twhile_nested:
  let nested := \while tvar 2 \do tvoid \done in
  \while tvar 1 \do \while tvar 2 \do tvoid \done \done = twhile (tvar 1) nested.
Proof. simpl. reflexivity. Qed.

End Examples.


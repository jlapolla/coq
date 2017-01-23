Module ProgramState.

Require Import T_NatRangeIterator.

Inductive StateDataType : Type :=
  | DT_NatRangeIterator : T_NatRangeIterator.NatRangeIterator -> StateDataType.

Inductive StateTypeType {ST : Type} : Type :=
  | TT_NatRangeIterator : @T_NatRangeIterator.T_NatRangeIterator ST ->
                          StateTypeType.

Inductive ProgramState : Type :=
  | C_ProgramState: list StateDataType ->
                    list (@StateTypeType ProgramState) ->
                    ProgramState.

End ProgramState.

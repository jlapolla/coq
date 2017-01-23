Module T_NatRangeIterator.

Inductive NatRangeIterator : Type :=
  | C_NatRangeIterator: nat -> nat -> NatRangeIterator.

Definition get_first {ST : Type} := ST -> NatRangeIterator -> ST -> nat -> Prop.

Definition set_first {ST : Type} := ST -> NatRangeIterator -> nat -> ST -> Prop.

Definition get_count {ST : Type} := ST -> NatRangeIterator -> ST -> nat -> Prop.

Definition set_count {ST : Type} := ST -> NatRangeIterator -> nat -> ST -> Prop.

Definition off {ST : Type} := ST -> NatRangeIterator -> ST -> bool -> Prop.

Definition after {ST : Type} := ST -> NatRangeIterator -> ST -> bool -> Prop.

Definition forth {ST : Type} := ST -> NatRangeIterator -> ST -> Prop.

Definition item {ST : Type} := ST -> NatRangeIterator -> ST -> nat -> Prop.

Inductive T_NatRangeIterator {ST : Type} : Type :=
  | C_T_NatRangeIterator: @get_first ST ->
                          @set_first ST ->
                          @get_count ST ->
                          @set_count ST ->
                          @off ST ->
                          @after ST ->
                          @forth ST ->
                          @item ST ->
                          T_NatRangeIterator.

End T_NatRangeIterator.

(** * Library Catalog

    This chapter contains a brief description of each library in the
    [Software] library collection.

    ** [Software.Language] Libraries

    This section shows the _conceptual_ hierarchy of the
    [Software.Language] libraries. This is not the actual file system
    hierarchy.

    - [State] Library: Defines the [state] and [exec_state] (execution
      state) types. A [state] combines a [stack] and a [store] (also
      called a _heap_), and represents the traditional notion of program
      state. An [exec_state] combines a [term] (the instructions being
      executed) and a [state], and represents the entire state of single
      threaded software execution. The [State] library also defines
      functions for modifying the [state]. Note: [term] is defined in
      the [Syntax] library.
      - [Stack] Library: Defines the [stack] type, which represents the
        notion of a call stack.
      - [Store] Library: Defines the [store] type, which represents the
        notion of a free store (also called a _heap_).
      - [RefPassStack] Library: Defines the [ref_pass_stack] type, which
        tracks which variables on the [stack] were passed by reference.
    - [Syntax] Library: Defines the [term] type, which represents
      language terms and statements.
      - [ObjectOrientedNotations] Module: Notations for [term] which
        resemble an object oriented programming language.
      - [Record] Library: Defines functions for manipulating record
        [term]'s. Record [term]'s are used to represent an object's data
        fields.
    - [Execution] Library: Defines the [exec_step] (execution step)
      relation, which defines how an [exec_state] changes as program
      execution progresses.
    - [Value] Library: Defines irreducible [term]'s which cannot be
      executed further by [exec_step].
    - [DynamicBinding] Library: Defines [called_on_class] functions
      which allow a different user defined function to be called based
      on the class the function was called on.
    - [SpecProps] Library: Defines propositions that are useful when
      writing specifications for user code.

    ** [Software.Lib] Libraries

    The libraries under [Software.Lib] extend Coq's standard library.
    Each library in [Software.Lib] is named after the Coq standard
    library that it extends.

    ** [Software.Doc] Libraries

    Documentation for the [Software] libraries, in [coqdoc] format. *)

(** * Conceptual Foundations *)

Require Coq.Arith.EqNat.

Section ConceptualFoundations.

(** ** Thought Experiment

    Consider a proposition [is_my_favorite_number]. *)

Variable is_my_favorite_number : nat -> Prop.

(** Let's assume that [3] is my favorite number. *)

Variable three_is_my_favorite_number : is_my_favorite_number 3.

(** Now we'll prove a simple fact about my favorite number. *)

Fact one_plus_my_favorite_number_is_four :
  forall n,
  is_my_favorite_number n ->
  1 + n = 4.
Proof.
  intros n H.
  Fail inversion H.
  Abort.

(** Oops. Something went wrong. Intuitively, using [inversion] on [H]
    should yield a hypothesis of type [n = 3]. However, the [inversion]
    tactic fails with "Error: The type of H is not inductive." We are
    forced to [Abort] the proof.

    Why did this happen? The error indicates it has something to do with
    induction.

    Let's try another proof to better understand the issue. *)

Fact zero_is_not_my_favorite_number :
  ~(is_my_favorite_number 0).
Proof.
  intros H.
  Fail inversion H.
  Abort.

(** Interesting. We cannot prove that zero is not my favorite number,
    and we know it has something to do with induction.

    The root of the problem is that we can prove the following: *)

Fact three_implies_is_my_favorite_number :
  forall n,
  n = 3 ->
  is_my_favorite_number n.
Proof.
  intros. subst n.
  apply three_is_my_favorite_number.
  Qed.

(** But we cannot prove its inverse: *)

Fact is_my_favorite_number_implies_three :
  forall n,
  is_my_favorite_number n ->
  n = 3.
Proof.
  intros.
  Fail inversion H.
  Abort.

(** Let's try again with an inductive definition of
    [is_my_favorite_number]. *)

Inductive is_my_favorite_number_inductive : nat -> Prop :=
  | three_is_my_favorite_number_inductive : is_my_favorite_number_inductive 3.

(** And let's try those same proofs again. *)

Fact one_plus_my_favorite_number_is_four' :
  forall n,
  is_my_favorite_number_inductive n ->
  1 + n = 4.
Proof.
  intros n H.
  inversion H.
  reflexivity.
  Qed.

Fact zero_is_not_my_favorite_number' :
  ~(is_my_favorite_number_inductive 0).
Proof.
  intros H.
  inversion H.
  Qed.

(** The proofs succeed. But why?

    The key is that our inductive definition says more than just [3] is
    my favorite number. It also says that [3] is the _ONLY_ number that
    is my favorite number. In other words, no other number satisfies the
    [is_my_favorite_number_inductive] proposition.

    In more mathematical terms, the only inhabitants of the proof type
    [is_my_favorite_number_inductive n] are those listed in the
    inductive definition. In this case, the only inhabitant of the proof
    type is [three_is_my_favorite_number_inductive]. Note that
    [three_is_my_favorite_number_inductive] is literally a proof of
    [is_my_favorite_number_inductive 3].

    We are able to use the [inversion] tactic on an inductive definition
    because the inductive definition enumerates _ALL_ the proofs which
    inhabit the proof type. Therefore, we can do case analysis by
    looking at each possible inhabitant one at a time.

    Note that we can achieve a similar effect without induction by
    defining cases when [is_my_favorite_number] is [False]. *)

Variable no_number_besides_three_is_my_favorite_number:
  forall n,
  n <> 3 -> ~(is_my_favorite_number n).

Fact one_plus_my_favorite_number_is_four'' :
  forall n,
  is_my_favorite_number n ->
  1 + n = 4.
Proof.
  intros n H.
  destruct (EqNat.beq_nat n 3) eqn:H0.
  - apply EqNat.beq_nat_true_iff in H0. subst n. reflexivity.
  - apply EqNat.beq_nat_false_iff in H0.
    apply no_number_besides_three_is_my_favorite_number in H0.
    apply H0 in H. inversion H.
  Qed.

Fact zero_is_not_my_favorite_number'' :
  ~(is_my_favorite_number 0).
Proof.
  apply no_number_besides_three_is_my_favorite_number.
  intros H. inversion H.
  Qed.

(** Without induction, the proofs are more convoluted.

    Note that inductive definitions also have other advantages besides
    simpler proofs. Namely, Coq auto generates induction rules for
    inductive definitions.

    ** Inductive Definitions, Concrete Classes

    Conceptually, an inductive definition fully defines and constrains
    all inhabitants of its type. After an inductive definition is
    established, we cannot define any additional inhabitants of the
    type. This has important consequences for modelling object oriented
    software in Coq.

    Consider what happens when we use an inductive definition to define
    the behavior of a class. The inductive definition says everything
    that the class does. Furthermore, it says that the class does not do
    anything else. The latter restriction means that we cannot implement
    _any_ variant or additional behavior in a subclass. Therefore,
    inductive definitions are not suitable for abstract classes and
    interfaces. They are only suitable for concrete classes. To put it
    another way: once we have an inductive definition of a class, we
    have explicitly defined all members of the class. No additional
    members (subclasses) can be added after that point.

    It is important to note that by defining class behavior inductively,
    we are relieved of the burden of stating what the class does _not_
    do. This is just like the example above: to use the non-inductive
    definition of [is_my_favorite_number] we had to define all cases
    where [is_my_favorite_number] is [False]. With the inductive
    definition, we did not need to enumerate the [False] cases; the
    inductive definition takes care of that for us. If we apply this
    concept to class definitions, this is good news. There are
    infinitely many things that a class does _not_ do, so it's a good
    thing that we don't have to enumerate them.

    Consider further that enumerating both [True] and [False] cases is
    inherently error-prone and dangerous. What if we accidentally
    introduce some overlap between the [True] and [False] cases? Then
    we have an inconsistency, and the principle of explosion applies.

    ** Regular Definitions, Abstract Classes

    Contrast an inductive definition with a regular definition. When we
    define a type with a regular definition, we do not know how many
    inhabitants the type has. In fact, the inhabitants of the type may
    be uncountable. We can define inhabitants later, and verify that
    they satisfy the definition.

    This means regular definitions are suitable for defining the
    behavior of abstract classes and interfaces. We define certain
    constraints, certain propositions that must be satisified by the
    class. We define _some_ of the things that the class must do. But
    unlike the inductive definition, we allow the class to have variant
    behavior. As long as our constraints are still met, the class can do
    whatever else it wants. This enables subclassing.

    Unlike an inductive definition, a regular definition allows us to
    enumerate both [True] and [False] cases. This opens the door for us
    to introduce inconsistencies. But in this case, we do not get "ex
    falso quodlibet." Instead, we get a logically inconsistent abstract
    specification which cannot be inhabited by any concrete class.

    The flexibility of a regular definition is both a blessing and a
    curse. As long as our constraints are met, a subclass can do
    whatever else it wants. This means a subclass could set all
    variables to null in every object presently in memory, as long as
    our specification does not specifically preclude it.

    Aside: To make another analogy, inductive definitions and regular
    definitions are like two different ways to interpret the law: the
    _inductive_ man says "If the law does not explicitly allow it, then
    it is illegal," while the _regular_ man says "If the law does not
    explicitly forbid it, then it is perfectly legal." It's the
    difference between a blacklist (regular definition) and a whitelist
    (inductive definition).

    ** Consequences

    What are the consequences for software modelling? Should our
    abstract specifications preclude all undesired behavior? No. There
    are infinitely many things that a class should _not_ do, so we
    cannot hope to enumerate them. Furthermore, when we define an
    abstract specification, we cannot possibly envision all variant
    implementations of that specification, so we cannot clearly define
    what is "undesired behavior." Consider for example, an abstract
    specification for a function that is expected to be side-effect
    free. One way to express this is to specify that the function
    terminates in the same state that it started in. But this precludes
    a subclass from, for example, logging the function call to an
    external log. Certainly it is not acceptable for an abstract
    specification to preclude this.

    So, abstract specifications cannot preclude all undesired behavior.
    This leads to an important question: can we prove properties of a
    class that is client to an abstract class and guarantee that those
    properties will hold for any implementation of the abstract class?
    And the answer is: in some cases we can, but in the general case
    we cannot. Consider for example an IteratorConcatenator class that
    takes two abstract Iterators and iterates over one, then the
    other. Can we prove that the IteratorConcatenator behaves as
    expected for any abstract Iterator? No, we cannot. Here is a counter
    example: if we pass in the same Iterator twice, the expected
    behavior fails. Even if we add in an extra precondition that says
    "the two Iterators are not the same object," then we can break
    the behavior by passing in two objects which are wrappers around
    the same internal Iterator object. The list of possible failure
    conditions is infinite. However, we can prove that the
    IteratorConcatenator behaves as expected for a specific set of
    concrete Iterators. In other words, we can prove that
    IteratorConcatenator behaves as expected for a single, fully-defined
    state.

    Therefore, while there are some properties we can verify over a
    range of states, in the general case we can only verify the behavior
    of a class in a particular, fully-defined state. This means in order
    to verify behavior, we have to select concrete classes for all
    abstractions, instantiate all the needed objects, configure all
    client-supplier dependencies (dependency injection), and then we can
    prove properties of the resulting state. Indeed this fact will shape
    much of our verification efforts.

    But how useful is the method if we can only verify against specific
    states? There are several advantages over traditional testing.

    - We can rigorously prove that an object in a particular state
      conforms to an entire abstract specification. This is something
      that is impossible to do in traditional testing.
    - We can reuse abstract specifications to verify multiple classes.
    - We can make stronger assertions about the behavior of our
      software. For example, we can verify that a function terminates in
      the same state that it was called in. We can verify that a
      particular program does not leak memory. These things are
      impossible to do in traditional testing.
    - Finally, sometimes we are not restricted to a fully fixed state.
      Sometimes we can prove properties over a range of states.


    These limitations apply also to the input to our program: sometimes
    we can prove a property for any input, but in the general case we
    can prove a property only for a specific input. Bear in mind that to
    prove a property for any input, we have to do case analysis on the
    input. Such case analysis is only possible if we can define the
    input inductively.

    In conclusion, some properties can be proven over a range of states,
    but in the general case, we can only prove a property for a specific
    state. In other words, we cannot prove that a class always conforms
    to an abstract specification, but we can prove that _there exists_ a
    state in which the class conforms to the abstract specification. *)

End ConceptualFoundations.


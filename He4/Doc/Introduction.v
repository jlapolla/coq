(** * Iterators

    Throughout this discussion we'll work with an [Iterator] interface
    and various concrete classes which implement [Iterator].

    ** Iterator Interface

    We'll start with a Java code example that consumes the [Iterator]
    interface:

[[
Iterator<int> it = getIteratorSomehow();
it.forth();

while (!it.after()) {

  doSomethingWithAnInt(it.item());
  it.forth();
}
]]

    N.B. This is not Java's standard [Iterator<E>] interface [[1]].

    An [Iterator] has three states:

    - _Start_: [Iterator] has not retrieved the first item.
    - _Intermediate_: [Iterator] has retrieved an item and is ready to
      retrieve the next item.
    - _Stop_: [Iterator] ran out of items.


    These three states are encoded by two boolean functions:

    - [off]: [false] if [Iterator] has a current item.
    - [after]: [true] if [Iterator] ran out of items.


    The states are encoded by [off] and [after] as follows:

    - _Start_: [off = true /\ after = false].
    - _Intermediate_: [off = false /\ after = false].
    - _Stop_: [off = true /\ after = true].


    N.B. [off = false /\ after = true] represents an invalid state.

    The [Iterator] moves to the next state or the next item when we call
    [forth]. If we consider the [Iterator] as a transition system [[2]]
    the set of state transition labelled by [forth] is:

    - (_Start_, _Intermediate_).
    - (_Start_, _Stop_).
    - (_Intermediate_, _Intermediate_).
    - (_Intermediate_, _Stop_).


    We call [item] to retrieve the [Iterator]'s current item.

    In summary, the [Iterator] interface contains the following
    functions:

    - [off]: [false] if [Iterator] has a current item.
    - [after]: [true] if [Iterator] ran out of items.
    - [forth]: move to next state or next item.
    - [item]: retrieve current item.

    ** NatRangeIterator Class

    A [NatRangeIterator] is an [Iterator] whose items are a range of
    [nat]'s. It is defined by two [nat]'s:

    - [first]: the first [nat] returned.
    - [count]: the number of [nat]'s returned before entering _Stop_
    state.

    ** NatMultiplierIterator Class

    A [NatMultiplierIterator] is an [Iterator] whose items are the items
    of another [Iterator] multiplied by a [nat]. It is defined by a
    [nat] [Iterator] and a [nat] multiplier:

    - [inner_iterator]: the source [nat] [Iterator].
    - [multiplier]: the [nat] which multiplies each item of the
      [inner_iterator].

    * Outcomes

    The outcomes of this discussion are:

    - An [Iterator] specification (in the form of a Coq function) which
      tests if an implementation specification (either a concrete class or
      a sub-interface) conforms to [Iterator].
    - A [NatRangeIterator] specification describing the behavior with
      respect to [first] and [count].
    - Proof that the [NatRangeIterator] specification conforms to the
      [Iterator] specifiation.
    - A [NatMultiplierIterator] specification describing the behavior
      with respect to [inner_iterator] and [multiplier].
    - Proof that the [NatMultiplierIterator] specification conforms to
      the [Iterator] specification.
    - A [Main] function which is a closed term that composes a
      [NatRangeIterator] with a [NatMultiplierIterator] to produce some
      output.
    - Proof that [Main] produces the expected output.

    * Naming Conventions

    This project uses function names from Eiffel's base library wherever
    possible. For example [off], [after], [forth], and [item] were
    inspired by Eiffel's [LINEAR] class [[3]].

    * References

    - [[1]]: https://docs.oracle.com/javase/8/docs/api/java/util/Iterator.html
    - [[2]]: https://en.wikipedia.org/wiki/Transition_system
    - [[3]]: https://www.eiffel.org/files/doc/static/trunk/libraries/base/linear_chart.html *)

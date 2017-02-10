(**

In order to prove that a particular function is deterministic in a
particular step relation, we must prove that that particular step
relation is deterministic, and from there prove that multi stepping to a
value is also deterministic. Of course, if we have any kind of
abstraction in our step relation, then calling functions on that
abstraction may be non-deterministic. E.g. if we are using an abstract
Iterator object, calling 'forth()' multi steps to one of two cases:
'after()' returns true, or 'after()' returns false.

Therefore determinisim is hard to maintain in the face of abstractions.
This means that we can only prove determinism for a closed system with
no abstractions. I.e. we can only prove facts about the entire system.

This doesn't just mess with a particular step relation. It also means
that it is absurd to assume determinism in a specification that is based
on an abstraction. So, basically, we cannot reasonably expect to prove a
specification based on an abstraction is correct, nor can we prove that
the object possesses certain properties for all concrete implementations
of the abstraction.

One problem is that the specification for the Iterator interface says
that an Iterator will uphold certain properties. However, it does NOT
say that those are the ONLY properties of the Iterator! (If it did, then
any variation in implementations would be illegal, and that would not be
useful at all.) Therefore, we don't have any kind of induction principle
on Iterator that we can invert to prove properties of a specification
based on Iterator.

One possibility is to have two specifications of Iterator: a
specification that subclasses use to show that they are an iterator, and
a specification that clients use when they depend on an Iterator. The
subclass specification would be non-inductive, so it would allow
variation in subclass behavior. The client specification would be
inductive / constructive, so it would fully specify what an Iterator
does, and restrict any behavior outside of that. Of course, this is not
a valid assumption. Also, in order to have a constructive definition of
Iterator, we would have to construct a concrete Iterator. And if we
construct a concrete Iterator, we no longer have an abstraction, and we
may as well test with individual subclasses.

A key principle here is that if we want to prove something, we need an
induction principle to make proofs worthwhile. Without an induction
principle, we are reduced to testing individual cases, and if we are
testing individual cases, we may as well do that in unit testing. Is
there an induction principle that defines Iterator? One that says "If my
class works with the abstract Iterator, then it works with anything that
conforms to Iterator"? No, there is not. The only way this could happen
is if we constructively defined Iterator as a concrete class, in which
case Iterator is no longer an abstraction (as described in the previous
paragraph).

Consider further that the inputs to our program are completely
arbitrary. They are abstract, like Iterator. If we make them concrete,
then we are only testing individual cases. So, even if we define the
entire object hierarchy concretely, even if we define the entire program
constructively, we still have abstraction in the input to the software.
And therefore we need also a constructive definition of that input. We
can provide such a constructive definition by guaranteeing behavior only
for a restricted set of inputs, but this does not help us prove the
robustness of our software.

Furthermore, defining the entire system up-front before we can prove
anything about it is not a helpful, practical approach. It's like
waterfall development all over again.

Alright, so what CAN we use Coq for in object oriented development?
Well, we can define a specification for a class, and ensure that the
class implies that specification. That is to say, the class includes the
behavior in the specifiation. Notice that the inverse implication does
not hold: the specification does not include the specific behavior and
implementation of the class. If it did, then there is only one possible
class that can inherit the specification, and therefore the
specification is a concrete class, and that's not that useful to us.

So, let me rephrase: perhaps we could use Coq to EXPRESS abstract
specifications in a rich, unambiguous way. We still cannot PROVE that
the class implies the specification unless we use concrete classes for
each of the class' dependencies. I.e. we cannot prove that the class
behavior implies the abstract specification behavior for any abstract
dependencies of the class. We can only prove this for concrete
dependencies.

However, even the restriction of concrete dependencies may still be
useful, namely because we can detect when a combination of classes does
NOT meet an abstract specification. For instance, I cannot prove that my
class implies the specification when you pass in any implementation of
Iterator, but I can try a concrete implemenation of Iterator, and see if
my class implies the specification. And if my class does NOT imply the
specification then I know there is a problem.

In other words, I cannot prove that my class will ALWAYS imply the
specification, but I can at least show that THERE EXISTS A STATE IN
WHICH MY CLASS IMPLIES THE SPECIFICATION. If I cannot demonstrate such a
state, then that's a good sign that there is something wrong with my
class.

Is this an improvement over unit testing? Well, it certainly avoids the
ambiguities of unit testing. I mean, unit testing does not PROVE that a
class upholds its specification for a certain configuration, it only
demonstrates abstract facts about the configuration, which we HOPE imply
the specification we are trying to demonstrate. So, I'd say that proving
that a particular concrete configuration upholds a specification is
worthwhile.

Reading this all again, I see that it is possible to define functions of
the form [step_relation -> tm -> state -> Prop], but we must provide a
concrete [step_relation], [tm], and [state] to get a [Prop]. And when we
prove that [Prop], we prove it only for that particular combination of
[step_relation], [tm], and [state].

The utility if this approach is in recycling the [Prop]'s. We write our
specification once, then apply it to many steps, terms, and states.
There is also potential for reusable proof automation in each
specification. This also has more expressive power than unit testing.
For example, you cannot assert properties about the entire state of the
program in a unit test.

Let's try it, and see how it goes.

*)

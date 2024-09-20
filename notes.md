# Hi

I'm Nathan, I'm a PhD student at UT Austin, studying verification of concurrent
and distributed systems.  Spent a decade in industry as a systems hacker.

Not a type theorist by trade, but this is still a paper I love!

# Overview

Taking a page from the new historicists tonight:

* Context: We'll discuss the environs surrounding the problem
* Text: We'll discuss the paper (and learn a bit how to read a PL paper!)
* Subtext: We'll discuss what the paper doesn't (and what might come next)

# Types are great!

Just to check: who here has written at least one program in a statically-typed
programming language?  Great, I see a lot of hands, because I didn't have a
plan-B.

Indeed, type systems are so ubiquitous that it's easy to take their power for
granted.  We can do lots of awesome things with type systems:

* Type checking (`program -> Either[(), TypeError]`)
* Type reconstruction (inference) (`program -> Either[Map[value, type], TypeError]`)
    - The meater of the two problems: this invents type assignments!
    - Spoiler: this is the problem the paper solves
* `<mysterious redaction>` (I'll tell you at the end)
    - gotta keep people at home watching, for Youtube watchtime metrics!

Most type systems considered useful also have really strong theoretical
properties:

* Soundness (invalid programs are always rejected; no spurious errors)
* Efficiency (many algorithms are in P, often even ~O(n))
* Decidable (type theorists write proofs that they'll terminate on all possible programs!)

It's the branch of formal methods that practitioners most commonly interact
with.  Big win for types!

# Milner

Bon mot: "Well-typed programs don't go wrong"

This is _not_ saying that "well-typed programs don't have business logic bugs";
it is saying a well-typed program is always going to be able to keep executing
down to its final value without crashing or invoking undefined behaviour.

(By the way, by convention, we're going to call a function that takes
some arguments and returns a value a "program", so forget about the
practicalities of main(), argv, etc.)

Also, Milner was talking about _a specific type system_ and _a specific
programming language_ in his paper, as opposed to making a general claim about
_all type systems_. But, in meme form, the quotation remains as something to
aspire to.

For our purposes: let's say that a program "goes wrong" if it does something
like raises an exception (e.g. AttributeError, IndexError). Of course, in
Python exceptions aren't exceptional, so this doesn't really apply to "real"
software, but just for today let's use this rough-and-ready approximation.

# Lists

Here's a super-simple definition of a Lisp-style linked list: we say a list
is either the empty list, or an value prepended onto a linked list.

We can write some simple functions that operate on lists: the fact that the
typechecker verifies the correctness of these functions for a (conceptually)
infinite number of inputs is kind of miraculous if you stop and think about it?

Now, it doesn't take too long to run into some trouble.  I think we can agree
that `avg_of` is well-typed -- from the type system's perspective it isn't invalid,
but can we conceive of a well-typed input to this program that would go wrong?

Empty list!  In the body of the function, we'll divide zero by zero; that'll
cause an exception.  We went wrong!

But like any good zealot, I'll argue the problem here was not types but an
insufficent application of types.  We let types down, not the other way!

# Typechecking is an abstract interpretation

There's a way to think about types that I think is really interesting:
TODO

# Context: three non-solutions

To motivate the paper, I'm going to propose three non-solutions to fixing the
above program.  The intention here is that we're going to learn something from
each of the non-solutions that will hopefully guide us to the solution we want
(spoilers: it's going to be liquid types).

## Non-solution 1: A minor fix...

Even though the problem here manifested with a division by zero, the real
original sin was that we passed the empty list to `avg_of`.  Our goal is to
statically reject passing None, and we can!  Changing the signature to the
function specifically consuming a `Cons` will reject `avg_of(None)`.

The big observation here is that we took advantage of _inheritance_ to be more
specific about what sorts of values we should accept here.  That's worth
remembering.

Why is this a non-solution?  This happened to work for our particular case,
but it's not obvious how we can generalise this to other situations.  

For example, if we were writing a `def variance_of(l: List[int]) -> float`
function, we might want to enforce our non-empty list's elements are all
nonnegative.  Or, it isn't obvious how we could enforce in types that, say, a
`zip` function's list arguments must be the same length.  It doesn't take
long before we abut limitations of how expressive our current type system is.

## Non-solution 2: Fully Automated Luxury Dependent Types

A lesson we might take from non-solution 1 is to say, "well, ok, let's go find
a really sophisticated type system we can, and use that instead!"

I really like Richard Eisenberg's concise definition of dependent types from
his Signals and Threads interview:

> A dependent type is a type that can _depend_ on some input that you give
> to a function. -- https://signalsandthreads.com/future-of-programming/

Note that "input" here means, like, a program value or expression, not another
type.  So, even though in Java we might think `ArrayList<Integer>` "depends" on
the Integer type, technically we don't call that a dependent type.

Dependent types actually appear fairly often in unexpected places: OCaml's
module system is sort of a dependent type system, and if you've heard of
things like generalised algebraic data types or frameworks like Scalaz or
Shapeless, you've encountered simplifed versions of the concept.

The classic dependent type is the so-called indexed vector, which is a
sequence of elements of some type T, whose length _can be reasoned about
statically_:  Remember that the type argment `n` exists only at compile
time and you could imagine it's erased at compile-time.  It's not
runtime state!

```python
# Not real Python!

class Vector(Generic[T], n: int): pass

class Empty(Vector[T, 0]): pass
class Cons(Vector[T, n+1]):
    elem: T
    tail: Vector(T, n)

abc: Vector[str, 3] = Cons("a", Cons("b", Cons("c", Empty())))
dabc: Vector[str, 4] = Cons("d", abc)
```

In our glorious dependently-typed future, we can write all sorts of
interesting functions that operate on Vectors:

```python

# Fin is another classic dependent type: it's a natural number that
# the compiler knows is no bigger than n.  We don't have to return 
# an Optional value anymore!
def element_at(l: Vector[T,n+1], i: Fin[n]) -> T:
    ...

# To concatenate two Vectors, well, hm, the type system needs to know
# about addition...
def concat(v1: Vector[T, m], v2: Vector[T, n]) -> Vector[T, m+n]:
    ...

# ...to build up a Vector of all permutations, well, what, now it needs
# to know about factorial (which is recursively-defined...)
def all_permutations(v: Vector[T, n]) -> Vector[Vector[T,n], fact(n)]:
    ...

# ...if the type system can typecheck this function, it has proven
# the Collantz conjecture!!!
def three_x_plus_one_until_convergence(n: int) -> Vector[int, collantz(n)]:
    ...
```

Unfortunately we have a big problem here - if we want arbitrary program
expressions in our dependent types, then our type system is basically as
expressive as our programming language!  So, we will lose decidability and
automated typechecking (this is why a lot of dependent type systems have
associated proof assistants; the point of writing a Coq or Lean proof is to
help the typechecker!)

Remember that we want typechecking as well as type inference, so, maybe
there's a way to give us a restricted form of dependent types that, say,
is expressive enough for element_at and concat but not the other two, and
that's a tradeoff we're okay with.

## Non-solution #3: model-checking/SMT/Z3/???

Who here has heard of a model checker before?

Briefly: you can think of a model checker as a breadth-first exploration
through the possible executions of a program, in order to check some 
_property_ of the program, stated in some logical language. 

One possible property of interest might be "At every point in our
program, it is the case that at no point in the future can we jump to a
program state where we attempt a division by zero".  If the property is
not always true, a _counterexample_ would be "here's a sequence of
execution steps that lead to the division by zero".  (You might be able
to come up with that series of steps starting with `avg_of([])`)!  We
call such a counterexample a _refutation_ of the property.

Obviously exhaustively executing the program with all possible values is
not going to be terribly useful, so we typically abstract away concrete
program states and explore programs _symbolically_. (That feels a bit
like abstract interpretation from a few minutes ago!)  The workhorse for
doing this sort of abstraction are tools called SMT solvers.

I could spend the full hour talking about SMT solvers, they are some of
my favourite sorts of computer programs.  Instead, let me give you just
enough intuition for our purposes.

Suppose I have program with two ints, `x` and `y`, in scope:

```
uint8_t x, y, z;
...
z = y-x;
assert(z == 0);
```

I haven't told you the values of x and y.  Does this assert ever fire?
It's _always_ going to be zero, right?  We as humans used a bit of
logics and knowledge about how the theory of linear arithmetic works in
order to reach that conclusion, without, hypothetically,
guess-and-checking some values for x and y or anything.

The way we do this in an SMT solver is to try to "well, actually" it: we
begin with some symbolic integers (remember, these will never get
instantiated with concrete values) and say, "hey, solver, I bet you
can't find values for x and y such that z is not zero by the end."  In
other words, we're asking it to find a refutation of the postcondition.


```
uint8_t x, y;
...
z = x+y;
assert(x <= z and y <= z);
```

Will this assert ever fire?  Can you come up with an example?  What if
I turned this into an unbounded BigInteger?

```
BigInt x, y;
...
z = x+y;
assert(x <= z and y <= z);
```

What's more, it's a fact of model checkers that, just like our non-fancy
type systems, they're sound, push-button in their automation, and can
scale up to checking real-world software (e.g. kernel device drivers,
distributed systems).

There's a great property of SMT solvers: the theories they expose are 
_decidable_, just like a good type system is - in other words, the
solver will always be able to give a model for a satisfying query, or
report that an inherently-contradictory one is satisfiable.

Now, here's a downside: suppose I had a precondition and an operation,
and instead of checking the postcondition I wanted to _invent_ one.

```
BigInt x, y
x = 0
y = x + 3
assert(/* TODO: a sensible postcondition */);
```

We could put all sorts of expressions in there: `y == 3`, `y >= 0`, `x
== 0`, `42 == 42`.  Broadly, we have an SMT analogy to type checking,
but not a really good one for reconstruction.  That's a thing we'll have
to think hard about.

Already you might be able to see that this lets us express things that
depend on program expressions, just like what we wanted dependent types
to do for us.  Feels promising...?

# Text: the paper proper 

One of the things I love about being a systems person is that it's
generally fairly easy as a practitioner to pick up, say, the MapReduce
paper or the Xen hypervisor paper or whatever and get the high order
bits out of the paper.

PL is a lot more theoretic, so it's a lot harder to grok!  Right off the
bat it kind of feels like we're in trouble.  The _abstract_ name-drops
HM, predicate abstraction, dependent types, safety properties,
refinement=

To be clear, this isn't a criticism of the paper - it's written for an
academic PL audience and people in those communities would know what
these things are, but it just means we have to do a bit of the legwork
to work up to this ourselves.

So, our goal for this section is to actually dig into the paper, and see
how the best parts of our three non-solutions actually feed into their
work.  Our first goal is to understand enough to grok the abstract!

## Refinement types are dependent types

Let me introduce a particular kind of dependent type to you: a
_refinement type_ is the pairing of an ordinary, polymorphic type
(called the _base type_) with a logical predicate that _refines_ it. {v:
int | 0 <= v ∧ v < n} refines the base type of the integers to be bound
between 0 and some other value n. Since n is a program-level term, a
refinement type is also a dependent type.  In fact, it's `Fin n` from a
few minutes ago!

Refinement predicates are boolean predicates over program values of
integer, boolean, and array types.  The paper calls these "logical
qualifiers". As it happens, those are theories we'd find in a decidable
SMT solver!

Remember before that our big problem with dependent types: In the limit,
we placed no restrictions on what sorts of expressions a type could
depend on.  But, because our logical language in the refinement part is
decidable, _typechecking is also automatically decidable too_.   And,
as we'll see soon, we can use an interesting approach called _predicate
abstraction_ to come up with a way for decidable _type reconstruction_
too!

In the words of Rondon et al, `type checking [over a constraint domain]
is shown to be decidable modulo the decidability of the domain`.

It's funny to me looking back that the authors don't make a huge deal
about using SMT solvers in their type system in this paper.  With the
benefit of hindsight, it's a really key advancement!

## Divide and Conquer

In terms of a solution strategy, there's something really nice about
having a refinement type be this tuple of a base type and a predicate.
We can use a traditional type system to check and reconstruct the
base type, (In the paper that's "step 1"), and use SMT-based techniques
to check and reconstruct the constraint that the refinement represents
("steps 2 and 3").

## Base types: H-M

Who here has heard of the Hindley-Milner type reconstruction algorithm?
OK, trick question: who here has used it?  Most of your hands should
be up.  H-M is actually a super-common type reconstruction algorithm;
ML languages, F#, Haskell, and Rust use it as a basis for their type
reconstruction, among many others.  Basically, odds are that if you
program in a language with a static type system rich enough to support
generics, where you don't have to manually annotate types, AND IT IS NOT
SCALA, it's likely got H-M in its bones.

In the paper, the only valid base types are int, bool, and `list[int]`.
Remember, this is a research prototype and not a full-fledged production
type system, so it's okay if there are some gaping holes in what sorts
of programs they typecheck, so long as we don't lose soundness.  After
all, you can flesh out the type system in the inevitable followup works!

H-M is really beautiful because it's so natural.  Here's a program,
imagine this is in Rust or something:

```
def f(a, b):
    if b:
        return a[0]
    return a[1] + 1
```
What's the type signature of this function? `list[int] -> bool -> int`.
How did you figure it out?  Well, you looked at the use of the arguments
to the function, and figured out how their use _constrains_ their types.
For example, `b` is used as a conditional, `a` is indexed so it has to
be a `list[?]`, and that `?` is the lhs of an arithmetic expression, so
`a` has to be a `list[int]`.   

What about this?
```
def f(a, b):
    if b:
        return a[0]
    return a[1]
```
This function is _underconstrained_: we can't resolve what the type of
the array is.  But that's ok, that means this is a _polymorphic_
function!  `list[T] -> bool -> T`!

What about this?
```
def f(a, b):
    if b:
        return a[0]
    return a[1] + b
```
Hopefully you can see that this produces a type error: it's a
contradiction that b can be both a bool and a number.

Congratulations, you understand H-M, you're now officially type
theorists.


# Hi

I'm Nathan, I'm a PhD student at UT Austin, studying formal methods for
concurrent and distributed systems.

Not a type theorist by trade, but this is still a paper I love!

# Overview

Taking a page from the new historicists tonight:

* Context: We'll discuss the environs surrounding the problem space
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
* `<mysterious redaction>` (I'll tell you at the end)
    - gotta keep people at home watching, for Youtube watchtime metrics!

Most type systems considered useful also have really strong theoretical
properties:

* Soundness (invalid programs are always rejected)
* Efficiency (many type-theoretic algorithms are in P, often even O(n))
* Decidable (type theorists write proofs that they'll terminate on all possible program inputs!)

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

For our purposes: let's say that a program "goes wrong" if it does
something like raises an exception (e.g. AttributeError, IndexError).
Of course, in Python exceptions aren't exceptional, so this doesn't really
apply to "real" software, but just for today let's use this rough-and-ready
approximation.

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

The classic dependent type is the so-called indexed vector, which is a sequence
of elements of some type T, whose length _can be reasoned about statically_:

```python
# Not real Python!

class Vector(Generic[T], n: int): pass

class Empty(Vector[T, 0]): pass
class Cons(Vector[T, n+1]):
    elem: T
    tail: Vector(T, n)

```

In our glorious dependently-typed future, we can write all sorts of interesting
functions that operate on Vectors:

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

## Non-solution #3: model-checking

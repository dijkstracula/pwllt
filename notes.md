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

By the way, in this talk, generally, I want to give you some intuition
about PL theory and notation, but I'm going to similarly be a bit fast
and loose with notation so we don't get too bogged down.  Don't @ me.

# Lists

Here's a super-simple definition of a Lisp-style linked list: we say a list
is either the empty list, or an value prepended onto a linked list.

```python
@dataclass
class Nil[T]: pass

@dataclass
class Cons[T]:
    head: T
    tail: List[T]

type List[T] = Nil[T] | Cons[T]
```

We can write some simple functions that operate on lists: the fact that the
typechecker verifies the correctness of these functions for a (conceptually)
infinite number of inputs is kind of miraculous if you stop and think about it?

```python
def sum_of(l: List[int]) -> int:
    match l:
        case Nil(): return 0
        case Cons(h, t): return h + sum_of(t)

def length_of(l: List[T]) -> int:
    match l:
        case Nil(): return 1
        case Cons(_, t): return 1 + length_of(t)

def element_at(l: List[T], n: int) -> Optional[T]:
    match l:
        case Nil(): return None
        case Cons(h, t):
            match n:
                case 0: return h
                case n: return element_at(t, n-1)

assert(sum_of(l1) == 6)
assert(length_of(l1) == 3)
assert(element_at(l2, 1) == "W")
```

Here's another function.

```python
def avg_of(l: List[int]) -> float:
    return sum_of(l) / length_of(l)

assert(avg_of(l1) == 2.0)
```

Now, it doesn't take too long to run into some trouble.  I think we can agree
that `avg_of` is well-typed -- from the type system's perspective it isn't
invalid, but can we conceive of a well-typed input to this program that would
go wrong?

Empty list!  In the body of the function, we'll divide zero by zero; that'll
cause an exception.  We went wrong!

But like any good zealot, I'll argue the problem here was not types but an
insufficent application of types.  We let types down, not the other way!

# Context: three non-solutions

To motivate the paper, I'm going to propose three non-solutions to fixing the
above program.  The intention here is that we're going to propose something
that isn't the right solution, but learn something from each them, that will
hopefully guide us to the solution we want (spoilers: it's going to be liquid
types).

## Non-solution 1: A minor fix...

Even though the problem here manifested with a division by zero, the real
original sin was that we passed the empty list to `avg_of`.  Our goal is to
statically reject passing Empty, and we can!  Changing the signature to
the function specifically consuming a `Cons` will reject `avg_of(None)`.

The big observation here is that we took advantage of _inheritance_
(which I'm going to call _subtyping_) to be more specific about what
sorts of values we should accept here.  Rather than saying "it's
sufficient for either an Empty or a Cons" we're now sort of saying "it's
necessary that it's a Cons".

```python
list_of_ints = Cons(1, Cons(2, Cons(3, None)))
list_of_nothing = None
list_of_strings = Cons("a", None)

def avg_of(l: List[int]) -> float:
    return sum_of(l) / length_of(l)

avg_of(list_of_ints)

avg_of(list_of_nothing)  # type error!
avg_of(list_of_strings)  # type error!
```

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

```java
/* Not real Java, of course! */

interface Vector<T, Integer n> { };

class Empty<T> extends Vector<T, 0> { };

class Cons<T, n+1> extends Vector<T, n+1> {
    public final T            head;
    public final Vector<T, n> tail;
}

Vector<Integer, 2> four_three =
    new Cons<>(4,
        new Cons<>(3, 
            new Empty<>()))

/* */

public void f(Vector<T, 3> triplet) {
    ...
}

f(four_three) /* type error! */
```

In our glorious dependently-typed future, we can write all sorts of
interesting functions that operate on Vectors:

```java
/* Again, of course, not real Java! */ 

/* Fin<n> is another classic depedent type: it's a natural number up
 * to but not exceeding `n`. */
public static T element_at(Vector<T, n+1> v, i: Fin<n>);

/* To concatenate two Vectors, well, hm, the type system needs to know
 * how to add two integers... Already, this is clearly more powerful than
 * for example Rust's const generics... */
public static Vector<T, m+n> concat(v1: Vector<T, m>, v2: Vector<T, n>);

/* To build up a Vector of all permutations, we need to know how to reason 
 * about recursive functions...
 */
public static Vector<Vector<T, n>, fact(n)> perms(v: Vector<T, n>);

/* If this typechecks, we have a proof of the Collantz conjecture! */
public static Vector<Integer, collantz(n)> iterate_3_x_plus_one(n: int);
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

One possible property of interest might be "At every point in our program, it
is the case that at no point in the future can we jump to a program state where
we attempt a division by zero".  If the property is not always true, a
_counterexample_ would be "here's a sequence of execution steps that lead to
the division by zero".  (You might be able to come up with that series of steps
starting with `avg_of([])`)!  We call such a counterexample a _refutation_ of
the property.

Notice something kind of interesting about "BFS through the program" idea: you
can imagine that every time we hit a branch we explore both possibilities: a
type system doesn't reall do this, right, like if you have an `x if b else y`
ternary form, the true branch and the false branch must always be the same
type.  Because a model checker explores both branches explicitly, it's not
discarding information it learns along one branch but not the other.

It's a fact of model checkers that, just like our non-fancy type systems,
they're sound, push-button in their automation, and can scale up to checking
real-world software (e.g. kernel device drivers, distributed systems).

## Sat and SMT

Obviously exhaustively executing the program with all possible values is
not going to be terribly useful, so we typically abstract away concrete
program states and explore programs _symbolically_.  The workhorse for
doing this sort of abstraction are tools called SAT and SMT solvers.

I could spend the full hour talking about SMT solvers, they are some of
my favourite sorts of computer programs.  Instead, let me give you just
enough intuition for our purposes.

## Satisfiability

A SAT solver solves the boolean Satisfiability problem.  This asks, "given a
collection of boolean variables and a formula in propositional logic, does
there exist an assignment of those variables such that the formula is true?"

```python
>>> from z3 import *
>>> b1, b2, b3 = Bools("b1 b2 b3")
>>> fmla = And(Or(b1, b2), Not(b3))
>>> solve(fmla)
[b3 = False, b1 = True, b2 = False]
>>> 
```

If you know a bit about complexity theory you might remember that SAT is the
canonical NP-Complete problem.  NP-Complete problems have a reputation for
being "effectively intractable", but good SAT solvers have heuristics and
algorithims that in a lot of practical cases cut down the search space.

Critically, about when this paper was written, SAT solvers really started
getting good at solving larger and larger problems.  If you wanted to integrate
SAT solvers into a new domain, 2008 was a great time to do it!

(Show SAT 2009 benchmarks graph from DP.)

## Program analysis with SMT

SMT means "Satisfiability, modulo theories".  You can think of SMT as SAT but
with a layer on top for richer datatypes than just booleans.  So, if you wanted
to write a query involving integers, you might incorporate the Theory of Linear
Arithmetic.  For queries involving arrays, there's a Theory of Arrays.  And so
on.

So here I have a repl open here, we're going to write some queries to
the Z3 SMT solver.  To be clear, Z3 is _not_ a model checker, remember, and not
every model checker uses SMT, but but you could build a model checker (or, a
liquid type system!) using Z3 as a library.

Suppose I have program with two ints, `x` and `y`, in scope:

```c
uint8_t x, y, z;
...
z = y-x;
assert(z == 0);
```

I haven't told you the values of x and y.  Does this assert ever fire? It's
_always_ going to be zero, right?  We as humans used a bit of logics and
knowledge about how the theory of linear arithmetic works in order to reach
that conclusion, without, hypothetically, guess-and-checking some values for x
and y or anything.

The way we do this in SMT is to ask the solver for a _refutation_ of the
postcondition: can it find a model where z is _not_ equal to zero?  If not,
then the postcondition z == 0 is valid; that is, true on every input!  If it's
not true on every input, Z3 will give us a counterexample.

Here's another classic C bug.  Will this assert ever fire?  

```c
int lo, hi = 0, len(a)-1
while (lo <= hi) {
    int mid = (lo + hi) / 2
    assert(lo <= mid && mid <= hi);
}
```

```python
s = z3.Solver()
lo, mid, hi = z3.BitVecs("lo, mid, hi", 8)
s.add(0 <= lo, 0 <= hi)

s.add(lo <= hi)         # This must be trus for us to enter the loop
mid = (lo + hi) / 2
s.add(z3.Not(z3.And(lo <= mid, mid <= hi)))

s.check()
print(s.model()) # If there's a model, we found a bug!
```

Do you remember your Programming Pearls?  How do we fix it?

```c
int lo, hi = 0, len(a)-1
while (lo <= hi) {
    mid = lo + ((hi - lo) / 2)
    assert(lo <= mid && mid <= hi);
}
```

There's a great property of SMT solvers: the theories they expose are
_decidable_, just like a good type system is - in other words, the solver will
always be able to give a model for a satisfying query, or report that an
inherently-contradictory one is satisfiable.

## Logical implication

One more thing I want to show: we've seen the ordinary logical operators
that we're used to from traditional programming: OR, AND, and OR.  SAT and SMT
solvers also have implications:

Recall how logical implication works: A => B states that it is _sufficient_
that A holds to know that B also holds.  Stated another way, B holds _whenever_
A holds.

TODO: I'd like to work this towards a good example of subsumption/subtyping.

## Downsides

Now, here's a downside: suppose I had a precondition and an operation, and
instead of checking the postcondition I wanted to have one invented
automatically for me.

```c
BigInt x, y
x = 0
y = x + 3
assert(/* TODO: a sensible postcondition */);
```

We could put all sorts of expressions in there: `y == 3`, `y >= 0`, `x == 0`,
`42 == 42`.  Broadly, we have an SMT analogy to type checking, but not a really
good one for reconstruction.  We would need to do something clever in order to
build a tool that could come up with a good postcondition for us like this.

Already you might be able to see that this lets us express things that depend
on program expressions, just like what we wanted dependent types to do for us.
Feels promising...?

# Text: the paper proper 

One of the things I love about being a systems person is that it's generally
fairly easy as a practitioner to pick up, say, the MapReduce paper or the Xen
hypervisor paper or whatever and get the high order bits out of the paper.

PL is a lot more theoretic, so it's a lot harder to grok!  Right off the bat it
kind of feels like we're in trouble.  The _abstract_ name-drops HM, predicate
abstraction, dependent types, safety properties, refinement, ...

To be clear, this isn't a criticism of the paper - it's written for an academic
PL audience and people in those communities would know what these things are,
but it just means we have to do a bit of the legwork to work up to this
ourselves.

So, our goal for this section is to actually dig into the paper, and see how
the best parts of our three non-solutions actually feed into their work.

## Refinement types are dependent types

Let me introduce a particular kind of dependent type to you: a _refinement
type_ is the pairing of an ordinary, polymorphic type (called the _base type_)
with a logical predicate that _refines_ it. {v: int | 0 <= v ∧ v < n} refines
the base type of the integers to be bound between 0 and some other value n.
Since n is a program-level term, a refinement type is also a dependent type.
In fact, it's `Fin n` from a few minutes ago!

Refinement predicates are boolean predicates over program values of integer,
boolean, and array types.  The paper calls these "logical qualifiers". As it
happens, those are theories we'd find in a decidable SMT solver!

Remember before that our big problem with dependent types: In the limit, we
placed no restrictions on what sorts of expressions a type could depend on.
But, because our logical language in the refinement part is decidable,
_typechecking is also automatically decidable too_.   And, as we'll see soon,
we can use an interesting approach called _predicate abstraction_ to come up
with a way for decidable _type reconstruction_ too!

In the words of Rondon et al, `type checking [over a constraint domain] is
shown to be decidable, modulo the decidability of the domain`.

It's funny to me looking back that the authors don't make a huge deal about
using SMT solvers in their type system in this paper.  With the benefit of
hindsight, it's a really key advancement!

## Divide and Conquer

In terms of a solution strategy, there's something really nice about having a
refinement type be this tuple of a base type and a predicate. We can use a
traditional type system to check and reconstruct the base type, (In the paper
that's "step 1"), and use SMT-based techniques to check and reconstruct the
constraint that the refinement represents ("steps 2 and 3").

# Solvent

Of course the downside of coming from a systems background is that you pick up,
say again, the MapReduce or Xen paper, but it's extremely nontrivial to go off
and implement the described system in order to play around with the ideas
yourself.  It was kind of a revelation to start transitioning into a PL person
when I started my PhD and to realise "hey, with a bit of elbow grease, you can
actually teach yourself how these things work by rebuilding them!"

So, what I've got here is a tiny liquid types system that a friend of mine and
I wrote a few years ago.  It handles typechecking most of the simple examples
in the paper, which was enough for our purposes (please do not rely on it for
your production system's type safety.)   It also has _many_ bugs that I hit
while preparing this talk, so hopefully I will steer us away from those.

We built it exactly for this reason: we both learn best by doing, so we did the
thing that would teach ourselves the technique well enough to explain it to
others!

Sammy totally went ham on this implementation, and he's the reason why it's so
good.  Thanks, Sammy, if you're tuning in!

## Typechecking, abstractly

So the funny thing about PL papers, coming from the systems world, is that in
theory everything you need to know in the paper is in two figures.
Technically, in this paper, it's four, but one figure is pseudocode, so.

## Figure 2: Syntax

There's a joke that all programming languages are is defining syntax and
defining semantics.  I'm showing Figure 2 not because we have to walk through
every little detail of the syntax, but to point out that syntax really can
circumscribe the expressiveness of your technique.

The first part describes what kind of expressions we want to typecheck; they're
more or less exactly the ones you expect; the actual paper typechecks ML rather
than, of course, Python, so that means this is where we might learn that the
typechecker only handles recursion and no loops, and, doesn't consider mutable
variables.

In particular, I want to draw your attention to "base types": recalling the
definition of refinement types, figure 2 tells us that their type system only
allows for base types to be `int` or `bool`.  Remember, this is a research
prototype and not a full-fledged production type system, so it's okay if there
are some gaping holes in what sorts of programs they typecheck, so long as we
don't lose soundness.  After all, you can flesh out the type system in the
inevitable followup works!

## Figure 3: Semantics???

In particular, the precise rules of how liquid types work are encoded in
the series of greek symbols in Figure 3.  But if you've never looked at
a typing rule, that figure is going to look like...a lot. Heck, even if
you have looked at a typing rule, that looks like a lot!

OK, so let me teach you a bit about how to decode the symbols in a PL
paper.  How might we typecheck the `1 + 2` fragment?

Somebody said something to the effect of "well, addition requires both
operands to be ints, and the resulting expression types to an int". 
Here's the typing rule for that:

```
⊢ p1 : int    ⊢ p2 : int
------------------------
     ⊢ p1 + p2 : int
```

`⊢ p : T` is called a "typing judgement", and can be read out as "the
program (expression) has type T.  This notion style goes back to Genzler
and says "if we can prove all the things above the line, we can conclude
the thing below the line" - it's a fancier way of writing a logical
implication.

What's cool about this is these typing rules can compose into
"derivation trees" (show figure 1.5 from P=P).  Some judgement above the
line might require a proof, so they stack on top of each other like a
tree.

Some typing rules only make sense in certain contexts.  For instance,
suppose we wanted to typecheck an anonymous function:

```
    (Γ(x) = A) ⊢ t : B
----------------------------
Γ ⊢ (lambda x: t) : A -> B
```
Notice we now have symbols to the left of the turnstyle.  There's this
new Gamma thing; think of this as the internal state of the typechecker.
I like to think of Gamma as a dictionary from program variable to type,
so this says "we can typecheck `lambda x: t` as a function from A to B
so long as the typechecker can "pull out" some type A when it looks up
the variable x.

One last thing: here's a typing rule that likely doesn't exist anywhere

```
⊢ p1 : int    ⊢ p2 : bool
------------------------
     ⊢ p1 + p2 : int
```

The absence of a rule like this means the type system doesn't permit the
"addition" of an int and a bool, which is generally a good thing unless
you're a Perl programmer.  The fact we don't make such nonsense programs
well-typed is getting closer to what Milner was expressing with his
"well-typed programs don't go wrong" maxim!

## Typechecking, concretely

OK, enough theory for now.  Let's typecheck some programs.  Our goal is to
reconstruct a liquid type for the max function.  This is a great first example
because it's got simple control flow, but no iterative computation like loops
or recursion.  (That'll come later.)

## Base types: H-M

Who here has used the Hindley-Milner type reconstruction algorithm?
Trick question!  Most of your hands should be up.  H-M is actually a
super-common type reconstruction algorithm; ML languages, F#, Haskell,
and Rust use it as a basis for their type reconstruction, among many
others.  Basically, odds are that if you program in a language with a
static type system rich enough to support generics, where you don't have
to manually annotate types, AND IT IS NOT SCALA, it's likely got H-M in
its bones.

H-M is really beautiful because it's so natural.  Here's a program whose 
type we want to infer.

```python
def max(x, y):
    if x > y:
        return x
    else:
        return y
```
Imagine you were the Rust type inference algorithm.  What's the type signature
of this function? `int -> int -> int`. How did you figure it out?  Well, you
looked at the use of the arguments to the function, and figured out how their
use _constrains_ their types.

```python
def max(x: 'X, y: 'Y) -> 'GUESS # Types with ticks are "constraint"s
    cond: 'IF = x > y
    if cond:
        ret: 'GUESS = x
        return ret
    else:
        ret: 'GUESS = y
        return ret
```
We are going to solve for the return type, which I gave a constraint
variable called `GUESS.  Because our program has `x > y`, we know that
x and y need to be ints (or, technically, ints or "subtypes" of ints, if
we had inheritance).  Conversely, Guess needs to be the types of x and
y, or, a "supertype" thereof, if we had inheritance.  In a world without
subtyping, everything's an int, so 'GUESS is constrained to be an int.

What about this?
```python
def f(a, b):
    if b > a:
        return b
    return False
```
Hopefully you can see that this produces a type error: it's a
contradiction that b can be both a bool and a number.  The reason why is
that H-M is going to try to constrain `GUESS to be an int and a bool,
which it can't, because they're not equal, nor would they ever have a
subtyping relationship.

Hey, this idea of building up constraints and then solving for them...does
anyone recognise what meta-algorithm this is?  (hint: are there are prolog
sickos in the audience?)  Yeah, it's unification!  And if you are old enough to
have taken logic programming in school but not so old that you've forgotten the
contents of your logic programming in school, you might remember that
unification is guaranteed to produce the _most general unifier_ for its set of
constraints.  This means that we'll get the most general type assigments; we'll
never overfit to the data.

Congratulations, you understand H-M, you're now officially type
theorists.

## From base types to logical qualifiers

For the rest of the talk, we're going to treat reconstructing base types as a
solved problem, because it really is.  Typechecking and reconstructing the
logical qualifiers is the novel part.

```python
def max(a: {int | K1}, b: {int | K2}) -> {int | K3}: 
    if b > a:
        return b
    return a

print(max(42,99))
```

```python
def max(a: int, b: int) -> {int | True}: 
    ...
print(max(42,99))
```
Well, technically correct, but a bit underspecified; this doesn't tell
us anything more than just running H-M.  So, we'd hope we'd do better.

OK, maybe something like

```python
def max(a: int, b: int) -> {int | a <= V and b <= V}: 
    ...
```
That seems pretty reasonable: "the return value is at least as big as
both inputs."  Or, what about:

```python

def max(a: int, b: int) -> {int | a == V or b == V}: 
    ...
```
"The return value is one of the two inputs".  Is this one better or
worse?  Feels worse, but how can we _quantify_ which might be better?


```python
def max(a: int, b: int) -> {int | V == 99}: 
    ...
print(max(42,99))
```
Clearly this is the opposite problem of just saying "True" - in this world, we
observed "well, we call max() only once, and the return value was 99, so the
dependent type should encode that fact.  Certainly this sort of global view is
simultaneously's way too overspecified and too myopoic!

## Two kinds of refinement constraints

Just like with H-M, our goal is going to be to come up with some
constraints to solve.  But instead of saying "are these two base types
equal (or inherit from some common superclass)", we're going to ask "are
these two logical qualifiers compatable", for some definition of
"logically compatable".

Remember that we have the wildcard that we can substitute program values
in.  Suppose we're typing the body

```python
def max(x: {int | K1}, x: {int | K2}) -> {int | K3}: 
    if x > y: # <- suppose we are typechecking here...
        return x
    else:
        return y
```

We're going to want to come up with logical qualifiers for each of these
variables.  We're going to do this in two ways:

* Scope constraints: how could the logical qualifier depend on existing
  values in scope?
* Flow constraints: how could the logical qualifier depend on a
  particular control flow path through the program?

### Scope constraints

Scope constraints are probably the easiest to understand so let's talk
about those first.  

K1 and K2 have no scope constraints because they're "at the top of the
program".  So, their typing contexts are empty.  By contrast, what's in
scope when we compute K3?  Well, x and y are, so the refinement type can
depend on values of x and y!

```
Γ ⊢ K1
Γ ⊢ K2
Γ(x) = {int | K1} ; Γ(y) = {int | K2} Γ ⊢ K3
```

### Flow constraints

The paper doesn't explicitly call these "flow constraints" but
subsequent work does, and I like the terminology.

Suppose in some actual execution, x > y, so we return x.
```python
def max(x: {int | K1}, x: {int | K2}) -> {int | K3}: 
    if x > y: 
        return x # <- What is K3 in this case?
    else:
        return y
```

In this case, our typing context doesn't just involve values in scope
but facts related to control flow through the program.  So, it'll look
like this:

```
Γ ⊢ K1
Γ ⊢ K2
Γ(x) = {int | K1} ; Γ(y) = {int | K2} ; (x > y) Γ ⊢ K3
```

If you're a type theorist you might start itching, because we have
program values in our typing context.  That, generally, doesn't make
sense.  But, remember, we're implementing a _dependent type system_
here, so terms and types can in fact intermingle in the context!

OK, so what's the type for the return value in this path?  A reasonable
thing to say is `{int | x == v} = K3`.  That is, the type of the return
value is exactly x.  But, some of you probably can see that this will
contradict the other flow when take the false branch.  So, we don't want
to say that K3 is _equal_, but rather this branch's type is a _subtype_
of the final type: `{int | x == v} <: K3`!

By symmetry, we'll have:

```
Γ ⊢ K1
Γ ⊢ K2
Γ(x) = {int | K1} ; Γ(y) = {int | K2} ; (x > y)  Γ ⊢ {int | x == v } <: K3
Γ(x) = {int | K1} ; Γ(y) = {int | K2} ; ~(x > y) Γ ⊢ {int | y == v } <: K3
```

Because the final type is going to be one of these two types, we could choose to
say "well, why not take the logical-OR of them?"  That means our type signature
would end up being

```python
def max(a: int, b: int) -> {int | V == b or V == a}: 
    ...
```

Remember that we concluded that this typing was "fine", but not the S-tier
solution.  We want a better way to come up with the right subtype.

### What's in a subtype?

How should we generalize our inferred type instead?

Remember an informal definition of subtyping, courtesy of Liskov: "if A is a
subtype of B, then it's _sufficent_ to have an A in a situation where we need a
B".  Hey, that's equivalent to our definition for logical implication!  

```
 (x > y), {int | x == v } <: K3
~(x > y), {int | y == v } <: K3

 (x > y) /\ x == v ==> (our final refinement type)
~(x > y) /\ x == v ==> (our final refinement type)
```

So, if we had manually annotated the return type of this function, typechecking
the logical qualifier would simply boil down to asking Z3 "does this logical
implication hold?"!!! 

This is encoded in the `[Dec <: Base]` rule (TODO: explain denotational
semantics or skip??)

## Predefined qualifiers

So this whole time I've been saying "coming up with the right refinement
qualifier is hard" 

- now it's time to tell you how the authors did it. The
thrilling conclusion: they did it in advance!

A liquid type system contains a predefined set of qualifiers from the SMT
solver's theory that's used as a sort of "basis set" that will comprise a
reconstructed liquid type:

```python
quals = [0 < V, 
         _ <= V, 
         V < _,
         len(_) <= V]
```
Here's the built-in qualifiers from the paper.  The underbar is the * operator
from the paper; the idea is that it can be replaced with any variable in scope
whose base type typechecks (e.g. can't place a boolean on the LHS of <=).

You're probably thinking "well, doesn't this really limit the expressivity of
the refinement types?", and, yes, indeed it does, but that's kind of the point!
The idea is that so long as you have a representitve, but still finite, set of
qualifiers, the type system has a finite amount of work to do during
typechecking.

Something not discussed in the paper is that these qualifiers can be overriden
by the application programmer.

For instance, the liquid type Vec implementation in the paper artefact comes
with an additional set of qualifiers, written by the implementer of the data
structure, specific to that program:

```c
(* a portion of ./postests/vec/len.hquals, simplified *)
qualif LVAR(v): len(v) [<, =, >] *
qualif LCONST(v): len(v) [<, =, >]  [0, 1]
qualif SETAPPEND(v): len(v) = (len(v) > * ? len(v) : * + 1)
qualif LSUM(v) : len(v) = [0, 1] + len( * ) + len( * )
qualif TOARR(v): len( * ) = Array.length v
```

In this way, both the type system implementer and the application programmer,
can _bias_ the inferred types.  This idea of a "customizable typechecker" feels
like a really interesting idea, I wonder why it was left as an implementation
detail?

## Concreteizing qualifiers without scope constraints

We need to expand our qualifiers by substituting all our scope constraints for
$\star$.  Any well-type program term in scope can replace a *.

Remember that `K1` and `K2` have no scope constrants, so we discard all
qualifiers except for `0 <= v`.  This means the _only_ possible subtype of K1
that we could synthesize would be of the form:

```python
{int | 0 <= V} <: {int | K1}
{int | 0 <= V} <: {int | K2}
```

## Concreteizing qualifiers with scope constraints

By contrast, `K3` has `x` and `y` as scope constraints, so we can substitute
both those in.  This is our initial guess 

```python
{int | V == x} <: {int | 0<=V ∧ x<=V ∧ y<=V ∧ V<x ∧ V<y} <: {int | K3}
{int | V == y} <: {int | 0<=V ∧ x<=V ∧ y<=V ∧ V<x ∧ V<y} <: {int | K3}
```

Here's the problem: our initial guess is going to be almost certainly logically-invalid. 
Indeed, if V == x, then certainly it isn't the case that V<x!

We just created the cross product of all our logical qualifiers with all the
scope constraints with all the flow constraints.  If we asked Z3 to check
whether this implication is valid, it won't have good news for us. 

The thing is, though, that there's some _subset_ of those formulas that _is_
valid.  We need a _weakening_ process by which we'll cull the ones that lead to
contradictions.  This process is called _predicate abstraction_.

Obviously we don't want to try all 2**n possibilities of subsets, but the good
news is that we can cull invalid formulae greedily.  We can test each formula
in a given flow individually.

```
 (V == x) => (0<=V ∧ x<=V ∧ y<=V ∧ V<x ∧ V<y})
 (V == y) => (0<=V ∧ x<=V ∧ y<=V ∧ V<x ∧ V<y})

 (V == x) => (     ∧ x<=V ∧ y<=V ∧     ∧ V<y})
 (V == y) => (     ∧ x<=V ∧ y<=V ∧ V<x ∧    })
```

So now we have an internally-consistent set of qualifiers for each of the two
possible control flow paths.  What's the final set of qualifiers for K3?  Well,
whatever it is has to be true for both flows; we simply take the intersection!

```
 (V == x) => (     ∧ x<=V ∧ y<=V ∧     ∧ V<y})
 (V == y) => (     ∧ x<=V ∧ y<=V ∧ V<x ∧    })
                     x<=V ∧ y<=V
```

So our final type is the one we agreed upon earlier was the best: 
`{int | x <= V and y <= V}`!

Just to drive the point home: here's how the return type of max might be
interpreted outside the function definition:

```python
a = ...
m = max(a, 10) # { int | a <= V ∧ 10 <= V } 
```
# The home stretch

So we've actually covered a heck of a lot today.  We kind of built up liquid
types from first principles, starting with "here's a function that shouldn't
typecheck!"

I want to talk about two more things before we all go to the bar, or whatever
happens after we wrap up here.  

## Extensions for recursion

The max() example was pretty straightforward in the sense that while control 
flow branched, we didn't loop or have any sort of recursion.

Here's a function that behaves equvialently to `sum(range(k))`:

```python
@solvent.infer
def my_sum(k):
    "Computes sum(range(k))."
    if k < 0:
        return 0
    else:
        s = my_sum(k-1)
        return s + k
```

Just as before, we'd compute the base type and assign constraint variables
for the argument and the body:


```python
@solvent.infer
def my_sum(k: {int | K1}):
    "Computes sum(range(k))."
    if k < 0:
        return 0 # K2
    else:
        s = my_sum(k-1)
        return s + k # K2
```

The base case is pretty simple to do: the subtype of K2 here is the refinement
type that forces its value to be 0.

```
            (k < 0)                              ⊢ {int | v == 0 }   <: {int | K2}

Γ(k) = K1, !(k < 0)                              ⊢ {int | v == k-1 } <: {int | K1}
Γ(k) = K1, !(k < 0), Γ(s) = typeof(my_sum(k-1))  ⊢ {int | v == s+k } <: {int | K2}
```

What I wrote here is a real abuse of notation - our typing context can't have
"a function call" in it as I've written it.  I wrote it this way to emphasize a fact:
if k appears in the return type for K2 at all, the type of `my_sum(k-1)` is going to have
all occurrences of k replaced with k-1.  Just like our example with max().

The way we write this is with _substitution_ notation, another classic PL paper-ism.

```
Γ(k) = K1, !(k < 0), Γ(s) = [k-1/k]K2  ⊢ {int | v == s+k } <: {int | K2}
```

The stuff in the square brackets means "any occurrences of k are to be replaced with
k-1.  The mnemonic I like is that k is getting "squashed" by the k-1.  Let's continue
with predicate abstraction as we did before: we learn from the base case example
that 

```
            (k < 0)                    ⊢ {int | v == 0 }   <: {int | 0 <= V ∧ k <= V} <: {int | K2}
Γ(k) = K1, !(k < 0), Γ(s) = [k-1/k]K2  ⊢ {int | v == s+k } <: {int | K2}
```

This means we have a subtype to plug into K2!

```
            (k < 0)                                         ⊢ {int | v == 0 }   <: {int | 0 <= V ∧ k <= V} <: {int | K2}
Γ(k) = K1, !(k < 0), Γ(s) = [k-1/k]{int | 0 <= V ∧ k <= V}  ⊢ {int | v == s+k } <: {int | K2}
```

```
            (k < 0)                                    ⊢ {int | v == 0 }   <: {int | 0 <= V ∧ k <= V} <: {int | K2}
Γ(k) = K1, !(k < 0), Γ(s) = {int | 0 <= V ∧ k-1 <= V}  ⊢ {int | v == s+k } <: {int | K2}
```

Finally, remember the point here: this says "if we look up the variable S in
our context, its refinement type tells us that s will be greater than zero and
greater than k-1. Let's just state that explicitly?

```
            (k < 0)                        ⊢ {int | v == 0 }   <: {int | 0 <= V ∧ k <= V} <: {int | K2}
Γ(k) = K1, !(k < 0), (0 <= s), (k-1 <= s)  ⊢ {int | v == s+k } <: {int | K2}
```

Notice what we've done here: by doing this substitution on the recursive call,
we've banished any occurrences of recursion in our typing judgements!  So, now
we can proceed as we did before, and discover that the final type of my_sum is

```
int -> {int | 0 <= V ∧ k <= V} 
```

## closed form

Certainly true enough.  Let me leave you with one more final thought: we know
there's a closed form for summation: `(n * (n+1))/2`.  Maybe if you asked ChatGPT
to write you a refinement type for my_sum it would hand you back that closed form,
but with our current set of qualifiers, the type system is biased against ever
finding it.

Something for you all to think about on the subway home: what might happen if we
were to add `(_ * (_ + 1)) / 2 == V` into our set of logical qualifiers...?

# Later work:

Generalizing followup work came soon after, focusing on imperative programs in
C and Haskell. More recently, follow-up work has been done in integrating
liquid types into a gradual typing environment and industrial languages like
TypeScript.

## Bonus: synquid

I told you at the beginning that types are great for three big kinds of problems.
Now it's time to show you what the third and final problem is:

TYPE DIRECTED PROGRAM SYNTHESIS: `refinement type -> program`.

This is a procedure where we start with a liquid type describing a type
signature and it gives us a program that satisfies that type!

TODO: what's the bare minimum of what I can say here?

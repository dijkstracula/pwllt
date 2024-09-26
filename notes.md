# Hi

I'm Nathan, I study the verification of low-level and distributed systems.  I'm not really a PL person by trade, and I'm certainly not a type theorist by trade, but this is still a paper I love!


# Overview

Taking a page from the new historicists tonight:

* Context: We'll discuss the environs surrounding the problem
* Text: We'll discuss the paper (and learn a bit how to read a PL paper!)
* Subtext: We'll discuss what the paper doesn't (and what might come next)


# Type theories are great!

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


# Type metatheories are great, too!

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

Here's a tiny bit of PL notation that will be important in the paper here:
this "less than" sort of symbol indicates that Nil and Cons are subtypes
of List.

# What's in a subtype?

Subtyping is a really important part of this paper, so I want to remind us
of some rough-and-ready intuitions for what it means that Cons is a subtype
of List:

* The classic Liskov substitution principle tells us that whenever you have
a List you can safely substitute in a Cons.
* Similarly, you can think of a type as a collection of possible values, and
subtyping tells us that Cons' values are a subset of List's.
* There's actually a deep connection between a type and a logical proposition.
Viewed in that light, everything that's "true" about a List is also true about
a Cons.

# Functions on Lists

OK, that's our data definition; here are some functions that operate on Lists.

The fact that the typechecker verifies the correctness of these functions for a 
(conceptually)infinite number of inputs is kind of miraculous if you stop and 
think about it?

One thing to point out here: the ith element is not always defined on a list:
we might return a None if the index is out of bounds.  

# Avg

Something great feature of type systems is that they _compose_.  What that means
is I can take two programs that typecheck, and combine them into another
well-typed program.


Now, it doesn't take too long to run into some trouble.  I think we can agree
that `avg_of` is well-typed -- from the type system's perspective it isn't
invalid, but can we conceive of a well-typed input to this program that would
go wrong?

Empty list!  In the body of the function, we'll divide zero by zero; that'll
cause an exception.  We went wrong!

But like any good zealot, I'll argue the problem here was not types but an
insufficent application of types.  We let types down, not the other way!

# Intense abstract

Now, I will put it to you that liquid types can solve the average_of function
problem for us, but I want to come at the solution a bit sideways.

Right from the beginning the paper hits us with a bunch of technical terms
that folks would reasonably not know.  Safety proprety?  Hindley-Milner type
inference?  Predicate abstraction?  Model checkers?

# Three non solutions

As an outsider of the community looking in, it's easy to feel like the core
idea of this paper just sprouted forth like Athena from the authors' heads.
It doesn't have to feel this way, though!

To motivate the paper, and also to explain all those technical terms in the
abstract, I'm going to propose three non-solutions to fixing the
above program.  

The intention here is that we're going to propose something
that isn't the right solution, but learn something from each them.  This will
hopefully set us up to feel as if inventing liquid types was a very natural 
consequence.

# Non-solution 1: A minor fix...

Even though the problem here manifested with a division by zero, the real
original sin was that we passed the empty list to `avg_of`.  Our goal is to
statically reject passing Empty, and we can!  Changing the signature to
the function specifically consuming a `Cons` will reject `avg_of(None)`.

The big observation here is that we took advantage of _inheritance_
(which I'm going to call _subtyping_) to be more specific about what
sorts of values we should accept here.  

Rather than saying "it's sufficient for either an Empty or a Cons" we're now
sort of saying "it's necessary that it's a Cons".

Why is this a non-solution? We sort of fixed the actual cause of the crash,
division by zero, by making a distant, seemingly unrelated change to the
function signature.  This happened to work for our particular case,
but it's not obvious how we can generalise this to more complicated situations.

Basically, it doesn't take long before we abut limitations of how expressive 
our current type system is.

## Non-solution 2: Fully Automated Luxury Dependent Types

A lesson we might take from non-solution 1 is to say, "well, ok, let's go find
a really sophisticated type system we can, and use that instead!"

Who here has heard of a dependent type before?

I really like Richard Eisenberg's concise definition of dependent types from
his Signals and Threads interview:

> A dependent type is a type that can _depend_ on some input that you give
> to a function.

## "Dependent Java"

The classic dependent type is the so-called indexed vector, which is a
sequence of elements of some type T, whose length _can be reasoned about
statically_:  Remember that the type argment `n` exists only at compile
time and you could imagine it's erased at compile-time.  It's not
runtime state!

Notice that immediately we can see this is more expressive than, say, Rust's
const generics, brcause the type system needs to know how the expression n+1
relates to the expression n.

## Functions

In our glorious utopian dependently-typed future, we can write all sorts of
interesting typesafe functions that operate on Vectors:

Notice another classic dependent type here: our index can't just be any int,
but a finite natural number through to n, that depends on the size of the list.

That's cool, what else can we build?  Well, the concatenation of two Vectors
yields a vector whose length is their sum.  Makes sense, if our type system
knows about incrementing an int it could well know about summation.

But here's where things get hairy.  Here's a term-level function that computes
the factorial of a number.  Conceptually we could use the _output_ of this
function as the _input_ to a dependent type, say if we were computing a Vector
of all the permutations of some vector.  Now the type system needs to know
about the execution of arbitrary Java functions (which might not terminate)??

## Non-solution #3: model-checking/SMT/Z3/???

Who here has heard of a model checker before?

Model checkers are often used to check the correctness of concurrent code.
Here's Petersen's mutual exclusion algorithm (in pseudocode, but could be
real C code or whatever), and here's the graph of states that the model
checker come up. 

Briefly: you can think of a model checker as a breadth-first exploration
through the possible states of a program, in order to check some _safety
property_ of the program, such as "do we ever eventually reach a state 
where both threads hold the lock?" 

It's a fact of model checkers that, just like our non-fancy type systems,
they're sound, push-button in their automation, and can scale up to checking
real-world software (e.g. kernel device drivers, distributed systems).

## SAT

Obviously exhaustively executing the program with all possible values is
not going to be terribly useful, so we typically abstract away concrete
program states and explore these abstract programs _symbolically_.  
The workhorse that a lot of model checkers use for this are SAT solvers.

A SAT solver solves the boolean Satisfiability problem.  This asks, "given a
collection of boolean variables and a formula in propositional logic, does
there exist an assignment of those variables such that the formula is true?"

By the way, this is code using python bindings for Z3, which is one of the top
SAT solvers out there these days.  Important to remember that Z3 variables
are not concrete booleans that we can assign True or False to, but symbolic
ones that, when used in a logical formula, could potentially be assigned
to True or False by the solver.

Critically, about when this paper was written, SAT solvers really started
getting good at solving larger and larger real-world problems.  If you know
about NP Completeness you know that there's no truly efficient way that we know
of to solve the satisfiability problems, but formal methods folks have
developed heuristics that in practice often well.  So, If you wanted to
integrate SAT solvers into your problem domain, 2008 was a great time to do it!

## SMT

SMT means "Satisfiability, modulo theories".  You can think of SMT as SAT but
with a layer on top for richer datatypes than booleans.  A "theory"
in this context can be thought of as a datatype, like Integers, and a set of
axioms about how Integers behave mathematically, that the SMT solver knows
how to compile down to a SAT query.

Here's a Python program that creates some symbolic integers, and adds some
constraints to them: some linear inequalities must hold.  A satisfying assignment
now associates each symbolic variable with an example int that satisfies 
those constraints.

## Bsearch

Let me show you how powerful SMT can be for program analysis problems.  Here's
part of an implementation of binary search.  Can this assertion ever be false?

Here's how we might model this program in Z3.  Given three symbolic 32 bit
values, when we enter the loop we know that the loop condition is true.  So,
if we were to assign to mid the formula that corresponds to taking the average
in this way, we can ask the solver "is it possible that this is not true"?

Z3 tells us these constraints are satisfiable, which means there IS a case where
our assert would fire!  If we ask it for a satisfying assignment, it gives us
what we expect, a case where things overflow.

## Fixing it

How do we fix it?

If you remember that Google blog post from like 20 years ago, you do this other
midpoint computation that doesn't overflow.  Then Z3 tells us it can't find a
counterexample.

Another way to fix it is to use BigIntegers - here we swapped out the theory of
bit vectors for mathematical integers, which can't overflow.

## Inference

So SMT solvers are amazing and they're my friend and I love them.  But there
are things that they can't do for us, at least not right out of the box.

Suppose I wanted to transform this program into Z3, but, instead of checking
some assertion, I wanted one invented for me.  This is a bit like type inference
versus typechecking.  There's no way to ask a solver "invent me a satisfying
formula that, if we were to check it, would always be true."

# What have we learned?

# The text

So, our goal for this section is to actually dig into the paper, and see how
the best parts of our three non-solutions actually feed into their work.

# Refinement types are dependent types

Let me introduce a particular kind of dependent type to you: a _refinement
type_ is the pairing of an ordinary, polymorphic type (called the _base type_)
with a logical predicate that _refines_ it. {v: int | 0 <= v ∧ v < n} refines
the base type of the integers to be bound between 0 and some other value n.
Since n is a program-level term, a refinement type is also a dependent type.
In fact, it's `Fin n` from a few minutes ago!

The big observation is that we're going to limit how expressive our refinement
predicate can be: in particular, refinement types don't allow more complicated
expressions than what an SMT solver could handle.

Remember before that our big problem with dependent types: In the limit, we
placed no restrictions on what sorts of expressions a type could depend on.
But, because our logical language in the refinement part is decidable,
_typechecking is also automatically decidable too_.   And, as we'll see soon,
we can use an interesting approach called _predicate abstraction_ to come up
with a way for decidable _type reconstruction_ too!

It's funny to me looking back that the authors don't make a huge deal about
using SMT solvers in their type system in this paper.  With the benefit of
hindsight, it's a really key advancement and I think they were one of  the first?

# what can we do with a liquid type?

Here's some work that involves a similar sort of refinement type system,
from PLDI a decade earlier.  They built their dependent type system in order
to safely reason about bounds in array programs, and observed that you can get
some pretty massive performance improvements if you can elide bounds checks.

Now, they only built a type _checker_, seemingly reimplementing a lot of the
theories we can use from an SMT solver just as a library, without doing any
type inference.  So, programmers had to annotate those types themselves.

If the liquid types paper is able to infer the types of programs that these
folks had to manually annotate, that'd a big advancement!

## Divide and conquer

In terms of a solution strategy, there's something really nice about having a
refinement type be this tuple of a base type and a predicate. We can use a
traditional type system to check and reconstruct the base type, (In the paper
that's "step 1"), and use SMT-based techniques to check and reconstruct the
constraint that the refinement represents ("steps 2 and 3").

# H-M

Who here has used the Hindley-Milner type reconstruction algorithm?
Trick question!  Most of your hands should be up.  H-M is actually a
super-common type reconstruction algorithm; ML languages, F#, Haskell,
and Rust use it as a basis for their type reconstruction, among many
others.

H-M is really beautiful because it's so natural.  Here's a program whose 
liquid type we want to infer.  Let's begin by inferring the base type.  
You tell me: what's the base type of this function?

`int -> int -> int`. How did you figure it out?  

## Type reconstruction in two parts

Well, you looked at how values were used in the body of the function, and used
those constraints to come up with a consistent typing.  This is what H-M does
too!

## With constraint variables

So in this talk I'm going to call some constraint we're going to solve for
K, and they'll all be coloured cyan.

When we solve for this series of constraints, we find that Kx and Ky and K
are all ints.

By contrast, here's a function that is not well-typed; K can't be both
an int and a bool.

Hey, this idea of building up constraints and then solving for them...does
anyone recognise what meta-algorithm this is?  (hint: are there are prolog
sickos in the audience?)  Yeah, it's unification!  We find a consistent set
of values such that all these equalities hold.  No such set of values exists
here and that's why we have a type error.

## With subtyping

One thing to note: so far we haven't talked about inferring subtypes.
Because unification looks for equality of the left and right side of the
constraints, subtyping requires a looser definition of unification.

Here, I'm either going to get to the Datadog office by MTA or by SUV,
but either way I'm getting there in some sort of motorized vehicle.  
Notice that Vehicle isn't the only valid return type: it could also type to
Vehicle's supertype, Object.  So, with subtyping we now have a few different
valid typings - intuitively it feels like Vehicle should be inferred out of
those two options, maybe because it's the most specific?

Congratulations, you understand H-M, you're now officially type theorists.

# Liquid constraint generation

Now that we know the base types, we're going to do exactly the same thing
but with the refinement predicate half.

We had a pretty good intuition for what the base types should be, but our
intution might be a bit weaker for what logical predicate to solve for.

Here's a dumb one: we could just say "this produces an int, for which we are
not constraining any values".  That's not incorrect, but it's useless, it's a
bit like saying "the return base type is Object".  This tells us nothing!

Here's another one that might be more useful: it says "our return value is one
of the two arguments".  That's at least a type that depends on a program term!
If I were to criticise this candidate, it feels like it's overfitting to the
input data.

Here's a final one: it says "the return value is at big as both inputs".  That
feels like that's the best of the three, it's in some sense "more general" or
looser than the second one.

# Typing return values

Just to get us started, here are two constraints we know for sure: on the path
where x > y, the return type has one inhabitant: x!  This is called a Singleton
type (not to be confused with the design pattern).  By symmetry, the return
type on the other path has one inhabitant: y!

## Scope constraint

This motivates the notion of a scope constraint.  A scope constraint asks what
program variables currently in scope could be used in a refinement type?

We saw a minute ago that x and y could be involved in the return type, and a
scope constraint makes that notion formal.

By contrast, nothing is in scope for the input arguments (no global variables,
so those refinement predicates can't depend on any program variables.)

## Flow constraint

There's another kind of constraint we need to build up.  The paper doesn't call
them "flow constraints" but I picked that term up somewhere and I like it.  A
flow constraint asks "what do we know about about the logical qualifier based
on what paths we took through the program?"

What's true when we return x?  Well, certainly, even though we don't know the
exact values of x and y, symbolically, we know that x > y.  Conversely, we know
!(x>y) on the opposite path.  We now know more facts!

TODO: remove slide 55? or merge it with 56?

## Joining our two flows

OK, so the thing we need to do is combine our flows into a final constraint K.
We might propose something like this: we used unification to check consistent
uses of types before, but that won't work here: clearly V == x and V == y are
different, so they wouldn't "unify".  We want a looser definition of compatibility.

It's actually subtyping that we want!  We want K to represent "a common superclass"
between V==x and V==y.  But we need a bridge between the world of types and the 
world of logical propositions in order to figure out exactly what that means.

## What's in a subtype?

So this might feel like a weird subtype, so let's go back to our family-friendly
analogies from the top of the talk.

* Any time we see an {int|K}, whatever K is, we can use (V==X) in its place.
* The fact that V could equal X needs to be somehow encoded in whatever K is.

Logical implication works in fact, similarly: whatever Q tells you, P tells you
that too.  Implication and subtyping are related concepts!

# Lynchpin of the paper:

As far as I'm concerned, the real magic of the paper is in this diagram here.
Problem is, this is just a bunch of LaTeX and Greek symbols so this is probably
opaque to most of us.  Let's learn a bit more PL paper notation to decode what
this thing is saying.

## Inference rules

```
Premise, Premise, Premise
------------------------
     Conclusion
```

This notation goes back to Gentzen and says "in order to conclude the statement
below the line, we have to prove all the statements above the line".  It's a
different way of writing logical implication.

```
Γ ⊢ l : int    Γ ⊢ r : int
---------------------------
      Γ ⊢ l + r : int
```

Here's a simple typing rule written in this style.  

`Γ ⊢ p : T` is called a "typing judgement", and can be read out as "the
program (expression) has type T under some context Gamma.  Think of Gamma as
the internal state of the typechecker: for us, all the flow and scope constraints
we accumulate live as part of this Gamma thing; it's "a bag of facts that
we know".

So this typing rule says "if we want to conclude that l + r is an int, we have
to check that l is an int and r is an int.

Figure 3 in the paper has all the typing rules we are allowed to use in a liquid
types system.  Basically, what Milner was saying with "well-typed programs don't
go wrong" is "well typed programs behave according to the type system's rules" -
we can't do addition on an int and a bool because there's (hopefully!) no typing
rule that permits it!

## This particular typing rule

OK, so what does this typing rule say?  It says if we want to conclude that two
refinement types that share a base type are subtypes...

Take all the constraints we've accumulated out of Gamma and "and" them together
with the subtype's predicate... and check if that _always_ implies the supertype's!

## Let's try this out...

Let's play around with this idea that subtyping means implication.  We agreed
that True is the "technically correct" but boring supertype.  

We can ask z3 to check whether this implication is valid for every flow - 
remember, we negate it and ask for a counterexample.  It can't give one, so this
is a valid subtyping relation!

Similarly, we could do the same thing with our "second best, overfitting"
example.  Hopefully you can kind of see here that "A and B" is stronger than
"B or C", so this should always hold.

When we ask Z3 to check the validity of it, again, no counterexample, so we can
conclude this is also a vlid subtyping relation.

# Typechecking is solved

So if we were only interested in the typechecking problem, we're done.  We read
in the program that is manually annotated with refinement types, and ask Z3 to check
validity.

We want type reconstruction, though.  So, our system needs to invent a type
seemingly out of thin air.

# Drawing from a fixed set of qualifiers

So this whole time I've been saying "coming up with the right refinement
qualifier is hard" - now it's time to tell you how the authors did it. The
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
Here's the built-in qualifiers from the paper.  The underbar is the wildcard operator
from the paper.  The point is this: every inferred liquid type is going to
be a conjunction of clauses that look like this (with the wildcard replaced
with some program variable in scope).

You're probably thinking "well, doesn't this really limit the expressivity of
the refinement types?", and, yes, indeed it does, but that's kind of the point!
The idea is that so long as you have a representitve, but still finite, set of
qualifiers, the type system has a finite amount of work to do during
typechecking.

Something not discussed in the paper is that these qualifiers can be overriden
by the application programmer.  This idea of a "user-extendable type systems"
sounds super cool to me but they don't focus on the idea at all!  I wonder why.

# Predicate abstraction

The last major technique we need to talk about is called predicate abstraction.
This is a concept that comes out of the model checking and program verification
world.

Remember that our final inferred type is going to be a conjunction of qualifiers
drawn from our basis set.  Predicate abstraction begins with that set of predicates
and removes qualifiers that have counterexamples from our solver.

Definitionally, once we remove all the qualfiers with counterexamples, we're left
with qualfiers that are safe, that match our subtyping relationship!

## Building up the intiial predicate list

So up top here I have all our built-in qualifiers, and so I'm going to fill out
an initial list of qualifiers for our two flows.

How did we go from _ <= V to x <= V and y <= V?  Remember that underbar is the 
wildcard that any valid program term can be slotted in for.  What valid terms do
we know about?  Our scope constraints!  so, x and y get stuck in there.

## Too strong!

This inital predicate list is way too strong, like, we can see obvious contradictions
like (x == V) clearly can't imply V < x.  So, predicate abstraction is going
to give us the subset of these clauses that are non-contradictory.  

The act of throwing out clauses is called "weakening", because in some sense we're
making the logical statement say fewer things.

## 0 < V

So our first clause is 0 < V.  We want to ask if the refinement type X ==V is a suype of 0<V, which from our typing rule we know means we have a validity check to do.

Z3 tells us that it's not valid, which makes sense since X == V and 0 < V are sort of
unrelated statements,

so we throw it out and move onto the next one.  Clearly this one feels more okay,
if x == V it's certainly the case that x <= V.  So that one gets to stay in.

## Merging the flows

OK, so, we've thrown out all the clauses that contradict a given flow.  What do we
do to merge the two flows into our final refinement predicate?  Well, whatever's true
in one needs to be true in the other, so we simply take the clauses that are common
between them.

And that's how we reach out final refinement type!  This whole time we were wondering
"how is the best refinement type going to use a <= expression, which never even
appeared in the source program?  Well, it's because it in fact appeared in our
logical qualifier basis set.

# How well does it work?

The authors used the previous work's array programs test suite, removed their
hand-written type annotations, and found they could infer most types automatically.
They had to add additional custom qualifiers for a few benchmarks, though.

This like caught my eye - there was a highly-optimised quicksort implementation
"whose correctness invariants remained unclear" - I really don't know what this
means and I wish I did - did the authors just not understand the optimisations?

They also inferred some liquid types on existing OCaml libraries and actually
found some out-of-bounds bugs.  Neat.

## Bonus: synquid

I told you at the beginning that types are great for three big kinds of problems.
Now it's time to show you what the third and final problem is:

TYPE DIRECTED PROGRAM SYNTHESIS: `refinement type -> program`.

This is a procedure where we start with a liquid type describing a type
signature to a function and it gives us a function that satisfies that type!

This feels a little bit like back in our SMT example, trying to infer the correct
operation in the binary search midpoint computation.

So, I can start with the specification of a function that I want, with
Refinement types annotated, and have Synquid spit out the function that behaves
according to that signature!

I bring this up only because I want to leave you with how I started this talk.
Types are great.  We take types for granted.  And yet at least for me it is
wildly nonobvious that we could begin with "how do we make safe division" and
end up with "use logic to implement my code for me".  With a little bit of
types we can do some pretty amazing stuff.

# Where to go from here?

If you want to explore some of the topics, here're some ideas to get you
started.

That's all I've got.  Thanks!

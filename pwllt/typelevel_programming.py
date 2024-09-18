from __future__ import annotations
from dataclasses import dataclass

# ***

# Here's a way to represent the natural numbers (that looks a lot
# like a linked list: the Nats are either a Zero, or the successor
# of a Nat.)

class Nat: pass

@dataclass
class Zero(Nat): 
    pass

@dataclass
class Succ(Nat):
    n: Nat

# And here are some program _terms_ that evaluate at runtime.
two: Nat = Succ(Succ(Zero()))
four: Nat = Succ(two)

# ~~~

# ***

# Here's a similar way to represent the natural numbers
# at the _type_ level: Rather than Succ's constructor taking
# one argument, it takes as a _type argument_ its predecssor.
# (If your language has type erasure, this means these definitions
# can only exist at compile time as both classes have no fields,
# so they're all "of size zero"!)

from typing import Any, Generic, TypeVar
N,T = TypeVar("N", bound=TypeLevelNat, covariant=True), TypeVar("T")

class TypeLevelNat: pass
class Z(TypeLevelNat): pass
class S(TypeLevelNat, Generic[N]): pass

# Note: `Two` and `Four` are typedefs for _subtypes_ of Nat, 
# not terms with a concrete value!
Two = S[S[Z]]
Four = S[S[Two]]

#~~~

#***

from .lists import Cons, List, sum_of, length_of

# OK, what can we do with a typelevel Nat that we couldn't before?
# How about a Vector collection where the type system can reason about
# its length?

@dataclass
class Vec(Generic[N,T]): # A Vector of N elements of type T
    elems: List[T]       # ...is backed by our linked list implementation

# To create an empty Vector, the type argument for N must be Z, the
# zero type-level natural number.
def nil() -> Vec[Z, Any]: return Vec(None)

# This constructor stays to cons an element onto a vec, the resulting
# vector's return type will have a length that's one greater than 
def cons(t: T, l: Vec[N, T]) -> Vec[S[N], T]: return Vec(Cons(t, l.elems))

# This says to take the tail of a Vec, the type system must be sure
# that its length is the successor of some Nat (that is, greater than zero)
def tail(l: Vec[S[N], T]) -> Vec[N, T]: return Vec(l.elems)

empty: Vec[Z, int] = nil()
one_three:  Vec[Two, int] = cons(1, cons(3, nil()))
#four_four: Vec[Four, int] = cons(4, cons(4, nil())) # type error: Four is not Two


# This definition of avg says that the length of the input list must be
# proven by the typechecker to be the successor of some other nat; that is,
# that it's greater than zero!
def avg(l: Vec[S[N], int]) -> int:
    return sum_of(l.elems) // length_of(l.elems)

# avg(empty) # type error
avg(one_three)

# ~~~

# ***

N1, N2 = TypeVar("N1", bound=TypeLevelNat), TypeVar("N2", bound=TypeLevelNat)

# The idea that a type is a logical proposition becomes clearer when we start 
# expressing more interesting facts within the type system.  For instance, here's
# how we might encode the fact that two TypeLevelNats are equal:

@dataclass
class NatsEq(Generic[N1, N2]): 
    # TODO: how to emphasize that this state gets elided at runtime?
    n1: N1
    n2: N2

# Like any logical proposition, it can be true or false.  Clearly, there are many
# ways to instantiate a value of NatsEq that is false, like NatsEq(Two, Four).
# By writing functions that encode how to state that two nats are equal,
# we can connect a logical proposition (the type) to a proof of that proposition
# being true (a program that operates on that type).

# Here's a fact that's always true: Zero is always equal to itself.
nats_eq_zero: NatsEq[Z, Z] = NatsEq(Z(), Z())

# Here's another fact: if you give me a proof that two nonzero nats are equal,
# then I can give you a proof that their predecessors are equal, too.
def nats_eq_succ(n1: S[N1], n2: S[N2], eq_proof: NatsEq[S[N1], S[N2]]) -> NatsEq[N1, N2]:
    pass # sorry


# This lets us do things that we couldn't before: for instance, we can write
# a version of zip, such that the input Vecs must be known to have the same length
# at compile-time, and such that the output Vec must have that same length!
def vec_zip(v1: Vec[N, T], v2: Vec[N, T]) -> Vec[N, tuple[T,T]]:
    def zip_none(v1: Vec[Z, T], v2: Vec[Z, T]) -> Vec[Z, tuple[T,T]]:
        return Vec(None)
    def zip_cons(v1: Vec[Z, T], v2: Vec[Z, T]) -> Vec[Z, tuple[T,T]]:
        return Vec(None)

    match v1, v2:
        case Vec(None), Vec(None): return zip_none(v1, v2)
        case Vec(Cons(h1, _)), Vec(Cons(h2, _)):
            t1, t2 = tail(v1), tail(v2)
            return cons((h1, h2), vec_zip(t1, t2))
        case _: assert False

# ~~~

from __future__ import annotations
from dataclasses import dataclass

from typing import Any, Generic, Optional, TypeVar
from typing import NoReturn as Never

T = TypeVar("T", covariant=True)


# Data definition for a Lisp-style linked list.
# {{{


@dataclass
class Nil(Generic[T]): pass


@dataclass
class Cons(Generic[T]):
    head: T
    tail: List[T]


List = Nil[T] | Cons[T]

l1: List[int] = Cons(1, Cons(2, Nil()))
l2: List[str] = Cons("PWL", Cons("NYC", Nil()))
l3: List[Any] = Cons(101, Cons("a", Nil()))
l4: List[Never] = Nil()

# }}}


# Some well-typed functions on a List:
# {{{

def sum_of(l: List[int]) -> int:
    match l:
        case Nil():
            return 0
        case Cons(h, t):
            return h + sum_of(t)


def length_of(l: List[T]) -> int:
    match l:
        case Nil():
            return 0
        case Cons(_, t):
            return 1 + length_of(t)


def element_at(l: List[T], n: int) -> Optional[T]:
    match l:
        case Nil():
            return None
        case Cons(h, t):
            match n:
                case 0:
                    return h
                case n:
                    return element_at(t, n - 1)


# sum_of("uh oh")

# }}}


# ...one more:
# {{{
def avg_of(l: List[int]) -> float:
    return sum_of(l) / length_of(l)

l1: List[int] = Cons(1, Cons(2, Nil()))
l2: List[str] = Cons("PWL", Cons("NYC", Nil()))

avg_of(l1)  # A well-typed program that goes well.
avg_of(Nil())  # A well-typed program that goes wrong???

# ...is there a well-typed input to this program
# that causes this program to go wrong??

# }}}

# How about:
# {{{

try:
    avg_of(Nil())
except ZeroDivisionError:
    #     avg_of(None)
    # --> sum_of(None) / length_of(None)
    # --> 0 / 0

    pass

# }}}
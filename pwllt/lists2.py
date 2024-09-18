from .lists import List, Cons, sum_of, length_of

list_of_ints = Cons(1, Cons(2, Cons(3, None)))
list_of_nothing = None
list_of_strings = Cons("a", None)

# Here's one way to solve our dilemma:
# {{{ 

def avg_of(l: List[int]) -> float:
    return sum_of(l) / length_of(l)

avg_of(list_of_ints)

avg_of(list_of_nothing) 
#avg_of(list_of_strings)

# }}}

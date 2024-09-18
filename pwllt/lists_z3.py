import z3

s = z3.Solver()

# Type constructor for a _symbolic_ List[Int], modeled by Z3.
List = z3.Datatype(f"List[Int]")

# Constructors for List[Int]:
List.declare("none")

List.declare("cons", 
          ("head", z3.IntSort()),
          ("tail", List))

List = List.create()

# l is not a particular instance of a concrete list but a symbolic
# variable representing an unknown List to solve for.
l = z3.Const("l", List)

len_of = z3.Function("len_of", List, z3.IntSort())
s.add(z3.ForAll(l, z3.If(List.is_none(l),
                         len_of(l) == 0,
                         len_of(l) == (1 + len_of(List.tail(l))))))

s.add(len_of(l) == 2)

s.check()
m = s.model()
print(m[l])

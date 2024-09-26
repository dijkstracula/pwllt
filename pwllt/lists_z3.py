import itertools

# {{{

b1, b2, b3 = True, False, True
print(b1 and b2 or (not b3))

for b1, b2, b3 in itertools.product([False, True], repeat=3):
    if b1 and b2 or (not b3):
        print(f"b1={b1}, b2={b2}, b3={b3} == True")
# }}}

# {{{
import z3

b1, b2, b3 = z3.Bools("b1 b2 b3")
fmla = z3.And(z3.Or(b1, b2), z3.Not(b3))
z3.solve(fmla)

#print(s.model())
# }}}

# {{{
s = z3.Solver()

x,y,z = z3.BitVecs("x y z", 32)

s.add(y == x)          # Precondition assumption
z = y-x                # operation
s.add(z3.Not(z == 0))  # Is there a world where z != 0?
try:
    s.check()
    print(s.model()) # If there's a model, we found a bug!
except Exception as e:
    print("As expected, we failed to find a bug!")
# }}}

# Bsearch

# {{{
s = z3.Solver()
lo, mid, hi = z3.BitVecs("lo, mid, hi", 32)
s.add(0 <= lo, 0 <= hi)

s.add(lo <= hi)         # Loop invariant
mid = (lo + hi) / 2     # Operation
s.add(z3.Not(z3.And(lo <= mid, mid <= hi)))

s.check()
print(s.model()) # If there's a model, we found a bug!

{ int | 0 <= V and V <= n }

# How doe we fix this?

s = z3.Solver()
lo, mid, hi = z3.BitVecs("lo, mid, hi", 32)
s.add(0 <= lo, 0 <= hi)

s.add(lo <= hi)         # Precondition assumption
mid = lo + ((hi - lo) / 2)
s.add(z3.Not(z3.And(lo <= mid, mid <= hi)))

try:
    s.check()
    print(s.model()) # If there's a model, we found a bug!
except Exception:
    print("As expected, no error!")

# }}}



# {{{
s = z3.Solver()

x,y,z = z3.Ints("x y z")

s.add(z3.And(0 <= x, x < 100))
y = x+1
s.add(z3.Not(z3.And(0 <= y, y < 100)))

s.check()
print(s.model()) # If there's a model, we found a bug!
# }}}

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

#s.check()
#m = s.model()
#print(m[l])

# ac.bend's tests: each identity must check.

import Base
import ../lib/ac.bend as A

# a + (b + c) == c + (b + a)
def reorder(+a: Nat, +b: Nat, +c: Nat) -> {(a + (b + c) : Nat) == (c + (b + a) : Nat) : Nat}:
  A.ac([a, b, c], A.add(A.x0(), A.add(A.x1(), A.x2())), A.add(A.x2(), A.add(A.x1(), A.x0())), {==})

# doubling distributes: 2(a + b) + c == (a + c) + (a + 2b)
def doubling(+a: Nat, +b: Nat, +c: Nat) ->
  {(Nat.double((a + b : Nat)) + c : Nat) == ((a + c) + (a + Nat.double(b)) : Nat) : Nat}:
  A.ac([a, b, c], A.add(A.dbl(A.add(A.x0(), A.x1())), A.x2()),
    A.add(A.add(A.x0(), A.x2()), A.add(A.x0(), A.dbl(A.x1()))), {==})

# atoms may be any terms, and numerals ride along as atoms:
# 1 + (x + 2y) == (1 + y) + (y + x)
def numerals(+x: Nat, +y: Nat) -> {1n+(x + Nat.double(y) : Nat) == 1n+(y + (y + x) : Nat) : Nat}:
  A.ac([x, y, 1n], A.add(A.x2(), A.add(A.x0(), A.dbl(A.x1()))),
    A.add(A.add(A.x2(), A.x1()), A.add(A.x1(), A.x0())), {==})

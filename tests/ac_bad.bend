# ac.bend's negative test: this false identity must be rejected.

import Base
import ../lib/ac.bend as A

# FALSE: a + b == a + a
def bad(+a: Nat, +b: Nat) -> {(a + b : Nat) == (a + a : Nat) : Nat}:
  A.ac([a, b], A.add(A.x0(), A.x1()), A.add(A.x0(), A.x0()), {==})

import Base
import ../ac.bend as A

# FALSE: a + b == a + a  (must be rejected)
def bad(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(a, a) : Nat}:
  A.ac([a, b], A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, {==})

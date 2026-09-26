import Base
import ../ac.bend as A

# a + (b + c) == c + (b + a)
def t1(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(c, Nat.add(b, a)) : Nat}:
  A.ac([a, b, c], A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}, A.EAdd{A.EAtom{2n}, A.EAdd{A.EAtom{1n}, A.EAtom{0n}}}, {==})

# doubling distributes: 2(a + b) + c == (a + c) + (a + 2b)
def t2(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.double(Nat.add(a, b)), c) == Nat.add(Nat.add(a, c), Nat.add(a, Nat.double(b))) : Nat}:
  A.ac([a, b, c], A.EAdd{A.EDbl{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}}, A.EAtom{2n}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{2n}}, A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{1n}}}}, {==})

# atoms may be arbitrary terms, and numerals ride along as atoms: 1 + (x + 2y) == (y + 1) + (y + x)
def t3(+x: Nat, +y: Nat) -> {1n+Nat.add(x, Nat.double(y)) == Nat.add(1n+y, Nat.add(y, x)) : Nat}:
  A.ac([x, y, 1n], A.EAdd{A.EAtom{2n}, A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{1n}}}}, A.EAdd{A.EAdd{A.EAtom{2n}, A.EAtom{1n}}, A.EAdd{A.EAtom{1n}, A.EAtom{0n}}}, {==})

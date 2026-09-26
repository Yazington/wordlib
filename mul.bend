# mul.bend: laws of Base's Nat.mul. Kept apart from nat.bend because the
# proofs use ac.bend, which imports nat.bend.

import Base
import ./nat.bend as N
import ./ac.bend as A

def mul_add_r_rev(+a: Nat, +b: Nat, +x: Nat) -> {Nat.add(Nat.mul(a, x), Nat.mul(b, x)) == Nat.mul(Nat.add(a, b), x) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.add(a, b), x), Nat.add(Nat.mul(a, x), Nat.mul(b, x)), N.mul_add_r(a, b, x))

def mul_add_l(+x: Nat, +y: Nat, +z: Nat) -> {Nat.mul(x, Nat.add(y, z)) == Nat.add(Nat.mul(x, y), Nat.mul(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(p, Nat.add(y, z)), Nat.add(Nat.mul(p, y), Nat.mul(p, z)), mul_add_l(p, y, z)) : {Nat.add(Nat.add(y, z), _) == Nat.add(Nat.add(y, Nat.mul(p, y)), Nat.add(z, Nat.mul(p, z))) : Nat}
      A.ac([y, z, Nat.mul(p, y), Nat.mul(p, z)],
        A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAdd{A.EAtom{2n}, A.EAtom{3n}}},
        A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{2n}}, A.EAdd{A.EAtom{1n}, A.EAtom{3n}}}, {==})

def mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_add_r_rev(b, Nat.mul(p, b), c) : {Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) == _ : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

def mul_double_l(+x: Nat, +y: Nat) -> {Nat.double(Nat.mul(x, y)) == Nat.mul(Nat.double(x), y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      %mul_double_l(p, y) : {Nat.double(Nat.add(y, Nat.mul(p, y))) == Nat.add(y, Nat.add(y, _)) : Nat}
      A.ac([y, Nat.mul(p, y)],
        A.EDbl{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}},
        A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{1n}}}}, {==})

def mul_double_r(+x: Nat, +y: Nat) -> {Nat.double(Nat.mul(x, y)) == Nat.mul(x, Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      %mul_double_r(p, y) : {Nat.double(Nat.add(y, Nat.mul(p, y))) == Nat.add(Nat.double(y), _) : Nat}
      A.ac([y, Nat.mul(p, y)],
        A.EDbl{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}},
        A.EAdd{A.EDbl{A.EAtom{0n}}, A.EDbl{A.EAtom{1n}}}, {==})

def mul_zero(+a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      mul_zero(p)

def mul_succ(+a: Nat, +b: Nat) -> {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_succ(p, b) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+Nat.add(b, _) : Nat}
      %N.add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      %mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n++p:
      %mul_succ(b, p) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

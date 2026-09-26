# nat_mul.bend: laws of Base's Nat.mul. Apart from nat.bend because the
# proofs use ac.bend, which imports nat.bend.

import Base
import ./nat.bend as N
import ./ac.bend as A

# a * x + b * x == (a + b) * x
def mul_add_r_rev(+a: Nat, +b: Nat, +x: Nat) ->
  {((a * x) + (b * x) : Nat) == ((a + b) * x : Nat) : Nat}:
  Equal.sym(Nat, ((a + b) * x : Nat), ((a * x) + (b * x) : Nat), N.mul_add_r(a, b, x))

# x * (y + z) == x * y + x * z
def mul_add_l(+x: Nat, +y: Nat, +z: Nat) ->
  {(x * (y + z) : Nat) == ((x * y) + (x * z) : Nat) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      +Y = (p * y : Nat)
      +Z = (p * z : Nat)
      +e = Equal.sym(Nat, (p * (y + z) : Nat), (Y + Z : Nat), mul_add_l(p, y, z))
      %e : {((y + z) + _ : Nat) == ((y + Y) + (z + Z) : Nat) : Nat}
      # (y + z) + (Y + Z) == (y + Y) + (z + Z)
      A.ac([y, z, Y, Z],
        A.add(A.add(A.x0(), A.x1()), A.add(A.x2(), A.x3())),
        A.add(A.add(A.x0(), A.x2()), A.add(A.x1(), A.x3())), {==})

# a * (b * c) == (a * b) * c
def mul_assoc(+a: Nat, +b: Nat, +c: Nat) ->
  {(a * (b * c) : Nat) == ((a * b) * c : Nat) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      +L = ((b * c) + (p * (b * c)) : Nat)
      %mul_add_r_rev(b, (p * b : Nat), c) : {L == _ : Nat}
      %mul_assoc(p, b, c) : {L == ((b * c) + _ : Nat) : Nat}
      {==}

# 2(x * y) == (2x) * y
def mul_double_l(+x: Nat, +y: Nat) ->
  {Nat.double((x * y : Nat)) == (Nat.double(x) * y : Nat) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      +M = (p * y : Nat)
      %mul_double_l(p, y) : {Nat.double((y + M : Nat)) == (y + (y + _) : Nat) : Nat}
      # 2(y + M) == y + (y + 2M)
      A.ac([y, M], A.dbl(A.add(A.x0(), A.x1())), A.add(A.x0(), A.add(A.x0(), A.dbl(A.x1()))), {==})

# 2(x * y) == x * (2y)
def mul_double_r(+x: Nat, +y: Nat) ->
  {Nat.double((x * y : Nat)) == (x * Nat.double(y) : Nat) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      +M = (p * y : Nat)
      %mul_double_r(p, y) : {Nat.double((y + M : Nat)) == (Nat.double(y) + _ : Nat) : Nat}
      # 2(y + M) == 2y + 2M
      A.ac([y, M], A.dbl(A.add(A.x0(), A.x1())), A.add(A.dbl(A.x0()), A.dbl(A.x1())), {==})

# a * 0 == 0
def mul_zero(+a: Nat) -> {(a * 0n : Nat) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      mul_zero(p)

# a + a * b == a * (1 + b)
def mul_succ(+a: Nat, +b: Nat) -> {(a + (a * b) : Nat) == (a * 1n+b : Nat) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      +M = (p * b : Nat)
      %mul_succ(p, b) : {1n+(p + (b + M) : Nat) == 1n+(b + _ : Nat) : Nat}
      %N.add_swap(p, b, M) : {1n+(p + (b + M) : Nat) == 1n+_ : Nat}
      {==}

# a * b == b * a
def mul_comm(+a: Nat, +b: Nat) -> {(a * b : Nat) == (b * a : Nat) : Nat}:
  match a:
    case 0n:
      %mul_zero(b) : {_ == (b * 0n : Nat) : Nat}
      {==}
    case 1n++p:
      %mul_succ(b, p) : {(b + (p * b) : Nat) == _ : Nat}
      %mul_comm(p, b) : {(b + (p * b) : Nat) == (b + _ : Nat) : Nat}
      {==}

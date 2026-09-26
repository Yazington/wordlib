# nat.bend: lemmas about Base's Nat.add, Nat.double and Nat.mul, and the
# facts that let a proof rule a case out (injectivity, parity, clashes).
#
# A rewrite `%e : P`, with e : {a == b : T}, takes the goal P[b/_] to
# P[a/_]: P is the goal with _ where b sits, and a takes its place.

import Base

# Addition
# --------

# a == a + 0
def add_zero(+a: Nat) -> {a == (a + 0n : Nat) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

# 1 + (a + b) == a + (1 + b)
def add_succ(+a: Nat, -b: Nat) -> {1n+(a + b : Nat) == (a + 1n+b : Nat) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+(p + b : Nat) == 1n+_ : Nat}
      {==}

# a + b == b + a
def add_comm(+a: Nat, +b: Nat) -> {(a + b : Nat) == (b + a : Nat) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+(p + b : Nat) == _ : Nat}
      %add_comm(p, b) : {1n+(p + b : Nat) == 1n+_ : Nat}
      {==}

# a + (b + c) == (a + b) + c
def add_assoc(+a: Nat, +b: Nat, +c: Nat) ->
  {(a + (b + c) : Nat) == ((a + b) + c : Nat) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+(p + (b + c) : Nat) == 1n+_ : Nat}
      {==}

# x + (y + z) == y + (x + z)
def add_swap(+x: Nat, +y: Nat, +z: Nat) ->
  {(x + (y + z) : Nat) == (y + (x + z) : Nat) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, (q + z : Nat)) : {1n+(q + (y + z) : Nat) == _ : Nat}
      %add_swap(q, y, z) : {1n+(q + (y + z) : Nat) == 1n+_ : Nat}
      {==}

# (a + b) + (c + d) == (a + c) + (b + d)
def add_4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {((a + b) + (c + d) : Nat) == ((a + c) + (b + d) : Nat) : Nat}:
  %add_assoc(a, b, (c + d : Nat)) : {_ == ((a + c) + (b + d) : Nat) : Nat}
  %add_assoc(a, c, (b + d : Nat)) : {(a + (b + (c + d)) : Nat) == _ : Nat}
  %add_swap(b, c, d) : {(a + (b + (c + d)) : Nat) == (a + _ : Nat) : Nat}
  {==}

# a + a == 2a
def double_add_self(+a: Nat) -> {(a + a : Nat) == Nat.double(a) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, p) : {1n+_ == 2n+Nat.double(p) : Nat}
      %double_add_self(p) : {2n+(p + p : Nat) == 2n+_ : Nat}
      {==}

# (a + b) * x == a * x + b * x (the one product law ac.bend needs; the
# others are in nat_mul.bend)
def mul_add_r(+a: Nat, +b: Nat, +x: Nat) ->
  {((a + b) * x : Nat) == ((a * x) + (b * x) : Nat) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(x, (p * x : Nat), (b * x : Nat)) : {(x + ((p + b) * x) : Nat) == _ : Nat}
      %mul_add_r(p, b, x) : {(x + ((p + b) * x) : Nat) == (x + _ : Nat) : Nat}
      {==}

# Clashes
# -------
# To refute e : {a == b} where a and b differ, rewrite through a motive that
# sends b to Empty and a to Unit, then answer Unit{}.

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# 1 + x == 1 + y gives x == y
def succ_inj(+x: Nat, +y: Nat, e: {1n+x == 1n+y : Nat}) -> {x == y : Nat}:
  Equal.cong(Nat, Nat, n => pred(n), 1n+x, 1n+y, e)

def is_succ(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

# 1 + x != 0
def succ_ne_zero(+x: Nat, e: {1n+x == 0n : Nat}) -> Empty:
  %e : is_succ(_)
  Unit{}

def is_false(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False != True
def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : is_false(_)
  Unit{}

# 2a == 2b gives a == b
def double_inj(+a: Nat, +b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      +e2 = Equal.sym(Nat, 0n, 2n+Nat.double(q), e)
      Empty.absurd({0n == 1n+q : Nat}, succ_ne_zero(1n+Nat.double(q), e2))
    case 1n++p 0n:
      Empty.absurd({1n+p == 0n : Nat}, succ_ne_zero(1n+Nat.double(p), e))
    case 1n++p 1n++q:
      +dp = Nat.double(p)
      +dq = Nat.double(q)
      %double_inj(p, q, succ_inj(dp, dq, succ_inj(1n+dp, 1n+dq, e))) : {1n+p == 1n+_ : Nat}
      {==}

# 2a != 2b + 1: no even Nat is odd
def parity(+a: Nat, +b: Nat, e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n _:
      succ_ne_zero(Nat.double(b), Equal.sym(Nat, 0n, 1n+Nat.double(b), e))
    case 1n++p 0n:
      succ_ne_zero(Nat.double(p), succ_inj(1n+Nat.double(p), 0n, e))
    case 1n++p 1n++q:
      +dp = Nat.double(p)
      +dq = Nat.double(q)
      parity(p, q, succ_inj(dp, 1n+dq, succ_inj(1n+dp, 2n+dq, e)))

# Cancellation
# ------------

# p + x == p + y gives x == y
def add_cancel_l(+p: Nat, +x: Nat, +y: Nat, e: {(p + x : Nat) == (p + y : Nat) : Nat}) ->
  {x == y : Nat}:
  match p:
    case 0n:
      e
    case 1n++q:
      add_cancel_l(q, x, y, succ_inj((q + x : Nat), (q + y : Nat), e))

# x + p == y + p gives x == y
def add_cancel_r(+x: Nat, +y: Nat, +p: Nat, e: {(x + p : Nat) == (y + p : Nat) : Nat}) ->
  {x == y : Nat}:
  add_cancel_l(p, x, y,
    Equal.trans(Nat, (p + x : Nat), (y + p : Nat), (p + y : Nat),
      Equal.trans(Nat, (p + x : Nat), (x + p : Nat), (y + p : Nat), add_comm(p, x), e),
      add_comm(y, p)))

# Order
# -----

# x <= y gives y == x + (y - x)
def le_sub(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) ->
  {y == (x + Nat.sub(y, x) : Nat) : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      Empty.absurd({0n == 1n+(p + 0n : Nat) : Nat}, false_ne_true(h))
    case 1n++p 1n++q:
      %le_sub(p, q, h) : {1n+q == 1n+_ : Nat}
      {==}

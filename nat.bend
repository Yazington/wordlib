# nat.bend: laws of Base's Nat.add, Nat.mul and Nat.double, as typed defs.
# Rewrites follow Bend's rule: `%e : P` with e : {a == b} takes the goal
# P[b/_] to P[a/_].

import Base

# Addition
# --------

def add_zero(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# the first two summands of a triple sum swap
def add_swap(+x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Nat.add(q, z)) : {1n+Nat.add(q, Nat.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Nat.add(q, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

# the middle summands of two pairs swap
def add_4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %add_assoc(a, b, Nat.add(c, d)) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %add_assoc(a, c, Nat.add(b, d)) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %add_swap(b, c, d) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == Nat.add(a, _) : Nat}
  {==}

# Doubling
# --------

def double_add_self(+a: Nat) -> {Nat.add(a, a) == Nat.double(a) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, p) : {1n+_ == 2n+Nat.double(p) : Nat}
      %double_add_self(p) : {2n+Nat.add(p, p) == 2n+_ : Nat}
      {==}

# Multiplication
# --------------

def mul_add_r(+a: Nat, +b: Nat, +x: Nat) -> {Nat.mul(Nat.add(a, b), x) == Nat.add(Nat.mul(a, x), Nat.mul(b, x)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(x, Nat.mul(p, x), Nat.mul(b, x)) : {Nat.add(x, Nat.mul(Nat.add(p, b), x)) == _ : Nat}
      %mul_add_r(p, b, x) : {Nat.add(x, Nat.mul(Nat.add(p, b), x)) == Nat.add(x, _) : Nat}
      {==}

# Injectivity and clashes
# -----------------------

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(+x: Nat, +y: Nat, e: {1n+x == 1n+y : Nat}) -> {x == y : Nat}:
  Equal.cong(Nat, Nat, n => pred(n), 1n+x, 1n+y, e)

# a motive for refuting 1n+x == 0n: it sends 0n to Empty
def disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def succ_ne_zero(+x: Nat, e: {1n+x == 0n : Nat}) -> Empty:
  %e : disc(_)
  Unit{}

def double_inj(+a: Nat, +b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      Empty.absurd({0n == 1n+q : Nat}, succ_ne_zero(1n+Nat.double(q), Equal.sym(Nat, 0n, 2n+Nat.double(q), e)))
    case 1n++p 0n:
      Empty.absurd({1n+p == 0n : Nat}, succ_ne_zero(1n+Nat.double(p), e))
    case 1n++p 1n++q:
      %double_inj(p, q, succ_inj(Nat.double(p), Nat.double(q), succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))) : {1n+p == 1n+_ : Nat}
      {==}

# no even Nat is odd
def parity(+a: Nat, +b: Nat, e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n _:
      succ_ne_zero(Nat.double(b), Equal.sym(Nat, 0n, 1n+Nat.double(b), e))
    case 1n++p 0n:
      succ_ne_zero(Nat.double(p), succ_inj(1n+Nat.double(p), 0n, e))
    case 1n++p 1n++q:
      parity(p, q, succ_inj(Nat.double(p), 1n+Nat.double(q), succ_inj(1n+Nat.double(p), 2n+Nat.double(q), e)))

# Cancellation
# ------------

def add_cancel_l(+p: Nat, +x: Nat, +y: Nat, e: {Nat.add(p, x) == Nat.add(p, y) : Nat}) -> {x == y : Nat}:
  match p:
    case 0n:
      e
    case 1n++q:
      add_cancel_l(q, x, y, succ_inj(Nat.add(q, x), Nat.add(q, y), e))

def add_cancel_r(+x: Nat, +y: Nat, +p: Nat, e: {Nat.add(x, p) == Nat.add(y, p) : Nat}) -> {x == y : Nat}:
  add_cancel_l(p, x, y,
    Equal.trans(Nat, Nat.add(p, x), Nat.add(y, p), Nat.add(p, y),
      Equal.trans(Nat, Nat.add(p, x), Nat.add(x, p), Nat.add(y, p), add_comm(p, x), e),
      add_comm(y, p)))

# Order
# -----

# a motive for refuting False{} == True{}: it sends True{} to Empty
def bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

# x <= y leaves room for the difference: y == x + (y - x)
def le_sub(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {y == Nat.add(x, Nat.sub(y, x)) : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      Empty.absurd({0n == Nat.add(1n+p, 0n) : Nat}, false_ne_true(h))
    case 1n++p 1n++q:
      %le_sub(p, q, h) : {1n+q == 1n+_ : Nat}
      {==}

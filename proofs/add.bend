# add.bend: the adder. adc_nat pins Word.adc to a + b + c less its carry's
# 2^n; not_nat puts every value below 2^n and to_nat_inj makes values
# determine words. The other addition laws follow by arithmetic on values.

import Base
import ../LAWS.bend as Laws
import ../word.bend as W
import ../lib/nat.bend as N
import ../lib/nat_mul.bend as M
import ../lib/ac.bend as A
import ./bits.bend as B
import ./wrap.bend as Wrap

# a + 0 == a: the head bit passes through, the carry stays 0
def Laws.add_zero(n, a):
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{False{}, t}:
      B.cons_eq(p, False{}, False{}, Word.add(p, t, Word.zero(p)), t, {==}, Laws.add_zero(p, t))
    case 1n+p WCon{True{}, t}:
      B.cons_eq(p, True{}, True{}, Word.add(p, t, Word.zero(p)), t, {==}, Laws.add_zero(p, t))

# The exact adder
# ---------------

# One row of the full adder, bits a0 + b0 + c == s + 2k (checked by fa), on
# top of the tail t + u with carry-in kb. With the tail's law as ih,
#   (s + 2R) + 2 scale(K, P) == (a0 + 2A) + ((b0 + 2B) + c)
# where R, K, A and B are the tail's sum, carry-out and inputs, and P = 2^p.
def adc_nat.bit(+s: Nat, +k: Nat, +a0: Nat, +b0: Nat, +c: Nat,
  +p: Nat, +t: Word(p), +u: Word(p), +kb: Bool,
  ih: {(Word.to_nat(p, Word.adc(p, t, u, False{}, kb))
      + W.scale(W.carry(p, t, u, kb), W.pow2(p)) : Nat)
    == (Word.to_nat(p, t) + (Word.to_nat(p, u) + k) : Nat) : Nat},
  fa: {(s + Nat.double(k) : Nat) == (a0 + (b0 + c) : Nat) : Nat}) ->
  {((s + Nat.double(Word.to_nat(p, Word.adc(p, t, u, False{}, kb))))
      + W.scale(W.carry(p, t, u, kb), Nat.double(W.pow2(p))) : Nat)
    == ((a0 + Nat.double(Word.to_nat(p, t)))
      + ((b0 + Nat.double(Word.to_nat(p, u))) + c) : Nat) : Nat}:
  +R = Word.to_nat(p, Word.adc(p, t, u, False{}, kb))
  +K = W.carry(p, t, u, kb)
  +P = W.pow2(p)
  +X = W.scale(K, P)
  +T = Word.to_nat(p, t)
  +U = Word.to_nat(p, u)
  +RHS = ((a0 + Nat.double(T)) + ((b0 + Nat.double(U)) + c) : Nat)
  +L = (s + Nat.double((T + (U + k) : Nat)) : Nat)
  %Wrap.scale_dbl(K, P) : {((s + Nat.double(R)) + _ : Nat) == RHS : Nat}
  %Wrap.double_sum(s, R, X) : {_ == RHS : Nat}
  %Equal.sym(Nat, (R + X : Nat), (T + (U + k) : Nat), ih) : {(s + Nat.double(_) : Nat) == RHS : Nat}
  # RHS == (a0 + (b0 + c)) + (2T + 2U)
  %A.ac([a0, T, b0, U, c],
    A.add(A.add(A.x0(), A.add(A.x2(), A.x4())), A.add(A.dbl(A.x1()), A.dbl(A.x3()))),
    A.add(A.add(A.x0(), A.dbl(A.x1())), A.add(A.add(A.x2(), A.dbl(A.x3())), A.x4())), {==})
    : {L == _ : Nat}
  %fa : {L == (_ + (Nat.double(T) + Nat.double(U)) : Nat) : Nat}
  # s + 2(T + (U + k)) == (s + 2k) + (2T + 2U)
  A.ac([s, T, U, k], A.add(A.x0(), A.dbl(A.add(A.x1(), A.add(A.x2(), A.x3())))),
    A.add(A.add(A.x0(), A.dbl(A.x3())), A.add(A.dbl(A.x1()), A.dbl(A.x2()))), {==})

# the full adder's truth table: inputs a0 b0 c, outputs s k
def Laws.adc_nat(n, a, b, c):
  match n a b c:
    case 0n WNil{} WNil{} False{}:
      {==}
    case 0n WNil{} WNil{} True{}:
      {==}
    #                                                        s   k   a0  b0  c
    case 1n++p WCon{False{}, +t} WCon{False{}, +u} False{}:
      adc_nat.bit(0n, 0n, 0n, 0n, 0n, p, t, u, False{}, Laws.adc_nat(p, t, u, False{}), {==})
    case 1n++p WCon{False{}, +t} WCon{False{}, +u} True{}:
      adc_nat.bit(1n, 0n, 0n, 0n, 1n, p, t, u, False{}, Laws.adc_nat(p, t, u, False{}), {==})
    case 1n++p WCon{False{}, +t} WCon{True{}, +u} False{}:
      adc_nat.bit(1n, 0n, 0n, 1n, 0n, p, t, u, False{}, Laws.adc_nat(p, t, u, False{}), {==})
    case 1n++p WCon{False{}, +t} WCon{True{}, +u} True{}:
      adc_nat.bit(0n, 1n, 0n, 1n, 1n, p, t, u, True{}, Laws.adc_nat(p, t, u, True{}), {==})
    case 1n++p WCon{True{}, +t} WCon{False{}, +u} False{}:
      adc_nat.bit(1n, 0n, 1n, 0n, 0n, p, t, u, False{}, Laws.adc_nat(p, t, u, False{}), {==})
    case 1n++p WCon{True{}, +t} WCon{False{}, +u} True{}:
      adc_nat.bit(0n, 1n, 1n, 0n, 1n, p, t, u, True{}, Laws.adc_nat(p, t, u, True{}), {==})
    case 1n++p WCon{True{}, +t} WCon{True{}, +u} False{}:
      adc_nat.bit(0n, 1n, 1n, 1n, 0n, p, t, u, True{}, Laws.adc_nat(p, t, u, True{}), {==})
    case 1n++p WCon{True{}, +t} WCon{True{}, +u} True{}:
      adc_nat.bit(1n, 1n, 1n, 1n, 1n, p, t, u, True{}, Laws.adc_nat(p, t, u, True{}), {==})

# Bounds and injectivity
# ----------------------

# 1 + (w + not w) == 2^n: a head bit and its complement add to 1
def Laws.not_nat(n, w):
  match n w:
    case 0n WNil{}:
      {==}
    case 1n++p WCon{False{}, +t}:
      +T = Word.to_nat(p, t)
      +T2 = Word.to_nat(p, Word.not(p, t))
      %Laws.not_nat(p, t) : {1n+(Nat.double(T) + 1n+Nat.double(T2) : Nat) == Nat.double(_) : Nat}
      # 1 + (2T + (1 + 2T2)) == 2(1 + (T + T2))
      A.ac([T, T2, 1n], A.add(A.x2(), A.add(A.dbl(A.x0()), A.add(A.x2(), A.dbl(A.x1())))),
        A.dbl(A.add(A.x2(), A.add(A.x0(), A.x1()))), {==})
    case 1n++p WCon{True{}, +t}:
      +T = Word.to_nat(p, t)
      +T2 = Word.to_nat(p, Word.not(p, t))
      %Laws.not_nat(p, t) : {2n+(Nat.double(T) + Nat.double(T2) : Nat) == Nat.double(_) : Nat}
      # 1 + ((1 + 2T) + 2T2) == 2(1 + (T + T2))
      A.ac([T, T2, 1n], A.add(A.x2(), A.add(A.add(A.x2(), A.dbl(A.x0())), A.dbl(A.x1()))),
        A.dbl(A.add(A.x2(), A.add(A.x0(), A.x1()))), {==})

# equal values, equal words: head bits by parity, tails by induction
def Laws.to_nat_inj(n, a, b, h):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n++p WCon{False{}, +t} WCon{False{}, +u}:
      +T = Word.to_nat(p, t)
      +U = Word.to_nat(p, u)
      B.cons_eq(p, False{}, False{}, t, u, {==}, Laws.to_nat_inj(p, t, u, N.double_inj(T, U, h)))
    case 1n++p WCon{True{}, +t} WCon{True{}, +u}:
      +T = Word.to_nat(p, t)
      +U = Word.to_nat(p, u)
      +h2 = N.double_inj(T, U, N.succ_inj(Nat.double(T), Nat.double(U), h))
      B.cons_eq(p, True{}, True{}, t, u, {==}, Laws.to_nat_inj(p, t, u, h2))
    case 1n++p WCon{False{}, +t} WCon{True{}, +u}:
      +T = Word.to_nat(p, t)
      +U = Word.to_nat(p, u)
      Empty.absurd({WCon{False{}, t} == WCon{True{}, u} : Word.Con<p>}, N.parity(T, U, h))
    case 1n++p WCon{True{}, +t} WCon{False{}, +u}:
      +T = Word.to_nat(p, t)
      +U = Word.to_nat(p, u)
      +h2 = Equal.sym(Nat, 1n+Nat.double(T), Nat.double(U), h)
      Empty.absurd({WCon{True{}, t} == WCon{False{}, u} : Word.Con<p>}, N.parity(U, T, h2))

# Addition without overflow
# -------------------------

# the adder's law for a + b, with carry-in 0
def add_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {(Word.to_nat(n, Word.add(n, a, b)) + W.scale(W.carry(n, a, b, False{}), W.pow2(n)) : Nat)
    == (Word.to_nat(n, a) + Word.to_nat(n, b) : Nat) : Nat}:
  +L = (Word.to_nat(n, Word.add(n, a, b)) + W.scale(W.carry(n, a, b, False{}), W.pow2(n)) : Nat)
  +B0 = Word.to_nat(n, b)
  %Equal.sym(Nat, B0, (B0 + 0n : Nat), N.add_zero(B0)) : {L == (Word.to_nat(n, a) + _ : Nat) : Nat}
  Laws.adc_nat(n, a, b, False{})

# a + b below 2^n leaves no carry, so the sum is exact
def Laws.add_exact(n, a, b, g, h):
  +S = (Word.to_nat(n, a) + Word.to_nat(n, b) : Nat)
  Wrap.no_carry(W.carry(n, a, b, False{}), Word.to_nat(n, Word.add(n, a, b)), S, W.pow2(n), g,
    add_eq(n, a, b), h)

# Associativity
# -------------
# Both groupings add to A + (B + C) once their carries' 2^n are added
# back; both are below 2^n; so they have the same value (uniq), and the same
# words (to_nat_inj).

# scale(K2, P) + scale(K1, P) == (K2 + K1) P
def scales(+K2: Bool, +K1: Bool, +P: Nat) ->
  {(W.scale(K2, P) + W.scale(K1, P) : Nat) == ((W.b2n(K2) + W.b2n(K1)) * P : Nat) : Nat}:
  +L = (W.scale(K2, P) + W.scale(K1, P) : Nat)
  %M.mul_add_r_rev(W.b2n(K2), W.b2n(K1), P) : {L == _ : Nat}
  %Wrap.scale_mul(K2, P) : {L == (_ + (W.b2n(K1) * P) : Nat) : Nat}
  %Wrap.scale_mul(K1, P) : {L == (W.scale(K2, P) + _ : Nat) : Nat}
  {==}

# (a + b) + c, by value: X + (k2 + k1) 2^n == A + (B + C), where k1 and k2
# are the carries of a + b and of (a + b) + c
def assoc.left(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) ->
  {(Word.to_nat(n, Word.add(n, Word.add(n, a, b), c))
      + ((W.b2n(W.carry(n, Word.add(n, a, b), c, False{})) + W.b2n(W.carry(n, a, b, False{})))
        * W.pow2(n)) : Nat)
    == (Word.to_nat(n, a) + (Word.to_nat(n, b) + Word.to_nat(n, c)) : Nat) : Nat}:
  +P = W.pow2(n)
  +ab = Word.add(n, a, b)
  +X = Word.to_nat(n, Word.add(n, ab, c))
  +AB = Word.to_nat(n, ab)
  +k2 = W.carry(n, ab, c, False{})
  +k1 = W.carry(n, a, b, False{})
  +K2 = W.scale(k2, P)
  +K1 = W.scale(k1, P)
  +A0 = Word.to_nat(n, a)
  +B0 = Word.to_nat(n, b)
  +C0 = Word.to_nat(n, c)
  +RHS = (A0 + (B0 + C0) : Nat)
  %scales(k2, k1, P) : {(X + _ : Nat) == RHS : Nat}
  # X + (K2 + K1) == (X + K2) + K1
  %A.ac([X, K2, K1],
    A.add(A.add(A.x0(), A.x1()), A.x2()), A.add(A.x0(), A.add(A.x1(), A.x2())), {==})
    : {_ == RHS : Nat}
  %Equal.sym(Nat, (X + K2 : Nat), (AB + C0 : Nat), add_eq(n, ab, c)) : {(_ + K1 : Nat) == RHS : Nat}
  # (AB + C) + K1 == (AB + K1) + C
  %A.ac([AB, C0, K1],
    A.add(A.add(A.x0(), A.x2()), A.x1()), A.add(A.add(A.x0(), A.x1()), A.x2()), {==})
    : {_ == RHS : Nat}
  %Equal.sym(Nat, (AB + K1 : Nat), (A0 + B0 : Nat), add_eq(n, a, b)) : {(_ + C0 : Nat) == RHS : Nat}
  Equal.sym(Nat, RHS, ((A0 + B0) + C0 : Nat), N.add_assoc(A0, B0, C0))

# a + (b + c), by value: Y + (j2 + j1) 2^n == A + (B + C), where j1 and j2
# are the carries of b + c and of a + (b + c)
def assoc.right(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) ->
  {(Word.to_nat(n, Word.add(n, a, Word.add(n, b, c)))
      + ((W.b2n(W.carry(n, a, Word.add(n, b, c), False{})) + W.b2n(W.carry(n, b, c, False{})))
        * W.pow2(n)) : Nat)
    == (Word.to_nat(n, a) + (Word.to_nat(n, b) + Word.to_nat(n, c)) : Nat) : Nat}:
  +P = W.pow2(n)
  +bc = Word.add(n, b, c)
  +Y = Word.to_nat(n, Word.add(n, a, bc))
  +BC = Word.to_nat(n, bc)
  +j2 = W.carry(n, a, bc, False{})
  +j1 = W.carry(n, b, c, False{})
  +J2 = W.scale(j2, P)
  +J1 = W.scale(j1, P)
  +A0 = Word.to_nat(n, a)
  +RHS = (A0 + (Word.to_nat(n, b) + Word.to_nat(n, c)) : Nat)
  %scales(j2, j1, P) : {(Y + _ : Nat) == RHS : Nat}
  # Y + (J2 + J1) == (Y + J2) + J1
  %A.ac([Y, J2, J1],
    A.add(A.add(A.x0(), A.x1()), A.x2()), A.add(A.x0(), A.add(A.x1(), A.x2())), {==})
    : {_ == RHS : Nat}
  %Equal.sym(Nat, (Y + J2 : Nat), (A0 + BC : Nat), add_eq(n, a, bc)) : {(_ + J1 : Nat) == RHS : Nat}
  %N.add_assoc(A0, BC, J1) : {_ == RHS : Nat}
  %Equal.sym(Nat, (BC + J1 : Nat), (Word.to_nat(n, b) + Word.to_nat(n, c) : Nat), add_eq(n, b, c))
    : {(A0 + _ : Nat) == RHS : Nat}
  {==}

def Laws.add_assoc(n, a, b, c):
  +P = W.pow2(n)
  +wl = Word.add(n, a, Word.add(n, b, c))
  +wr = Word.add(n, Word.add(n, a, b), c)
  +Y = Word.to_nat(n, wl)
  +X = Word.to_nat(n, wr)
  +jl = (W.b2n(W.carry(n, a, Word.add(n, b, c), False{})) + W.b2n(W.carry(n, b, c, False{})) : Nat)
  +kr = (W.b2n(W.carry(n, Word.add(n, a, b), c, False{})) + W.b2n(W.carry(n, a, b, False{})) : Nat)
  +S = (Word.to_nat(n, a) + (Word.to_nat(n, b) + Word.to_nat(n, c)) : Nat)
  # Y + jl P == S == X + kr P
  +e = Equal.trans(Nat, (Y + (jl * P) : Nat), S, (X + (kr * P) : Nat),
    assoc.right(n, a, b, c), Equal.sym(Nat, (X + (kr * P) : Nat), S, assoc.left(n, a, b, c)))
  +GY = Word.to_nat(n, Word.not(n, wl))
  +GX = Word.to_nat(n, Word.not(n, wr))
  Laws.to_nat_inj(n, wl, wr,
    Wrap.uniq(Y, X, P, GY, GX, jl, kr, e, Laws.not_nat(n, wl), Laws.not_nat(n, wr)))

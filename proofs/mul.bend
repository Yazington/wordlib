# mul.bend: multiplication. Word.mul is shift-and-add: for each bit of a,
# add b to the accumulator when the bit is 1, then shift b left. W.mulq
# counts how often that wraps past 2^n, and mul_go_nat keeps
#   result + mulq 2^n == acc + a b
# at every step. The product laws follow from it by arithmetic on values.

import Base
import ../LAWS.bend as Laws
import ../word.bend as W
import ../lib/nat.bend as N
import ../lib/nat_mul.bend as M
import ../lib/ac.bend as A
import ./add.bend as Add
import ./shift.bend as Shift
import ./wrap.bend as Wrap

# A scale(K, P) == (A b2n(K)) P
def mul_scale(+A0: Nat, +K: Bool, +P: Nat) ->
  {(A0 * W.scale(K, P) : Nat) == ((A0 * W.b2n(K)) * P : Nat) : Nat}:
  %Equal.sym(Nat, W.scale(K, P), (W.b2n(K) * P : Nat), Wrap.scale_mul(K, P))
    : {(A0 * _ : Nat) == ((A0 * W.b2n(K)) * P : Nat) : Nat}
  M.mul_assoc(A0, W.b2n(K), P)

# shifting b left doubles its product with A, less the top bit shifted out:
# 2A b == A shl(b) + A scale(top, 2^n)
def shl_prod(+n: Nat, +b: Word(n), +A0: Nat) ->
  {(Nat.double(A0) * Word.to_nat(n, b) : Nat)
    == ((A0 * Word.to_nat(n, Word.shl(n, b)))
      + (A0 * W.scale(W.top(n, False{}, b), W.pow2(n))) : Nat) : Nat}:
  +B0 = Word.to_nat(n, b)
  +SB = Word.to_nat(n, Word.shl(n, b))
  +ST = W.scale(W.top(n, False{}, b), W.pow2(n))
  +RHS = ((A0 * SB) + (A0 * ST) : Nat)
  %M.mul_double_l(A0, B0) : {_ == RHS : Nat}
  %M.mul_add_l(A0, SB, ST) : {Nat.double((A0 * B0 : Nat)) == _ : Nat}
  %Equal.sym(Nat, (SB + ST : Nat), Nat.double(B0), Laws.shl_nat(n, b))
    : {Nat.double((A0 * B0 : Nat)) == (A0 * _ : Nat) : Nat}
  M.mul_double_r(A0, B0)

# a 0 bit: nothing added, b shifted
def mul_go.zero(+n: Nat, +mp: Nat, +at: Word(mp), +b: Word(n), +acc: Word(n),
  ih: {(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc))
      + (W.mulq(n, mp, at, Word.shl(n, b), acc) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, acc) + (Word.to_nat(mp, at) * Word.to_nat(n, Word.shl(n, b))) : Nat)
    : Nat}) ->
  {(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc))
      + ((W.mulq(n, mp, at, Word.shl(n, b), acc)
        + (Word.to_nat(mp, at) * W.b2n(W.top(n, False{}, b)))) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, acc) + (Nat.double(Word.to_nat(mp, at)) * Word.to_nat(n, b)) : Nat) : Nat}:
  +P = W.pow2(n)
  +R = Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc))
  +Q = W.mulq(n, mp, at, Word.shl(n, b), acc)
  +A1 = Word.to_nat(mp, at)
  +TOP = W.top(n, False{}, b)
  +ACC = Word.to_nat(n, acc)
  +SB = Word.to_nat(n, Word.shl(n, b))
  +AST = (A1 * W.scale(TOP, P) : Nat)
  +RHS = (ACC + (Nat.double(A1) * Word.to_nat(n, b)) : Nat)
  %M.mul_add_r_rev(Q, (A1 * W.b2n(TOP) : Nat), P) : {(R + _ : Nat) == RHS : Nat}
  %mul_scale(A1, TOP, P) : {(R + ((Q * P) + _) : Nat) == RHS : Nat}
  %Equal.sym(Nat, (R + ((Q * P) + AST) : Nat), ((R + (Q * P)) + AST : Nat),
    N.add_assoc(R, (Q * P : Nat), AST)) : {_ == RHS : Nat}
  %Equal.sym(Nat, (R + (Q * P) : Nat), (ACC + (A1 * SB) : Nat), ih) : {(_ + AST : Nat) == RHS : Nat}
  %N.add_assoc(ACC, (A1 * SB : Nat), AST) : {_ == RHS : Nat}
  %shl_prod(n, b, A1) : {(ACC + _ : Nat) == RHS : Nat}
  {==}

# a 1 bit: b added (with its carry), b shifted
def mul_go.one(+n: Nat, +mp: Nat, +at: Word(mp), +b: Word(n), +acc: Word(n),
  ih: {(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)))
      + (W.mulq(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, Word.add(n, acc, b))
      + (Word.to_nat(mp, at) * Word.to_nat(n, Word.shl(n, b))) : Nat) : Nat}) ->
  {(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)))
      + ((W.mulq(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))
        + ((Word.to_nat(mp, at) * W.b2n(W.top(n, False{}, b)))
          + W.b2n(W.carry(n, acc, b, False{})))) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, acc)
      + (Word.to_nat(n, b) + (Nat.double(Word.to_nat(mp, at)) * Word.to_nat(n, b))) : Nat) : Nat}:
  +P = W.pow2(n)
  +sum = Word.add(n, acc, b)
  +R = Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), sum))
  +Q = W.mulq(n, mp, at, Word.shl(n, b), sum)
  +A1 = Word.to_nat(mp, at)
  +B0 = Word.to_nat(n, b)
  +TOP = W.top(n, False{}, b)
  +K = W.carry(n, acc, b, False{})
  +ACC = Word.to_nat(n, acc)
  +ACC2 = Word.to_nat(n, sum)
  +SB = Word.to_nat(n, Word.shl(n, b))
  +AST = (A1 * W.scale(TOP, P) : Nat)
  +SK = W.scale(K, P)
  +RHS = (ACC + (B0 + (Nat.double(A1) * B0)) : Nat)
  %M.mul_add_r_rev(Q, ((A1 * W.b2n(TOP)) + W.b2n(K) : Nat), P) : {(R + _ : Nat) == RHS : Nat}
  %M.mul_add_r_rev((A1 * W.b2n(TOP) : Nat), W.b2n(K), P) : {(R + ((Q * P) + _) : Nat) == RHS : Nat}
  %mul_scale(A1, TOP, P) : {(R + ((Q * P) + (_ + (W.b2n(K) * P))) : Nat) == RHS : Nat}
  %Wrap.scale_mul(K, P) : {(R + ((Q * P) + (AST + _)) : Nat) == RHS : Nat}
  %Equal.sym(Nat, (R + ((Q * P) + (AST + SK)) : Nat), ((R + (Q * P)) + (AST + SK) : Nat),
    N.add_assoc(R, (Q * P : Nat), (AST + SK : Nat))) : {_ == RHS : Nat}
  %Equal.sym(Nat, (R + (Q * P) : Nat), (ACC2 + (A1 * SB) : Nat), ih)
    : {(_ + (AST + SK) : Nat) == RHS : Nat}
  # (ACC2 + A SB) + (AST + SK) == (ACC2 + SK) + (A SB + AST)
  %A.ac([ACC2, (A1 * SB : Nat), AST, SK],
    A.add(A.add(A.x0(), A.x3()), A.add(A.x1(), A.x2())),
    A.add(A.add(A.x0(), A.x1()), A.add(A.x2(), A.x3())), {==}) : {_ == RHS : Nat}
  %Equal.sym(Nat, (ACC2 + SK : Nat), (ACC + (B0 + 0n) : Nat), Laws.adc_nat(n, acc, b, False{}))
    : {(_ + ((A1 * SB) + AST) : Nat) == RHS : Nat}
  %shl_prod(n, b, A1) : {((ACC + (B0 + 0n)) + _ : Nat) == RHS : Nat}
  # (ACC + (B + 0)) + 2A B == ACC + (B + 2A B)
  A.ac([ACC, B0, (Nat.double(A1) * B0 : Nat)],
    A.add(A.add(A.x0(), A.add(A.x1(), A.zero())), A.x2()),
    A.add(A.x0(), A.add(A.x1(), A.x2())), {==})

def Laws.mul_go_nat(n, m, a, b, acc):
  match m a:
    case 0n _:
      {==}
    case 1n++mp WCon{False{}, +at}:
      mul_go.zero(n, mp, at, b, acc, Laws.mul_go_nat(n, mp, at, Word.shl(n, b), acc))
    case 1n++mp WCon{True{}, +at}:
      mul_go.one(n, mp, at, b, acc, Laws.mul_go_nat(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)))

# The product
# -----------

# the zero word's value is 0
def mul_nat.zero(+n: Nat) -> {0n == Word.to_nat(n, Word.zero(n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %mul_nat.zero(p) : {0n == Nat.double(_) : Nat}
      {==}

# 0 + M == M, with 0 as the value of the zero word
def mul_nat.start(+n: Nat, +M0: Nat) -> {(Word.to_nat(n, Word.zero(n)) + M0 : Nat) == M0 : Nat}:
  %mul_nat.zero(n) : {(_ + M0 : Nat) == M0 : Nat}
  {==}

# the multiplier started with acc = 0
def Laws.mul_nat(n, a, b):
  +zero = Word.zero(n)
  +AB = (Word.to_nat(n, a) * Word.to_nat(n, b) : Nat)
  +L = (Word.to_nat(n, Word.mul(n, a, b)) + (W.mulq(n, n, a, b, zero) * W.pow2(n)) : Nat)
  Equal.trans(Nat, L, (Word.to_nat(n, zero) + AB : Nat), AB,
    Laws.mul_go_nat(n, n, a, b, zero), mul_nat.start(n, AB))

# the product law, with its right side as a b + 0 2^n
def mul_exact.pad(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {(Word.to_nat(n, Word.mul(n, a, b)) + (W.mulq(n, n, a, b, Word.zero(n)) * W.pow2(n)) : Nat)
    == ((Word.to_nat(n, a) * Word.to_nat(n, b)) + 0n : Nat) : Nat}:
  +AB = (Word.to_nat(n, a) * Word.to_nat(n, b) : Nat)
  +L = (Word.to_nat(n, Word.mul(n, a, b)) + (W.mulq(n, n, a, b, Word.zero(n)) * W.pow2(n)) : Nat)
  %N.add_zero(AB) : {L == _ : Nat}
  Laws.mul_nat(n, a, b)

# the product and a b are both below 2^n and differ by a multiple of it
def Laws.mul_exact(n, a, b, g, h):
  +r = Word.mul(n, a, b)
  +Q = W.mulq(n, n, a, b, Word.zero(n))
  +AB = (Word.to_nat(n, a) * Word.to_nat(n, b) : Nat)
  Wrap.uniq(Word.to_nat(n, r), AB, W.pow2(n), Word.to_nat(n, Word.not(n, r)), g, Q, 0n,
    mul_exact.pad(n, a, b), Laws.not_nat(n, r), h)

# a b and b a are the same Nat, so the two products differ by multiples of
# 2^n
def mul_comm.values(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {(Word.to_nat(n, Word.mul(n, a, b)) + (W.mulq(n, n, a, b, Word.zero(n)) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, Word.mul(n, b, a)) + (W.mulq(n, n, b, a, Word.zero(n)) * W.pow2(n)) : Nat)
    : Nat}:
  +A0 = Word.to_nat(n, a)
  +B0 = Word.to_nat(n, b)
  +L1 = (Word.to_nat(n, Word.mul(n, a, b)) + (W.mulq(n, n, a, b, Word.zero(n)) * W.pow2(n)) : Nat)
  +L2 = (Word.to_nat(n, Word.mul(n, b, a)) + (W.mulq(n, n, b, a, Word.zero(n)) * W.pow2(n)) : Nat)
  Equal.trans(Nat, L1, (A0 * B0 : Nat), L2, Laws.mul_nat(n, a, b),
    Equal.trans(Nat, (A0 * B0 : Nat), (B0 * A0 : Nat), L2, M.mul_comm(A0, B0),
      Equal.sym(Nat, L2, (B0 * A0 : Nat), Laws.mul_nat(n, b, a))))

def Laws.mul_comm(n, a, b):
  +ab = Word.mul(n, a, b)
  +ba = Word.mul(n, b, a)
  Laws.to_nat_inj(n, ab, ba,
    Wrap.uniq(Word.to_nat(n, ab), Word.to_nat(n, ba), W.pow2(n),
      Word.to_nat(n, Word.not(n, ab)), Word.to_nat(n, Word.not(n, ba)),
      W.mulq(n, n, a, b, Word.zero(n)), W.mulq(n, n, b, a, Word.zero(n)),
      mul_comm.values(n, a, b), Laws.not_nat(n, ab), Laws.not_nat(n, ba)))

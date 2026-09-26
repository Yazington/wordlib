# sub.bend: subtraction. Word.sub(a, b) is Word.adc with the subtract flag,
# which adds the complement of b with carry-in 1 (adc_sub); with the exact
# adder and the complement's value (not_nat), a - b is exactly d whenever
# a = b + d.

import Base
import ../LAWS.bend as Laws
import ../word.bend as W
import ../lib/nat.bend as N
import ../lib/ac.bend as A
import ./add.bend as Add
import ./wrap.bend as Wrap

# One bit of adc_sub: both sides run the full adder on the same bits, so
# they share its output pair sk. Its carry k is only known inside sk, so the
# tails' law comes in as a function of k.
def adc_sub.step(-p: Nat, at: Word(p), bt: Word(p), sk: Bool & Bool,
  ih: @k: Bool ->
    {Word.adc(p, at, Word.not(p, bt), False{}, k) == Word.adc(p, at, bt, True{}, k) : Word(p)}) ->
  {Word.adc.con(p, at, Word.not(p, bt), False{}, sk)
    == Word.adc.con(p, at, bt, True{}, sk) : Word(1n+p)}:
  (s, k) = sk
  %ih(k) : {WCon{s, Word.adc(p, at, Word.not(p, bt), False{}, k)} == WCon{s, _} : Word.Con<p>}
  {==}

def Laws.adc_sub(n, a, b, c):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n++p WCon{x, +t} WCon{y, +u}:
      adc_sub.step(p, t, u, Bool.full_add(x, Bool.not(y), c), k => Laws.adc_sub(p, t, u, k))

# a == b + d gives a + (not b + 1) == d + 2^n
def sub_eq.value(+n: Nat, +a: Word(n), +b: Word(n), +d: Nat,
  h: {Word.to_nat(n, a) == (Word.to_nat(n, b) + d : Nat) : Nat}) ->
  {(Word.to_nat(n, a) + (Word.to_nat(n, Word.not(n, b)) + 1n) : Nat)
    == (d + W.pow2(n) : Nat) : Nat}:
  +A0 = Word.to_nat(n, a)
  +B0 = Word.to_nat(n, b)
  +NB = Word.to_nat(n, Word.not(n, b))
  %Laws.not_nat(n, b) : {(A0 + (NB + 1n) : Nat) == (d + _ : Nat) : Nat}
  %Equal.sym(Nat, A0, (B0 + d : Nat), h)
    : {(_ + (NB + 1n) : Nat) == (d + 1n+(B0 + NB : Nat) : Nat) : Nat}
  # (B + d) + (NB + 1) == d + (1 + (B + NB))
  A.ac([B0, d, NB, 1n], A.add(A.add(A.x0(), A.x1()), A.add(A.x2(), A.x3())),
    A.add(A.x1(), A.add(A.x3(), A.add(A.x0(), A.x2()))), {==})

# a - b plus its carry's 2^n is d + 2^n
def sub_eq(+n: Nat, +a: Word(n), +b: Word(n), +d: Nat,
  h: {Word.to_nat(n, a) == (Word.to_nat(n, b) + d : Nat) : Nat}) ->
  {(Word.to_nat(n, Word.sub(n, a, b))
      + W.scale(W.carry(n, a, Word.not(n, b), True{}), W.pow2(n)) : Nat)
    == (d + W.pow2(n) : Nat) : Nat}:
  +nb = Word.not(n, b)
  +K = W.scale(W.carry(n, a, nb, True{}), W.pow2(n))
  +RHS = (d + W.pow2(n) : Nat)
  %Laws.adc_sub(n, a, b, True{}) : {(Word.to_nat(n, _) + K : Nat) == RHS : Nat}
  Equal.trans(Nat, (Word.to_nat(n, Word.adc(n, a, nb, False{}, True{})) + K : Nat),
    (Word.to_nat(n, a) + (Word.to_nat(n, nb) + 1n) : Nat), RHS,
    Laws.adc_nat(n, a, nb, True{}), sub_eq.value(n, a, b, d, h))

# a - b is below 2^n and adds up to d + 2^n with its carry: it is d
def Laws.sub_nat(n, a, b, d, h):
  +r = Word.sub(n, a, b)
  Wrap.wrap_exact(W.carry(n, a, Word.not(n, b), True{}), Word.to_nat(n, r), d, W.pow2(n),
    Word.to_nat(n, Word.not(n, r)), sub_eq(n, a, b, d, h), Laws.not_nat(n, r))

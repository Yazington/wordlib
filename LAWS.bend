# wordlib: laws about Base's fixed-width words. Word(n) is n Bools,
# least significant bit first; U32 wraps Word(32n).

import Base
import ./word.bend as W

# Bitwise algebra
# ---------------

# LAW: xor is commutative
law xor_comm:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}

# LAW: xor is associative
law xor_assoc:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Word(n)
  {Word.xor(n, a, Word.xor(n, b, c)) == Word.xor(n, Word.xor(n, a, b), c) : Word(n)}

# LAW: zero is the identity of xor
law xor_zero:
  for n: Nat
  for a: Word(n)
  {Word.xor(n, a, Word.zero(n)) == a : Word(n)}

# LAW: every word is its own xor inverse
law xor_self:
  for n: Nat
  for +a: Word(n)
  {Word.xor(n, a, a) == Word.zero(n) : Word(n)}

# LAW: and is commutative
law and_comm:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.and(n, a, b) == Word.and(n, b, a) : Word(n)}

# LAW: and is associative
law and_assoc:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Word(n)
  {Word.and(n, a, Word.and(n, b, c)) == Word.and(n, Word.and(n, a, b), c) : Word(n)}

# LAW: or is commutative
law or_comm:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.or(n, a, b) == Word.or(n, b, a) : Word(n)}

# LAW: or is associative
law or_assoc:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Word(n)
  {Word.or(n, a, Word.or(n, b, c)) == Word.or(n, Word.or(n, a, b), c) : Word(n)}

# LAW: not is an involution
law not_not:
  for n: Nat
  for a: Word(n)
  {Word.not(n, Word.not(n, a)) == a : Word(n)}

# LAW: De Morgan: not (a and b) is (not a) or (not b)
law not_and:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.not(n, Word.and(n, a, b)) == Word.or(n, Word.not(n, a), Word.not(n, b)) : Word(n)}

# Arithmetic
# ----------

# LAW: zero is the identity of add
law add_zero:
  for n: Nat
  for a: Word(n)
  {Word.add(n, a, Word.zero(n)) == a : Word(n)}

# LAW: the adder is exact. An n-bit add with carry-in c yields a word
# and a carry-out; the word plus the carry-out's weight 2^n is the true
# sum a + b + c. Together with the bound on words, this pins Word.add
# to addition mod 2^n.
law adc_nat:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), W.scale(W.carry(n, a, b, c), W.pow2(n))) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), W.b2n(c))) : Nat}

# LAW: a word and its complement sum to 2^n - 1. So every word's value
# is below 2^n, with to_nat(not w) as the gap.
law not_nat:
  for n: Nat
  for w: Word(n)
  {1n+Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))) == W.pow2(n) : Nat}

# LAW: to_nat is injective: words with the same value are the same word
law to_nat_inj:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

# LAW: subtracting is adding the complement: Word.sub(a, b) is a + not b
# with carry-in 1, i.e. a + (2^n - b) mod 2^n.
law adc_sub:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {Word.adc(n, a, Word.not(n, b), False{}, c) == Word.adc(n, a, b, True{}, c) : Word(n)}

# LAW: subtraction without wrap: when a = b + d, a - b is exactly d
law sub_nat:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +d: Nat
  for h: {Word.to_nat(n, a) == Nat.add(Word.to_nat(n, b), d) : Nat}
  {Word.to_nat(n, Word.sub(n, a, b)) == d : Nat}

# LAW: word addition is associative
law add_assoc:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  {Word.add(n, a, Word.add(n, b, c)) == Word.add(n, Word.add(n, a, b), c) : Word(n)}

# LAW: addition without overflow: when a + b < 2^n, the word sum is exact
law add_exact:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +g: Nat
  for h: {1n+Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), g) == W.pow2(n) : Nat}
  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

# LAW: shifting c in from below doubles the value, adds c and drops the
# top bit, whose weight is 2^n
law shl_put:
  for n: Nat
  for +c: Bool
  for +w: Word(n)
  {Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), W.scale(W.top(n, c, w), W.pow2(n))) == Nat.add(W.b2n(c), Nat.double(Word.to_nat(n, w))) : Nat}

# LAW: shl doubles, less the top bit's 2^n
law shl_nat:
  for n: Nat
  for w: Word(n)
  {Nat.add(Word.to_nat(n, Word.shl(n, w)), W.scale(W.top(n, False{}, w), W.pow2(n))) == Nat.double(Word.to_nat(n, w)) : Nat}

# LAW: padding a zero on top keeps the value
law shr_pad:
  for n: Nat
  for w: Word(n)
  {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}

# LAW: shr halves, rounding down: twice the result plus the lost bit is w
law shr_nat:
  for n: Nat
  for w: Word(n)
  {Nat.add(W.b2n(W.lsb(n, w)), Nat.double(Word.to_nat(n, Word.shr(n, w)))) == Word.to_nat(n, w) : Nat}

# LAW: comparing words is comparing their values
law cmp_nat:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

# U32
# ---

# LAW: U32.xor is commutative
law u32_xor_comm:
  for a: U32
  for b: U32
  {U32.xor(a, b) == U32.xor(b, a) : U32}

# LAW: U32.and is commutative
law u32_and_comm:
  for a: U32
  for b: U32
  {U32.and(a, b) == U32.and(b, a) : U32}

# LAW: U32.or is commutative
law u32_or_comm:
  for a: U32
  for b: U32
  {U32.or(a, b) == U32.or(b, a) : U32}

# LAW: U32.xor is associative
law u32_xor_assoc:
  for a: U32
  for b: U32
  for c: U32
  {U32.xor(a, U32.xor(b, c)) == U32.xor(U32.xor(a, b), c) : U32}

# LAW: U32.and is associative
law u32_and_assoc:
  for a: U32
  for b: U32
  for c: U32
  {U32.and(a, U32.and(b, c)) == U32.and(U32.and(a, b), c) : U32}

# LAW: U32.or is associative
law u32_or_assoc:
  for a: U32
  for b: U32
  for c: U32
  {U32.or(a, U32.or(b, c)) == U32.or(U32.or(a, b), c) : U32}

# LAW: U32.add is associative
law u32_add_assoc:
  for a: U32
  for b: U32
  for c: U32
  {U32.add(a, U32.add(b, c)) == U32.add(U32.add(a, b), c) : U32}

# LAW: 0 is the identity of U32.add and U32.xor; xor self-cancels
law u32_add_zero:
  for a: U32
  {U32.add(a, 0) == a : U32}

law u32_xor_zero:
  for a: U32
  {U32.xor(a, 0) == a : U32}

law u32_xor_self:
  for +a: U32
  {U32.xor(a, a) == 0 : U32}

# LAW: U32.not is an involution
law u32_not_not:
  for a: U32
  {U32.not(U32.not(a)) == a : U32}

# LAW: U32s with the same value are equal
law u32_to_nat_inj:
  for a: U32
  for b: U32
  for h: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

# LAW: U32 subtraction without wrap: when a = b + d, a - b is exactly d
law u32_sub_nat:
  for +a: U32
  for +b: U32
  for +d: Nat
  for h: {U32.to_nat(a) == Nat.add(U32.to_nat(b), d) : Nat}
  {U32.to_nat(U32.sub(a, b)) == d : Nat}

# LAW: U32 comparison is comparison of values
law u32_cmp_nat:
  for a: U32
  for b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

law u32_lt_nat:
  for +a: U32
  for +b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

law u32_le_nat:
  for +a: U32
  for +b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

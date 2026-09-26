# wordlib: laws of Base's fixed-width words. Word(n) is n Bools, least
# significant bit first, and U32 wraps Word(32n). Word.to_nat(n, w) is w's
# value and W.pow2(n) is 2^n, so most laws below say what an operation does
# to values.

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

# Addition
# --------

# LAW: zero is the identity of add
law add_zero:
  for n: Nat
  for a: Word(n)
  {Word.add(n, a, Word.zero(n)) == a : Word(n)}

# LAW: the adder is exact. An n-bit add with carry-in c gives a word and a
# carry-out; the word plus the carry-out's weight 2^n is the true sum
# a + b + c. With not_nat, this pins Word.add to addition mod 2^n.
law adc_nat:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {(Word.to_nat(n, Word.adc(n, a, b, False{}, c)) + W.scale(W.carry(n, a, b, c), W.pow2(n)) : Nat)
    == (Word.to_nat(n, a) + (Word.to_nat(n, b) + W.b2n(c)) : Nat) : Nat}

# LAW: a word and its complement sum to 2^n - 1. So every word's value is
# below 2^n, with the complement's value as the gap.
law not_nat:
  for n: Nat
  for w: Word(n)
  {1n+(Word.to_nat(n, w) + Word.to_nat(n, Word.not(n, w)) : Nat) == W.pow2(n) : Nat}

# LAW: words with the same value are the same word
law to_nat_inj:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

# LAW: addition without overflow: when a + b < 2^n, the word sum is exact
law add_exact:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +g: Nat
  for h: {1n+((Word.to_nat(n, a) + Word.to_nat(n, b)) + g : Nat) == W.pow2(n) : Nat}
  {Word.to_nat(n, Word.add(n, a, b)) == (Word.to_nat(n, a) + Word.to_nat(n, b) : Nat) : Nat}

# LAW: word addition is associative
law add_assoc:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  {Word.add(n, a, Word.add(n, b, c)) == Word.add(n, Word.add(n, a, b), c) : Word(n)}

# Subtraction
# -----------

# LAW: subtracting is adding the complement: Word.sub(a, b) is a + not b
# with carry-in 1, that is, a + (2^n - b) mod 2^n
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
  for h: {Word.to_nat(n, a) == (Word.to_nat(n, b) + d : Nat) : Nat}
  {Word.to_nat(n, Word.sub(n, a, b)) == d : Nat}

# Shifts
# ------

# LAW: shifting c in from below doubles the value, adds c and drops the
# top bit, whose weight is 2^n
law shl_put:
  for n: Nat
  for +c: Bool
  for +w: Word(n)
  {(Word.to_nat(n, Word.shl.put(n, c, w)) + W.scale(W.top(n, c, w), W.pow2(n)) : Nat)
    == (W.b2n(c) + Nat.double(Word.to_nat(n, w)) : Nat) : Nat}

# LAW: shl doubles, less the top bit's 2^n
law shl_nat:
  for n: Nat
  for w: Word(n)
  {(Word.to_nat(n, Word.shl(n, w)) + W.scale(W.top(n, False{}, w), W.pow2(n)) : Nat)
    == Nat.double(Word.to_nat(n, w)) : Nat}

# LAW: padding a zero on top keeps the value
law shr_pad:
  for n: Nat
  for w: Word(n)
  {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}

# LAW: shr halves, rounding down: twice the result plus the lost bit is w
law shr_nat:
  for n: Nat
  for w: Word(n)
  {(W.b2n(W.lsb(n, w)) + Nat.double(Word.to_nat(n, Word.shr(n, w))) : Nat)
    == Word.to_nat(n, w) : Nat}

# Comparison
# ----------

# LAW: comparing words is comparing their values
law cmp_nat:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

# Multiplication
# --------------

# LAW: each step of the shift-and-add multiplier keeps
# result + q * 2^n == acc + a * b, with q = mulq counting the wraps
law mul_go_nat:
  for +n: Nat
  for +m: Nat
  for +a: Word(m)
  for +b: Word(n)
  for +acc: Word(n)
  {(Word.to_nat(n, Word.mul.go(n, m, a, b, acc)) + (W.mulq(n, m, a, b, acc) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, acc) + (Word.to_nat(m, a) * Word.to_nat(n, b)) : Nat) : Nat}

# LAW: the product is a * b less some multiple of 2^n
law mul_nat:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {(Word.to_nat(n, Word.mul(n, a, b)) + (W.mulq(n, n, a, b, Word.zero(n)) * W.pow2(n)) : Nat)
    == (Word.to_nat(n, a) * Word.to_nat(n, b) : Nat) : Nat}

# LAW: multiplication without overflow: when a * b < 2^n, the product is exact
law mul_exact:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +g: Nat
  for h: {1n+((Word.to_nat(n, a) * Word.to_nat(n, b)) + g : Nat) == W.pow2(n) : Nat}
  {Word.to_nat(n, Word.mul(n, a, b)) == (Word.to_nat(n, a) * Word.to_nat(n, b) : Nat) : Nat}

# LAW: word multiplication is commutative
law mul_comm:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.mul(n, a, b) == Word.mul(n, b, a) : Word(n)}

# U32
# ---
# The laws above at n = 32, for the type Bend programs use.

# LAW: U32 xor, and and or are commutative and associative
law u32_xor_comm:
  for a: U32
  for b: U32
  {(a .^. b : U32) == (b .^. a : U32) : U32}

law u32_and_comm:
  for a: U32
  for b: U32
  {(a .&. b : U32) == (b .&. a : U32) : U32}

law u32_or_comm:
  for a: U32
  for b: U32
  {(a .|. b : U32) == (b .|. a : U32) : U32}

law u32_xor_assoc:
  for a: U32
  for b: U32
  for c: U32
  {(a .^. (b .^. c) : U32) == ((a .^. b) .^. c : U32) : U32}

law u32_and_assoc:
  for a: U32
  for b: U32
  for c: U32
  {(a .&. (b .&. c) : U32) == ((a .&. b) .&. c : U32) : U32}

law u32_or_assoc:
  for a: U32
  for b: U32
  for c: U32
  {(a .|. (b .|. c) : U32) == ((a .|. b) .|. c : U32) : U32}

# LAW: U32 addition is associative, and 0 is its identity
law u32_add_assoc:
  for a: U32
  for b: U32
  for c: U32
  {(a + (b + c) : U32) == ((a + b) + c : U32) : U32}

law u32_add_zero:
  for a: U32
  {(a + 0 : U32) == a : U32}

# LAW: U32 multiplication is commutative
law u32_mul_comm:
  for a: U32
  for b: U32
  {(a * b : U32) == (b * a : U32) : U32}

# LAW: 0 is the identity of xor, and every U32 is its own xor inverse
law u32_xor_zero:
  for a: U32
  {(a .^. 0 : U32) == a : U32}

law u32_xor_self:
  for +a: U32
  {(a .^. a : U32) == 0 : U32}

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
  for h: {U32.to_nat(a) == (U32.to_nat(b) + d : Nat) : Nat}
  {U32.to_nat((a - b : U32)) == d : Nat}

# LAW: comparing U32s is comparing their values
law u32_cmp_nat:
  for a: U32
  for b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

law u32_lt_nat:
  for +a: U32
  for +b: U32
  {(a < b : U32) == (U32.to_nat(a) < U32.to_nat(b) : Nat) : Bool}

law u32_le_nat:
  for +a: U32
  for +b: U32
  {(a <= b : U32) == (U32.to_nat(a) <= U32.to_nat(b) : Nat) : Bool}

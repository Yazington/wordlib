# word.bend: the vocabulary wordlib's laws are stated in.

import Base

# a bit as a Nat
def b2n(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# p if k, else 0n
def scale(k: Bool, p: Nat) -> Nat:
  match k:
    case False{}:
      0n
    case True{}:
      p

def pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# majority of three bits: a full adder's carry out
def maj(a: Bool, b: Bool, c: Bool) -> Bool:
  match a b c:
    case False{} False{} _:
      False{}
    case True{} True{} _:
      True{}
    case False{} True{} _:
      c
    case True{} False{} _:
      c

# the carry out of Word.adc's add: the bit an n-bit sum overflows into
def carry(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          carry(p, at, bt, maj(ab, bb, c))

# the bit Word.shl.put(n, c, w) shifts out: w's top bit, or c when n is 0
def top(n: Nat, c: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match w:
        case WCon{b, t}:
          top(p, b, t)

# the lowest bit (False for the empty word)
def lsb(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          b

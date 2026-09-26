# u32.bend: the U32 laws. A U32 is a Word(32n) inside a U32{..}, and each
# U32 operation applies its Word operation inside, so every U32 law is a
# word law at n = 32.

import Base
import ../LAWS.bend as Laws
import ./bits.bend as Bits
import ./add.bend as Add
import ./sub.bend as Sub
import ./compare.bend as Compare
import ./mul.bend as Mul

# equal words make equal U32s
def u32_eq(-x: Word(32n), -y: Word(32n), e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  %e : {U32{x} == U32{_} : U32}
  {==}

def Laws.u32_xor_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      u32_eq(Word.xor(32n, x, y), Word.xor(32n, y, x), Laws.xor_comm(32n, x, y))

def Laws.u32_and_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      u32_eq(Word.and(32n, x, y), Word.and(32n, y, x), Laws.and_comm(32n, x, y))

def Laws.u32_or_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      u32_eq(Word.or(32n, x, y), Word.or(32n, y, x), Laws.or_comm(32n, x, y))

def Laws.u32_xor_assoc(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      u32_eq(Word.xor(32n, x, Word.xor(32n, y, z)), Word.xor(32n, Word.xor(32n, x, y), z),
        Laws.xor_assoc(32n, x, y, z))

def Laws.u32_and_assoc(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      u32_eq(Word.and(32n, x, Word.and(32n, y, z)), Word.and(32n, Word.and(32n, x, y), z),
        Laws.and_assoc(32n, x, y, z))

def Laws.u32_or_assoc(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      u32_eq(Word.or(32n, x, Word.or(32n, y, z)), Word.or(32n, Word.or(32n, x, y), z),
        Laws.or_assoc(32n, x, y, z))

def Laws.u32_add_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      u32_eq(Word.add(32n, x, Word.add(32n, y, z)), Word.add(32n, Word.add(32n, x, y), z),
        Laws.add_assoc(32n, x, y, z))

def Laws.u32_add_zero(a):
  match a:
    case U32{x}:
      u32_eq(Word.add(32n, x, Word.zero(32n)), x, Laws.add_zero(32n, x))

def Laws.u32_mul_comm(a, b):
  match a b:
    case U32{+x} U32{+y}:
      u32_eq(Word.mul(32n, x, y), Word.mul(32n, y, x), Laws.mul_comm(32n, x, y))

def Laws.u32_xor_zero(a):
  match a:
    case U32{x}:
      u32_eq(Word.xor(32n, x, Word.zero(32n)), x, Laws.xor_zero(32n, x))

def Laws.u32_xor_self(a):
  match a:
    case U32{+x}:
      u32_eq(Word.xor(32n, x, x), Word.zero(32n), Laws.xor_self(32n, x))

def Laws.u32_not_not(a):
  match a:
    case U32{x}:
      u32_eq(Word.not(32n, Word.not(32n, x)), x, Laws.not_not(32n, x))

def Laws.u32_to_nat_inj(a, b, h):
  match a b:
    case U32{+x} U32{+y}:
      u32_eq(x, y, Laws.to_nat_inj(32n, x, y, h))

def Laws.u32_sub_nat(a, b, d, h):
  match a b:
    case U32{+x} U32{+y}:
      Laws.sub_nat(32n, x, y, d, h)

def Laws.u32_cmp_nat(a, b):
  match a b:
    case U32{x} U32{y}:
      Laws.cmp_nat(32n, x, y)

def Laws.u32_lt_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Cmp, Bool, o => Cmp.is_lt(o), Word.cmp(32n, x, y),
        Nat.cmp(Word.to_nat(32n, x), Word.to_nat(32n, y)), Laws.cmp_nat(32n, x, y))

def Laws.u32_le_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Cmp, Bool, o => Cmp.is_le(o), Word.cmp(32n, x, y),
        Nat.cmp(Word.to_nat(32n, x), Word.to_nat(32n, y)), Laws.cmp_nat(32n, x, y))

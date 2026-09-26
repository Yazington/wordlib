# count.bend: the vocabulary of list/'s sorting laws.

import Base

def b2n(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# what h weighs in a count: 1 when counting everything (None), else 1
# exactly when h is x
def hit(m: Maybe<&2, U32>, h: U32) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      b2n(U32.is_eq(x, h))

# how many elements of xs m picks: all of them, or the copies of x
def count(+m: Maybe<&2, U32>, xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(hit(m, h), count(m, t))

# each element is at most the next
def sorted.go(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(U32.is_le(x, h), sorted.go(t, h))

def sorted(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      sorted.go(t, h)

# Base's sort on U32, by <=
def sort(+xs: List<&2, U32>) -> List<&2, U32>:
  List.sort(~U32, ~U32.is_le, xs)

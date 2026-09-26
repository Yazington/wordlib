# compare.bend: Word.cmp compares from the top bit down, and Nat.cmp on
# values does the same: a higher part decides unless it ties, and then the
# head bits do. So one lemma per pair of head bits carries the order down.

import Base
import ../LAWS.bend as Laws

# a tie on x, y is broken by head bits 0, 0: cmp(2x, 2y)
def cmp_bits.ff(+x: Nat, +y: Nat) ->
  {Word.cmp.fin(False{}, False{}, Nat.cmp(x, y))
    == Nat.cmp(Nat.double(x), Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cmp_bits.ff(p, q)

# head bits 0, 1: cmp(2x, 2y + 1)
def cmp_bits.ft(+x: Nat, +y: Nat) ->
  {Word.cmp.fin(False{}, True{}, Nat.cmp(x, y))
    == Nat.cmp(Nat.double(x), 1n+Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cmp_bits.ft(p, q)

# head bits 1, 0: cmp(2x + 1, 2y)
def cmp_bits.tf(+x: Nat, +y: Nat) ->
  {Word.cmp.fin(True{}, False{}, Nat.cmp(x, y))
    == Nat.cmp(1n+Nat.double(x), Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cmp_bits.tf(p, q)

# head bits 1, 1: cmp(2x + 1, 2y + 1)
def cmp_bits.tt(+x: Nat, +y: Nat) ->
  {Word.cmp.fin(True{}, True{}, Nat.cmp(x, y))
    == Nat.cmp(1n+Nat.double(x), 1n+Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cmp_bits.tt(p, q)

def Laws.cmp_nat(n, a, b):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n++p WCon{False{}, +t} WCon{False{}, +u}:
      +fin = Word.cmp.fin(False{}, False{}, Word.cmp(p, t, u))
      %cmp_bits.ff(Word.to_nat(p, t), Word.to_nat(p, u)) : {fin == _ : Cmp}
      %Laws.cmp_nat(p, t, u) : {fin == Word.cmp.fin(False{}, False{}, _) : Cmp}
      {==}
    case 1n++p WCon{False{}, +t} WCon{True{}, +u}:
      +fin = Word.cmp.fin(False{}, True{}, Word.cmp(p, t, u))
      %cmp_bits.ft(Word.to_nat(p, t), Word.to_nat(p, u)) : {fin == _ : Cmp}
      %Laws.cmp_nat(p, t, u) : {fin == Word.cmp.fin(False{}, True{}, _) : Cmp}
      {==}
    case 1n++p WCon{True{}, +t} WCon{False{}, +u}:
      +fin = Word.cmp.fin(True{}, False{}, Word.cmp(p, t, u))
      %cmp_bits.tf(Word.to_nat(p, t), Word.to_nat(p, u)) : {fin == _ : Cmp}
      %Laws.cmp_nat(p, t, u) : {fin == Word.cmp.fin(True{}, False{}, _) : Cmp}
      {==}
    case 1n++p WCon{True{}, +t} WCon{True{}, +u}:
      +fin = Word.cmp.fin(True{}, True{}, Word.cmp(p, t, u))
      %cmp_bits.tt(Word.to_nat(p, t), Word.to_nat(p, u)) : {fin == _ : Cmp}
      %Laws.cmp_nat(p, t, u) : {fin == Word.cmp.fin(True{}, True{}, _) : Cmp}
      {==}

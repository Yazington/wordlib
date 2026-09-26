# shift.bend: shifts by one bit. Shifting left doubles the value and drops
# the top bit, whose weight is 2^n; shifting right halves it and drops the
# low bit.

import Base
import ../LAWS.bend as Laws
import ../word.bend as W
import ./wrap.bend as Wrap

# One bit of shl.put: c shifts in as the head, the old head b moves into
# the tail t, and the tail's law (ih, with b's value as bb) gives
#   (c + 2R) + 2 scale(K, P) == c + 2(bb + 2T)
# where R is the shifted tail, K the bit it drops, T the tail and P = 2^p.
def shl_put.bit(+c: Nat, +bb: Nat, +p: Nat, +b: Bool, +t: Word(p),
  ih: {(Word.to_nat(p, Word.shl.put(p, b, t)) + W.scale(W.top(p, b, t), W.pow2(p)) : Nat)
    == (bb + Nat.double(Word.to_nat(p, t)) : Nat) : Nat}) ->
  {((c + Nat.double(Word.to_nat(p, Word.shl.put(p, b, t))))
      + W.scale(W.top(p, b, t), Nat.double(W.pow2(p))) : Nat)
    == (c + Nat.double((bb + Nat.double(Word.to_nat(p, t)) : Nat)) : Nat) : Nat}:
  +R = Word.to_nat(p, Word.shl.put(p, b, t))
  +K = W.top(p, b, t)
  +P = W.pow2(p)
  +X = W.scale(K, P)
  +RHS = (c + Nat.double((bb + Nat.double(Word.to_nat(p, t)) : Nat)) : Nat)
  %Wrap.scale_dbl(K, P) : {((c + Nat.double(R)) + _ : Nat) == RHS : Nat}
  %Wrap.double_sum(c, R, X) : {_ == RHS : Nat}
  %Equal.sym(Nat, (R + X : Nat), (bb + Nat.double(Word.to_nat(p, t)) : Nat), ih)
    : {(c + Nat.double(_) : Nat) == RHS : Nat}
  {==}

# the four cases of the bit shifted in (c) and the head moved along (b)
def Laws.shl_put(n, c, w):
  match n c w:
    case 0n False{} WNil{}:
      {==}
    case 0n True{} WNil{}:
      {==}
    #                                       c   bb
    case 1n++p False{} WCon{False{}, +t}:
      shl_put.bit(0n, 0n, p, False{}, t, Laws.shl_put(p, False{}, t))
    case 1n++p False{} WCon{True{}, +t}:
      shl_put.bit(0n, 1n, p, True{}, t, Laws.shl_put(p, True{}, t))
    case 1n++p True{} WCon{False{}, +t}:
      shl_put.bit(1n, 0n, p, False{}, t, Laws.shl_put(p, False{}, t))
    case 1n++p True{} WCon{True{}, +t}:
      shl_put.bit(1n, 1n, p, True{}, t, Laws.shl_put(p, True{}, t))

# shl is shl.put with a 0 shifted in
def Laws.shl_nat(n, w):
  match n w:
    case 0n WNil{}:
      {==}
    case 1n++p WCon{+b, +t}:
      Laws.shl_put(1n+p, False{}, WCon{b, t})

# the padding bit is on top, where it adds nothing
def Laws.shr_pad(n, w):
  match n w:
    case 0n WNil{}:
      {==}
    case 1n++p WCon{False{}, +t}:
      Equal.cong(Nat, Nat, v => Nat.double(v),
        Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Laws.shr_pad(p, t))
    case 1n++p WCon{True{}, +t}:
      Equal.cong(Nat, Nat, v => 1n+Nat.double(v),
        Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Laws.shr_pad(p, t))

# shr drops the head bit and pads the tail: its value is the tail's
def Laws.shr_nat(n, w):
  match n w:
    case 0n WNil{}:
      {==}
    case 1n++p WCon{False{}, +t}:
      Equal.cong(Nat, Nat, v => Nat.double(v),
        Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Laws.shr_pad(p, t))
    case 1n++p WCon{True{}, +t}:
      Equal.cong(Nat, Nat, v => 1n+Nat.double(v),
        Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Laws.shr_pad(p, t))

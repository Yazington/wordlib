# withdraw: the laws. A covered withdrawal is exact (never wraps), and an
# uncovered one changes nothing.

import Base
import ./main.bend as M

# LAW: when amt <= bal, what remains plus amt is exactly bal
law covered:
  for +bal: U32
  for +amt: U32
  for +h: {U32.is_le(amt, bal) == True{} : Bool}
  {Nat.add(U32.to_nat(M.withdraw(bal, amt)), U32.to_nat(amt)) == U32.to_nat(bal) : Nat}

# LAW: when amt > bal, the balance is untouched
law uncovered:
  for +bal: U32
  for +amt: U32
  for h: {U32.is_le(amt, bal) == False{} : Bool}
  {M.withdraw(bal, amt) == bal : U32}

# withdraw: the proofs, by wordlib's U32 laws.

import Base
import ./main.bend as M
import ./LAWS.bend as Laws
import ../../LAWS.bend as WL
import ../../PROOF.bend as WP
import ../../lib/nat.bend as N

# A covered withdrawal subtracts, and the subtraction does not wrap:
# u32_le_nat turns the U32 guard into Nat order, le_sub names the gap
# d = bal - amt, and u32_sub_nat says the U32 result is exactly d.
def Laws.covered(bal, amt, h):
  +B0 = U32.to_nat(bal)
  +A0 = U32.to_nat(amt)
  +d = Nat.sub(B0, A0)
  # amt <= bal as U32s, so as Nats
  +le = Equal.trans(Bool, (A0 <= B0 : Nat), (amt <= bal : U32), True{},
    Equal.sym(Bool, (amt <= bal : U32), (A0 <= B0 : Nat), WL.u32_le_nat(amt, bal)), h)
  # bal == amt + d
  +gap = N.le_sub(A0, B0, le)
  %Equal.sym(Bool, (amt <= bal : U32), True{}, h)
    : {(U32.to_nat(M.withdraw.go(_, bal, amt)) + A0 : Nat) == B0 : Nat}
  %Equal.sym(Nat, U32.to_nat((bal - amt : U32)), d, WL.u32_sub_nat(bal, amt, d, gap))
    : {(_ + A0 : Nat) == B0 : Nat}
  %Equal.sym(Nat, B0, (A0 + d : Nat), gap) : {(d + A0 : Nat) == _ : Nat}
  N.add_comm(d, A0)

# an uncovered withdrawal returns the balance untouched
def Laws.uncovered(bal, amt, h):
  %Equal.sym(Bool, (amt <= bal : U32), False{}, h) : {M.withdraw.go(_, bal, amt) == bal : U32}
  {==}

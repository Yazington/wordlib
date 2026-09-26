# withdraw: the proofs, by wordlib's U32 laws.

import Base
import ./main.bend as M
import ./LAWS.bend as Laws
import ../../LAWS.bend as WL
import ../../PROOF.bend as WP
import ../../nat.bend as N

# a covered withdrawal subtracts, and the subtraction does not wrap:
# u32_le_nat turns the U32 guard into Nat order, le_sub names the gap
# bal - amt, and u32_sub_nat says the U32 result is exactly that gap
def Laws.covered(bal, amt, h):
  %Equal.sym(Bool, U32.is_le(amt, bal), True{}, h) : {Nat.add(U32.to_nat(M.withdraw.go(_, bal, amt)), U32.to_nat(amt)) == U32.to_nat(bal) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.sub(bal, amt)), Nat.sub(U32.to_nat(bal), U32.to_nat(amt)), WL.u32_sub_nat(bal, amt, Nat.sub(U32.to_nat(bal), U32.to_nat(amt)), N.le_sub(U32.to_nat(amt), U32.to_nat(bal), Equal.trans(Bool, Nat.is_le(U32.to_nat(amt), U32.to_nat(bal)), U32.is_le(amt, bal), True{}, Equal.sym(Bool, U32.is_le(amt, bal), Nat.is_le(U32.to_nat(amt), U32.to_nat(bal)), WL.u32_le_nat(amt, bal)), h)))) : {Nat.add(_, U32.to_nat(amt)) == U32.to_nat(bal) : Nat}
  %Equal.sym(Nat, U32.to_nat(bal), Nat.add(U32.to_nat(amt), Nat.sub(U32.to_nat(bal), U32.to_nat(amt))), N.le_sub(U32.to_nat(amt), U32.to_nat(bal), Equal.trans(Bool, Nat.is_le(U32.to_nat(amt), U32.to_nat(bal)), U32.is_le(amt, bal), True{}, Equal.sym(Bool, U32.is_le(amt, bal), Nat.is_le(U32.to_nat(amt), U32.to_nat(bal)), WL.u32_le_nat(amt, bal)), h))) : {Nat.add(Nat.sub(U32.to_nat(bal), U32.to_nat(amt)), U32.to_nat(amt)) == _ : Nat}
  N.add_comm(Nat.sub(U32.to_nat(bal), U32.to_nat(amt)), U32.to_nat(amt))

def Laws.uncovered(bal, amt, h):
  %Equal.sym(Bool, U32.is_le(amt, bal), False{}, h) : {M.withdraw.go(_, bal, amt) == bal : U32}
  {==}

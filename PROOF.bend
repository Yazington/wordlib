# wordlib: the proofs of LAWS.bend, one file per topic in proofs/.
#
#   bend PROOF.bend    prints "All terms check." once every law is proved

import Base
import ./LAWS.bend as Laws
import ./proofs/bits.bend as Bits
import ./proofs/add.bend as Add
import ./proofs/sub.bend as Sub
import ./proofs/shift.bend as Shift
import ./proofs/compare.bend as Compare
import ./proofs/mul.bend as Mul
import ./proofs/u32.bend as U32s

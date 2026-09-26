# list: the proofs of list/LAWS.bend, one file per topic in list/proofs/.
#
#   bend list/PROOF.bend    prints "All terms check." once every law is proved

import Base
import ./LAWS.bend as Laws
import ./proofs/append.bend as Append
import ./proofs/reverse.bend as Reverse
import ./proofs/index.bend as Index
import ./proofs/build.bend as Build
import ./proofs/sort.bend as Sort

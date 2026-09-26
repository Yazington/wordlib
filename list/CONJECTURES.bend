# list: claims that are tested (bendcheck's lawcheck) but not yet proved.
# A law moves to LAWS.bend when its proof lands.

import Base
import ./count.bend as C

# CONJECTURE: sort returns a sorted list
law sort_sorted:
  for +xs: +List<U32>
  {C.sorted(C.sort(xs)) == True{} : Bool}

# CONJECTURE: sorting twice changes nothing
law sort_idem:
  for +xs: +List<U32>
  {C.sort(C.sort(xs)) == C.sort(xs) : List<&2, U32>}

# CONJECTURE: sorting a sorted list changes nothing
law sort_sorted_id:
  for +xs: +List<U32>
  for h: {C.sorted(xs) == True{} : Bool}
  {C.sort(xs) == xs : List<&2, U32>}

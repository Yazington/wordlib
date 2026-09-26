# list: laws of Base's List functions, for every quantity a and element
# type A. A list is affine unless a is &2, so each law's proof may use its
# lists once; parameters that only steer the statement are erased (-).

import Base
import ./count.bend as C

# Append
# ------

# LAW: [] is a right identity of append
law append_nil:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

# LAW: append is associative
law append_assoc:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  for -zs: List<a, A>
  {List.append(a, A, List.append(a, A, xs, ys), zs)
    == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}

# LAW: lengths add under append
law length_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.length(a, A, List.append(a, A, xs, ys))
    == (List.length(a, A, xs) + List.length(a, A, ys) : Nat) : Nat}

# LAW: concat distributes over append
law concat_append:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for -yss: List<a, List<a, A>>
  {List.concat(a, A, List.append(a, List<a, A>, xss, yss))
    == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}

# Reverse
# -------

# LAW: reverse's loop reverses onto its accumulator
law reverse_go:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -acc: List<a, A>
  {List.reverse.go(a, A, xs, acc) == List.append(a, A, List.reverse(a, A, xs), acc) : List<a, A>}

# LAW: reversing an append swaps the parts
law reverse_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.reverse(a, A, List.append(a, A, xs, ys))
    == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}

# LAW: reverse is an involution
law reverse_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.reverse(a, A, List.reverse(a, A, xs)) == xs : List<a, A>}

# LAW: reverse keeps the length
law length_reverse:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.length(a, A, List.reverse(a, A, xs)) == List.length(a, A, xs) : Nat}

# Take, drop, set, get
# --------------------

# LAW: take and drop split a list
law take_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.append(a, A, List.take(a, A, xs, n), List.drop(a, A, xs, n)) == xs : List<a, A>}

# LAW: take keeps min(n, length) elements
law length_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.take(a, A, xs, n)) == Nat.min(n, List.length(a, A, xs)) : Nat}

# LAW: drop keeps length - n elements
law length_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.drop(a, A, xs, n)) == Nat.sub(List.length(a, A, xs), n) : Nat}

# LAW: set keeps the length
law length_set:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for x: A
  {List.length(a, A, List.set(a, A, xs, n, x)) == List.length(a, A, xs) : Nat}

# LAW: reading back an index just set gives the new value
law get_set:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for x: A
  for h: {Nat.is_lt(n, List.length(a, A, xs)) == True{} : Bool}
  {List.get(a, A, List.set(a, A, xs, n, x), n) == Some{x} : Maybe<a, A>}

# Building lists
# --------------

# LAW: zip is as long as the shorter list
law length_zip:
  for -a: Quant
  for -A: Kind(a)
  for -b: Quant
  for -B: Kind(b)
  for xs: List<a, A>
  for ys: List<b, B>
  {List.length(&1, A & B, List.zip(a, A, b, B, xs, ys))
    == Nat.min(List.length(a, A, xs), List.length(b, B, ys)) : Nat}

# LAW: range n has n elements
law length_range:
  for +n: Nat
  {List.length(&2, Nat, List.range(n)) == n : Nat}

# LAW: replicate n x has n elements
law length_replicate:
  for -A: Data
  for n: Nat
  for +x: A
  {List.length(&2, A, List.replicate(A, n, x)) == n : Nat}

# Sorting (U32, by <=)
# --------------------
# count(Some{x}, xs) counts the copies of x; count(None{}, xs) counts all.

# LAW: counts add under append
law count_append:
  for +m: Maybe<&2, U32>
  for +xs: +List<U32>
  for +ys: +List<U32>
  {C.count(m, List.append(&2, U32, xs, ys)) == (C.count(m, xs) + C.count(m, ys) : Nat) : Nat}

# LAW: reverse's loop moves every element, keeping counts
law count_reverse_go:
  for +m: Maybe<&2, U32>
  for +xs: +List<U32>
  for +acc: +List<U32>
  {C.count(m, List.reverse.go(&2, U32, xs, acc)) == (C.count(m, xs) + C.count(m, acc) : Nat) : Nat}

# LAW: a merge keeps the counts of its accumulator and inputs, however
# much fuel it has
law merge_count:
  for +m: Maybe<&2, U32>
  for +fuel: Nat
  for +acc: +List<U32>
  for +xs: +List<U32>
  for +ys: +List<U32>
  {C.count(m, List.merge.go(~U32, ~U32.is_le, fuel, (acc, xs, ys)))
    == (C.count(m, acc) + (C.count(m, xs) + C.count(m, ys)) : Nat) : Nat}

# LAW: a merge pass keeps the counts of all runs together
law pass_count:
  for +m: Maybe<&2, U32>
  for +n: Nat
  for +runs: List<&2, List<&2, U32>>
  {C.count(m, List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, runs)))
    == C.count(m, List.concat(&2, U32, runs)) : Nat}

# LAW: the pass loop keeps the counts too
law sort_go_count:
  for +m: Maybe<&2, U32>
  for +fuel: Nat
  for +n: Nat
  for +runs: List<&2, List<&2, U32>>
  {C.count(m, List.sort.go(~U32, ~U32.is_le, fuel, n, runs))
    == C.count(m, List.concat(&2, U32, runs)) : Nat}

# LAW: splitting into runs and flattening gives the list back
law sort_runs:
  for -A: Data
  for xs: List<&2, A>
  {List.concat(&2, A, List.sort.runs(A, xs)) == xs : List<&2, A>}

# LAW: counting everything is the length
law count_all:
  for +xs: +List<U32>
  {C.count(None{}, xs) == List.length(&2, U32, xs) : Nat}

# LAW: sorting keeps every count
law sort_count:
  for +m: Maybe<&2, U32>
  for +xs: +List<U32>
  {C.count(m, C.sort(xs)) == C.count(m, xs) : Nat}

# LAW: sort is a permutation: each value occurs as often after as before
law sort_perm:
  for +x: U32
  for +xs: +List<U32>
  {C.count(Some{x}, C.sort(xs)) == C.count(Some{x}, xs) : Nat}

# LAW: sort keeps the length
law sort_length:
  for +xs: +List<U32>
  {List.length(&2, U32, C.sort(xs)) == List.length(&2, U32, xs) : Nat}

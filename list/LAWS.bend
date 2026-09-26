# list: laws of Base's List functions, for every quantity a and element
# type A. A list is affine unless a is &2, so each law's proof may use its
# lists once; parameters that only steer the statement are erased (-).

import Base

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
  {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}

# LAW: lengths add under append
law length_append:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for -ys: List<a, A>
  {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

# LAW: concat distributes over append
law concat_append:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for -yss: List<a, List<a, A>>
  {List.concat(a, A, List.append(a, List<a, A>, xss, yss)) == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}

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
  {List.reverse(a, A, List.append(a, A, xs, ys)) == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}

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
  {List.length(&1, A & B, List.zip(a, A, b, B, xs, ys)) == Nat.min(List.length(a, A, xs), List.length(b, B, ys)) : Nat}

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

# reverse.bend: reverse and its loop. A list of arbitrary elements is
# affine, so a proof may use it once: each helper carries what a second
# lemma call would need in an accumulator instead.

import Base
import ../LAWS.bend as Laws
import ../../lib/nat.bend as N
import ./append.bend as Append

# reverse's loop is associative in its accumulator:
#   go(xs, acc1 ++ acc2) == go(xs, acc1) ++ acc2
def rev_acc(a, -A: Kind(a), xs: List<a, A>, -acc1: List<a, A>, -acc2: List<a, A>) ->
  {List.reverse.go(a, A, xs, List.append(a, A, acc1, acc2))
    == List.append(a, A, List.reverse.go(a, A, xs, acc1), acc2) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_acc(a, A, t, h <> acc1, acc2)

def Laws.reverse_go(a, A, xs, acc):
  rev_acc(a, A, xs, Nil{}, acc)

# reversing an append onto acc: go(xs ++ ys, acc) == go(ys, go(xs, acc))
def rev_app(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -acc: List<a, A>) ->
  {List.reverse.go(a, A, List.append(a, A, xs, ys), acc)
    == List.reverse.go(a, A, ys, List.reverse.go(a, A, xs, acc)) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_app(a, A, t, ys, h <> acc)

def Laws.reverse_append(a, A, xs, ys):
  -rx = List.reverse(a, A, xs)
  Equal.trans(List<a, A>, List.reverse(a, A, List.append(a, A, xs, ys)),
    List.reverse.go(a, A, ys, rx), List.append(a, A, List.reverse(a, A, ys), rx),
    rev_app(a, A, xs, ys, Nil{}), Laws.reverse_go(a, A, ys, rx))

# reversing twice hands the accumulator back in front:
#   go(go(xs, acc), []) == go(acc, xs)
def rev_rev(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>) ->
  {List.reverse.go(a, A, List.reverse.go(a, A, xs, acc), Nil{})
    == List.reverse.go(a, A, acc, xs) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_rev(a, A, t, h <> acc)

def Laws.reverse_reverse(a, A, xs):
  rev_rev(a, A, xs, Nil{})

# length(go(xs, acc)) == k + length(xs), given length(acc) == k. The
# accumulator's length rides along as the Nat k, so the proof never
# measures acc (erased) or the tail (spent on the recursion) again.
def len_rev(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>, +k: Nat,
  e: {List.length(a, A, acc) == k : Nat}) ->
  {List.length(a, A, List.reverse.go(a, A, xs, acc)) == (k + List.length(a, A, xs) : Nat) : Nat}:
  match xs:
    case Nil{}:
      Equal.trans(Nat, List.length(a, A, acc), k, (k + 0n : Nat), e, N.add_zero(k))
    case h <> t:
      %N.add_succ(k, List.length(a, A, t))
        : {List.length(a, A, List.reverse.go(a, A, t, h <> acc)) == _ : Nat}
      len_rev(a, A, t, h <> acc, 1n+k,
        Equal.cong(Nat, Nat, n => 1n+n, List.length(a, A, acc), k, e))

def Laws.length_reverse(a, A, xs):
  len_rev(a, A, xs, Nil{}, 0n, {==})

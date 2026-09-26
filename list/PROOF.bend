# list: the proofs. Each statement is shaped so its proof uses the list it
# recurses on once: helpers carry accumulators or counters instead of
# calling a second lemma on the same list.

import Base
import ./LAWS.bend as Laws
import ../nat.bend as N

# Append
# ------

def Laws.append_nil(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.append_nil(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

def Laws.append_assoc(a, A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.append_assoc(a, A, t, ys, zs) : {h <> List.append(a, A, List.append(a, A, t, ys), zs) == h <> _ : List<a, A>}
      {==}

def Laws.length_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.length_append(a, A, t, ys) : {1n+List.length(a, A, List.append(a, A, t, ys)) == 1n+_ : Nat}
      {==}

def Laws.concat_append(a, A, xss, yss):
  match xss:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(List<a, A>,
        List.append(a, A, List.append(a, A, h, List.concat(a, A, t)), List.concat(a, A, yss)),
        List.append(a, A, h, List.append(a, A, List.concat(a, A, t), List.concat(a, A, yss))),
        Laws.append_assoc(a, A, h, List.concat(a, A, t), List.concat(a, A, yss)))
        : {List.append(a, A, h, List.concat(a, A, List.append(a, List<a, A>, t, yss))) == _ : List<a, A>}
      %Laws.concat_append(a, A, t, yss) : {List.append(a, A, h, List.concat(a, A, List.append(a, List<a, A>, t, yss))) == List.append(a, A, h, _) : List<a, A>}
      {==}

# Reverse
# -------

# reverse's loop is associative in its accumulator
def rev_acc(a, -A: Kind(a), xs: List<a, A>, -acc1: List<a, A>, -acc2: List<a, A>) ->
  {List.reverse.go(a, A, xs, List.append(a, A, acc1, acc2)) == List.append(a, A, List.reverse.go(a, A, xs, acc1), acc2) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_acc(a, A, t, h <> acc1, acc2)

def Laws.reverse_go(a, A, xs, acc):
  rev_acc(a, A, xs, Nil{}, acc)

# reversing an append onto acc: the first part goes on first
def rev_app(a, -A: Kind(a), xs: List<a, A>, -ys: List<a, A>, -acc: List<a, A>) ->
  {List.reverse.go(a, A, List.append(a, A, xs, ys), acc) == List.reverse.go(a, A, ys, List.reverse.go(a, A, xs, acc)) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_app(a, A, t, ys, h <> acc)

def Laws.reverse_append(a, A, xs, ys):
  Equal.trans(List<a, A>,
    List.reverse(a, A, List.append(a, A, xs, ys)),
    List.reverse.go(a, A, ys, List.reverse(a, A, xs)),
    List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)),
    rev_app(a, A, xs, ys, Nil{}),
    Laws.reverse_go(a, A, ys, List.reverse(a, A, xs)))

# reversing twice hands the accumulator back in front
def rev_rev(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>) ->
  {List.reverse.go(a, A, List.reverse.go(a, A, xs, acc), Nil{}) == List.reverse.go(a, A, acc, xs) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      rev_rev(a, A, t, h <> acc)

def Laws.reverse_reverse(a, A, xs):
  rev_rev(a, A, xs, Nil{})

# the accumulator's length rides along as a Nat k, so the proof never
# measures acc (erased) or t (spent on the recursion) a second time
def len_rev(a, -A: Kind(a), xs: List<a, A>, -acc: List<a, A>, +k: Nat, e: {List.length(a, A, acc) == k : Nat}) ->
  {List.length(a, A, List.reverse.go(a, A, xs, acc)) == Nat.add(k, List.length(a, A, xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.trans(Nat, List.length(a, A, acc), k, Nat.add(k, 0n), e, N.add_zero(k))
    case h <> t:
      %N.add_succ(k, List.length(a, A, t)) : {List.length(a, A, List.reverse.go(a, A, t, h <> acc)) == _ : Nat}
      len_rev(a, A, t, h <> acc, 1n+k, Equal.cong(Nat, Nat, n => 1n+n, List.length(a, A, acc), k, e))

def Laws.length_reverse(a, A, xs):
  len_rev(a, A, xs, Nil{}, 0n, {==})

# Take, drop, set, get
# --------------------

def Laws.take_drop(a, A, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %Laws.take_drop(a, A, t, p) : {h <> List.append(a, A, List.take(a, A, t, p), List.drop(a, A, t, p)) == h <> _ : List<a, A>}
      {==}

def Laws.length_take(a, A, xs, n):
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %Laws.length_take(a, A, t, p) : {1n+List.length(a, A, List.take(a, A, t, p)) == 1n+_ : Nat}
      {==}

def Laws.length_drop(a, A, xs, n):
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      Laws.length_drop(a, A, t, p)

def Laws.length_set(a, A, xs, n, x):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %Laws.length_set(a, A, t, p, x) : {1n+List.length(a, A, List.set(a, A, t, p, x)) == 1n+_ : Nat}
      {==}

def Laws.get_set(a, A, xs, n, x, h):
  match xs n:
    case Nil{} 0n:
      Empty.absurd({List.get(a, A, List.set(a, A, Nil{}, 0n, x), 0n) == Some{x} : Maybe<a, A>}, N.false_ne_true(h))
    case Nil{} 1n+p:
      Empty.absurd({List.get(a, A, List.set(a, A, Nil{}, 1n+p, x), 1n+p) == Some{x} : Maybe<a, A>}, N.false_ne_true(h))
    case y <> t 0n:
      {==}
    case y <> t 1n+p:
      Laws.get_set(a, A, t, p, x, h)

# Building lists
# --------------

def Laws.length_zip(a, A, b, B, xs, ys):
  match xs ys:
    case Nil{} _:
      {==}
    case h <> t Nil{}:
      {==}
    case x <> xt y <> yt:
      %Laws.length_zip(a, A, b, B, xt, yt) : {1n+List.length(&1, A & B, List.zip(a, A, b, B, xt, yt)) == 1n+_ : Nat}
      {==}

# range's loop counts its accumulator in
def range_go(+n: Nat, +acc: List<&2, Nat>) -> {List.length(&2, Nat, List.range.go(n, acc)) == Nat.add(n, List.length(&2, Nat, acc)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, 1n+Nat.add(p, List.length(&2, Nat, acc)), Nat.add(p, 1n+List.length(&2, Nat, acc)), N.add_succ(p, List.length(&2, Nat, acc)))
        : {List.length(&2, Nat, List.range.go(p, p <> acc)) == _ : Nat}
      range_go(p, p <> acc)

def Laws.length_range(n):
  Equal.trans(Nat, List.length(&2, Nat, List.range(n)), Nat.add(n, 0n), n,
    range_go(n, Nil{}), Equal.sym(Nat, n, Nat.add(n, 0n), N.add_zero(n)))

def Laws.length_replicate(A, n, x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.length_replicate(A, p, x) : {1n+List.length(&2, A, List.replicate(A, p, x)) == 1n+_ : Nat}
      {==}

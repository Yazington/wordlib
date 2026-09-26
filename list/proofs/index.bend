# index.bend: take, drop, set and get, by induction on the list and the
# index together.

import Base
import ../LAWS.bend as Laws
import ../../lib/nat.bend as N

def Laws.take_drop(a, A, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      -L = List.append(a, A, List.take(a, A, t, p), List.drop(a, A, t, p))
      %Laws.take_drop(a, A, t, p) : {h <> L == h <> _ : List<a, A>}
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
      %Laws.length_set(a, A, t, p, x)
        : {1n+List.length(a, A, List.set(a, A, t, p, x)) == 1n+_ : Nat}
      {==}

# an index past the end contradicts the bound
def Laws.get_set(a, A, xs, n, x, h):
  match xs n:
    case Nil{} 0n:
      Empty.absurd({List.get(a, A, Nil{}, 0n) == Some{x} : Maybe<a, A>}, N.false_ne_true(h))
    case Nil{} 1n+p:
      Empty.absurd({List.get(a, A, Nil{}, 1n+p) == Some{x} : Maybe<a, A>}, N.false_ne_true(h))
    case y <> t 0n:
      {==}
    case y <> t 1n+p:
      Laws.get_set(a, A, t, p, x, h)

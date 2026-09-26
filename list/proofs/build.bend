# build.bend: lists built by zip, range and replicate have the lengths
# their arguments say.

import Base
import ../LAWS.bend as Laws
import ../../lib/nat.bend as N

def Laws.length_zip(a, A, b, B, xs, ys):
  match xs ys:
    case Nil{} _:
      {==}
    case h <> t Nil{}:
      {==}
    case x <> xt y <> yt:
      %Laws.length_zip(a, A, b, B, xt, yt)
        : {1n+List.length(&1, A & B, List.zip(a, A, b, B, xt, yt)) == 1n+_ : Nat}
      {==}

# range's loop counts its accumulator in: length(go(n, acc)) == n + length(acc)
def range_go(+n: Nat, +acc: List<&2, Nat>) ->
  {List.length(&2, Nat, List.range.go(n, acc)) == (n + List.length(&2, Nat, acc) : Nat) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      +k = List.length(&2, Nat, acc)
      %Equal.sym(Nat, 1n+(p + k : Nat), (p + 1n+k : Nat), N.add_succ(p, k))
        : {List.length(&2, Nat, List.range.go(p, p <> acc)) == _ : Nat}
      range_go(p, p <> acc)

def Laws.length_range(n):
  Equal.trans(Nat, List.length(&2, Nat, List.range(n)), (n + 0n : Nat), n,
    range_go(n, Nil{}), Equal.sym(Nat, n, (n + 0n : Nat), N.add_zero(n)))

def Laws.length_replicate(A, n, x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.length_replicate(A, p, x)
        : {1n+List.length(&2, A, List.replicate(A, p, x)) == 1n+_ : Nat}
      {==}

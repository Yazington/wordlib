# list: the proofs. Each statement is shaped so its proof uses the list it
# recurses on once: helpers carry accumulators or counters instead of
# calling a second lemma on the same list.

import Base
import ./LAWS.bend as Laws
import ../nat.bend as N
import ../ac.bend as A
import ./count.bend as C

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

# Sorting (U32, by <=)
# --------------------

def Laws.count_append(m, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %N.add_assoc(C.hit(m, h), C.count(m, t), C.count(m, ys)) : {Nat.add(C.hit(m, h), C.count(m, List.append(&2, U32, t, ys))) == _ : Nat}
      %Laws.count_append(m, t, ys) : {Nat.add(C.hit(m, h), C.count(m, List.append(&2, U32, t, ys))) == Nat.add(C.hit(m, h), _) : Nat}
      {==}

def Laws.count_reverse_go(m, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %A.ac([C.count(m, t), C.hit(m, h), C.count(m, acc)], A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}, A.EAdd{A.EAdd{A.EAtom{1n}, A.EAtom{0n}}, A.EAtom{2n}}, {==}) : {C.count(m, List.reverse.go(&2, U32, t, h <> acc)) == _ : Nat}
      Laws.count_reverse_go(m, t, h <> acc)

# one merge step moves one element to the accumulator, whichever way the
# comparison goes; both outcomes' induction hypotheses come in, and the
# comparison picks one
def merge_step(b: Bool, +m: Maybe<&2, U32>, +f: Nat, +acc: +List<U32>, +x: U32, +xt: +List<U32>, +y: U32, +yt: +List<U32>,
  ih_gt: {C.count(m, List.merge.go(~U32, ~U32.is_le, f, (y <> acc, x <> xt, yt))) == Nat.add(C.count(m, y <> acc), Nat.add(C.count(m, x <> xt), C.count(m, yt))) : Nat},
  ih_le: {C.count(m, List.merge.go(~U32, ~U32.is_le, f, (x <> acc, xt, y <> yt))) == Nat.add(C.count(m, x <> acc), Nat.add(C.count(m, xt), C.count(m, y <> yt))) : Nat}) ->
  {C.count(m, List.merge.go(~U32, ~U32.is_le, f, List.merge.step(U32, acc, x, xt, y, yt, b))) == Nat.add(C.count(m, acc), Nat.add(C.count(m, x <> xt), C.count(m, y <> yt))) : Nat}:
  match b:
    case False{}:
      Equal.trans(Nat, C.count(m, List.merge.go(~U32, ~U32.is_le, f, (y <> acc, x <> xt, yt))), Nat.add(C.count(m, y <> acc), Nat.add(C.count(m, x <> xt), C.count(m, yt))), Nat.add(C.count(m, acc), Nat.add(C.count(m, x <> xt), C.count(m, y <> yt))), ih_gt,
        A.ac([C.hit(m, y), C.count(m, acc), C.hit(m, x), C.count(m, xt), C.count(m, yt)],
          A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAdd{A.EAdd{A.EAtom{2n}, A.EAtom{3n}}, A.EAtom{4n}}},
          A.EAdd{A.EAtom{1n}, A.EAdd{A.EAdd{A.EAtom{2n}, A.EAtom{3n}}, A.EAdd{A.EAtom{0n}, A.EAtom{4n}}}}, {==}))
    case True{}:
      Equal.trans(Nat, C.count(m, List.merge.go(~U32, ~U32.is_le, f, (x <> acc, xt, y <> yt))), Nat.add(C.count(m, x <> acc), Nat.add(C.count(m, xt), C.count(m, y <> yt))), Nat.add(C.count(m, acc), Nat.add(C.count(m, x <> xt), C.count(m, y <> yt))), ih_le,
        A.ac([C.hit(m, x), C.count(m, acc), C.count(m, xt), C.hit(m, y), C.count(m, yt)],
          A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAdd{A.EAtom{2n}, A.EAdd{A.EAtom{3n}, A.EAtom{4n}}}},
          A.EAdd{A.EAtom{1n}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{2n}}, A.EAdd{A.EAtom{3n}, A.EAtom{4n}}}}, {==}))

def Laws.merge_count(m, fuel, acc, xs, ys):
  match fuel:
    case 0n:
      Equal.trans(Nat, C.count(m, List.reverse.go(&2, U32, acc, List.append(&2, U32, xs, ys))),
        Nat.add(C.count(m, acc), C.count(m, List.append(&2, U32, xs, ys))),
        Nat.add(C.count(m, acc), Nat.add(C.count(m, xs), C.count(m, ys))),
        Laws.count_reverse_go(m, acc, List.append(&2, U32, xs, ys)),
        Equal.cong(Nat, Nat, z => Nat.add(C.count(m, acc), z), C.count(m, List.append(&2, U32, xs, ys)), Nat.add(C.count(m, xs), C.count(m, ys)),
          Laws.count_append(m, xs, ys)))
    case 1n++f:
      match xs ys:
        case Nil{} Nil{}:
          Laws.count_reverse_go(m, acc, Nil{})
        case Nil{} +y <> yt:
          Laws.count_reverse_go(m, acc, y <> yt)
        case +x <> xt Nil{}:
          Equal.trans(Nat, C.count(m, List.reverse.go(&2, U32, acc, x <> xt)), Nat.add(C.count(m, acc), C.count(m, x <> xt)),
            Nat.add(C.count(m, acc), Nat.add(C.count(m, x <> xt), 0n)),
            Laws.count_reverse_go(m, acc, x <> xt),
            Equal.cong(Nat, Nat, z => Nat.add(C.count(m, acc), z), C.count(m, x <> xt), Nat.add(C.count(m, x <> xt), 0n), N.add_zero(C.count(m, x <> xt))))
        case +x <> +xt +y <> +yt:
          merge_step(U32.is_le(x, y), m, f, acc, x, xt, y, yt,
            Laws.merge_count(m, f, y <> acc, x <> xt, yt),
            Laws.merge_count(m, f, x <> acc, xt, y <> yt))

def Laws.pass_count(m, n, runs):
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      {==}
    case +r1 <> +r2 <> rest:
      %Equal.sym(Nat, C.count(m, List.append(&2, U32, List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2)), List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, rest)))), Nat.add(C.count(m, List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2))), C.count(m, List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, rest)))), Laws.count_append(m, List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2)), List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, rest)))) : {_ == C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, List.concat(&2, U32, rest)))) : Nat}
      %Equal.sym(Nat, C.count(m, List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2))), Nat.add(C.count(m, Nil{}), Nat.add(C.count(m, r1), C.count(m, r2))), Laws.merge_count(m, n, Nil{}, r1, r2)) : {Nat.add(_, C.count(m, List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, rest)))) == C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, List.concat(&2, U32, rest)))) : Nat}
      %Equal.sym(Nat, C.count(m, List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, rest))), C.count(m, List.concat(&2, U32, rest)), Laws.pass_count(m, n, rest)) : {Nat.add(Nat.add(C.count(m, Nil{}), Nat.add(C.count(m, r1), C.count(m, r2))), _) == C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, List.concat(&2, U32, rest)))) : Nat}
      %Equal.sym(Nat, C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, List.concat(&2, U32, rest)))), Nat.add(C.count(m, r1), C.count(m, List.append(&2, U32, r2, List.concat(&2, U32, rest)))), Laws.count_append(m, r1, List.append(&2, U32, r2, List.concat(&2, U32, rest)))) : {Nat.add(Nat.add(C.count(m, Nil{}), Nat.add(C.count(m, r1), C.count(m, r2))), C.count(m, List.concat(&2, U32, rest))) == _ : Nat}
      %Equal.sym(Nat, C.count(m, List.append(&2, U32, r2, List.concat(&2, U32, rest))), Nat.add(C.count(m, r2), C.count(m, List.concat(&2, U32, rest))), Laws.count_append(m, r2, List.concat(&2, U32, rest))) : {Nat.add(Nat.add(C.count(m, Nil{}), Nat.add(C.count(m, r1), C.count(m, r2))), C.count(m, List.concat(&2, U32, rest))) == Nat.add(C.count(m, r1), _) : Nat}
      Equal.sym(Nat, Nat.add(C.count(m, r1), Nat.add(C.count(m, r2), C.count(m, List.concat(&2, U32, rest)))), Nat.add(Nat.add(C.count(m, r1), C.count(m, r2)), C.count(m, List.concat(&2, U32, rest))), N.add_assoc(C.count(m, r1), C.count(m, r2), C.count(m, List.concat(&2, U32, rest))))

def Laws.sort_go_count(m, fuel, n, runs):
  match fuel:
    case 0n:
      {==}
    case 1n++f:
      match runs:
        case Nil{}:
          {==}
        case +r <> Nil{}:
          %Equal.sym(List<&2, U32>, List.append(&2, U32, r, Nil{}), r, Laws.append_nil(&2, U32, r)) : {C.count(m, r) == C.count(m, _) : Nat}
          {==}
        case +r1 <> +r2 <> rest:
          Equal.trans(Nat,
            C.count(m, List.sort.go(~U32, ~U32.is_le, f, n, List.sort.pass(~U32, ~U32.is_le, n, r1 <> r2 <> rest))),
            C.count(m, List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, r1 <> r2 <> rest))),
            C.count(m, List.concat(&2, U32, r1 <> r2 <> rest)),
            Laws.sort_go_count(m, f, n, List.sort.pass(~U32, ~U32.is_le, n, r1 <> r2 <> rest)),
            Laws.pass_count(m, n, r1 <> r2 <> rest))

def Laws.sort_runs(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.sort_runs(A, t) : {h <> List.concat(&2, A, List.sort.runs(A, t)) == h <> _ : List<&2, A>}
      {==}

def Laws.count_all(xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.count_all(t) : {1n+C.count(None{}, t) == 1n+_ : Nat}
      {==}

def Laws.sort_count(m, xs):
  Equal.trans(Nat,
    C.count(m, List.sort.go(~U32, ~U32.is_le, List.length(&2, U32, xs), List.length(&2, U32, xs), List.sort.runs(U32, xs))),
    C.count(m, List.concat(&2, U32, List.sort.runs(U32, xs))),
    C.count(m, xs),
    Laws.sort_go_count(m, List.length(&2, U32, xs), List.length(&2, U32, xs), List.sort.runs(U32, xs)),
    Equal.cong(List<&2, U32>, Nat, z => C.count(m, z), List.concat(&2, U32, List.sort.runs(U32, xs)), xs, Laws.sort_runs(U32, xs)))

def Laws.sort_perm(x, xs):
  Laws.sort_count(Some{x}, xs)

def Laws.sort_length(xs):
  Equal.trans(Nat, List.length(&2, U32, C.sort(xs)), C.count(None{}, C.sort(xs)), List.length(&2, U32, xs),
    Equal.sym(Nat, C.count(None{}, C.sort(xs)), List.length(&2, U32, C.sort(xs)), Laws.count_all(C.sort(xs))),
    Equal.trans(Nat, C.count(None{}, C.sort(xs)), C.count(None{}, xs), List.length(&2, U32, xs),
      Laws.sort_count(None{}, xs), Laws.count_all(xs)))

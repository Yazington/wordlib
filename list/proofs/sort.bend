# sort.bend: Base's merge sort keeps every element. count(m, xs) counts the
# copies of x (m = Some{x}) or every element (m = None{}). Each stage of
# the sort keeps the counts: a merge moves elements from its inputs to its
# accumulator, a pass merges the runs in pairs, the pass loop repeats
# passes, and splitting into runs loses nothing. None of it depends on the
# fuel.

import Base
import ../LAWS.bend as Laws
import ../count.bend as C
import ../../lib/nat.bend as N
import ../../lib/ac.bend as A
import ./append.bend as Append

# the count of a merge's result, and of its state (acc, xs, ys)
def merged(+m: Maybe<&2, U32>, f: Nat, acc: +List<U32>, xs: +List<U32>, ys: +List<U32>) -> Nat:
  C.count(m, List.merge.go(~U32, ~U32.is_le, f, (acc, xs, ys)))

def parts(+m: Maybe<&2, U32>, acc: +List<U32>, xs: +List<U32>, ys: +List<U32>) -> Nat:
  (C.count(m, acc) + (C.count(m, xs) + C.count(m, ys)) : Nat)

# count(h :: t ++ ys) == hit(h) + (count t + count ys)
def Laws.count_append(m, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +H = C.hit(m, h)
      +L = (H + C.count(m, List.append(&2, U32, t, ys)) : Nat)
      %N.add_assoc(H, C.count(m, t), C.count(m, ys)) : {L == _ : Nat}
      %Laws.count_append(m, t, ys) : {L == (H + _ : Nat) : Nat}
      {==}

# reverse's loop moves h onto the accumulator
def Laws.count_reverse_go(m, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +T = C.count(m, t)
      +H = C.hit(m, h)
      +Z = C.count(m, acc)
      # (H + T) + Z == T + (H + Z)
      %A.ac([T, H, Z],
        A.add(A.x0(), A.add(A.x1(), A.x2())), A.add(A.add(A.x1(), A.x0()), A.x2()), {==})
        : {C.count(m, List.reverse.go(&2, U32, t, h <> acc)) == _ : Nat}
      Laws.count_reverse_go(m, t, h <> acc)

# One merge step moves a head to the accumulator. Which head depends on a
# comparison the proof cannot evaluate, so both outcomes' induction
# hypotheses come in (the fuel and the lists are reusable), and the
# comparison b picks one.
def merge_step(b: Bool, +m: Maybe<&2, U32>, +f: Nat, +acc: +List<U32>,
  +x: U32, +xt: +List<U32>, +y: U32, +yt: +List<U32>,
  ih_gt: {merged(m, f, y <> acc, x <> xt, yt) == parts(m, y <> acc, x <> xt, yt) : Nat},
  ih_le: {merged(m, f, x <> acc, xt, y <> yt) == parts(m, x <> acc, xt, y <> yt) : Nat}) ->
  {C.count(m, List.merge.go(~U32, ~U32.is_le, f, List.merge.step(U32, acc, x, xt, y, yt, b)))
    == parts(m, acc, x <> xt, y <> yt) : Nat}:
  match b:
    case False{}:
      +HX = C.hit(m, x)
      +HY = C.hit(m, y)
      # (HY + ACC) + ((HX + XT) + YT) == ACC + ((HX + XT) + (HY + YT))
      Equal.trans(Nat, merged(m, f, y <> acc, x <> xt, yt), parts(m, y <> acc, x <> xt, yt),
        parts(m, acc, x <> xt, y <> yt), ih_gt,
        A.ac([HY, C.count(m, acc), HX, C.count(m, xt), C.count(m, yt)],
          A.add(A.add(A.x0(), A.x1()), A.add(A.add(A.x2(), A.x3()), A.x4())),
          A.add(A.x1(), A.add(A.add(A.x2(), A.x3()), A.add(A.x0(), A.x4()))), {==}))
    case True{}:
      +HX = C.hit(m, x)
      +HY = C.hit(m, y)
      # (HX + ACC) + (XT + (HY + YT)) == ACC + ((HX + XT) + (HY + YT))
      Equal.trans(Nat, merged(m, f, x <> acc, xt, y <> yt), parts(m, x <> acc, xt, y <> yt),
        parts(m, acc, x <> xt, y <> yt), ih_le,
        A.ac([HX, C.count(m, acc), C.count(m, xt), HY, C.count(m, yt)],
          A.add(A.add(A.x0(), A.x1()), A.add(A.x2(), A.add(A.x3(), A.x4()))),
          A.add(A.x1(), A.add(A.add(A.x0(), A.x2()), A.add(A.x3(), A.x4()))), {==}))

# Out of fuel, the merge flushes acc, xs and ys; otherwise it steps.
def Laws.merge_count(m, fuel, acc, xs, ys):
  match fuel xs ys:
    case 0n _ _:
      +zs = List.append(&2, U32, xs, ys)
      +ACC = C.count(m, acc)
      Equal.trans(Nat, C.count(m, List.reverse.go(&2, U32, acc, zs)), (ACC + C.count(m, zs) : Nat),
        parts(m, acc, xs, ys), Laws.count_reverse_go(m, acc, zs),
        Equal.cong(Nat, Nat, z => (ACC + z : Nat), C.count(m, zs),
          (C.count(m, xs) + C.count(m, ys) : Nat), Laws.count_append(m, xs, ys)))
    case 1n++f Nil{} Nil{}:
      Laws.count_reverse_go(m, acc, Nil{})
    case 1n++f Nil{} +y <> yt:
      Laws.count_reverse_go(m, acc, y <> yt)
    case 1n++f +x <> xt Nil{}:
      +ACC = C.count(m, acc)
      +X = C.count(m, x <> xt)
      Equal.trans(Nat, C.count(m, List.reverse.go(&2, U32, acc, x <> xt)), (ACC + X : Nat),
        (ACC + (X + 0n) : Nat), Laws.count_reverse_go(m, acc, x <> xt),
        Equal.cong(Nat, Nat, z => (ACC + z : Nat), X, (X + 0n : Nat), N.add_zero(X)))
    case 1n++f +x <> +xt +y <> +yt:
      merge_step(U32.is_le(x, y), m, f, acc, x, xt, y, yt,
        Laws.merge_count(m, f, y <> acc, x <> xt, yt),
        Laws.merge_count(m, f, x <> acc, xt, y <> yt))

# count(r1 ++ (r2 ++ zs)) == count r1 + (count r2 + count zs)
def count_append3(+m: Maybe<&2, U32>, +r1: +List<U32>, +r2: +List<U32>, +zs: +List<U32>) ->
  {C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, zs)))
    == (C.count(m, r1) + (C.count(m, r2) + C.count(m, zs)) : Nat) : Nat}:
  +C1 = C.count(m, r1)
  Equal.trans(Nat, C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, zs))),
    (C1 + C.count(m, List.append(&2, U32, r2, zs)) : Nat),
    (C1 + (C.count(m, r2) + C.count(m, zs)) : Nat),
    Laws.count_append(m, r1, List.append(&2, U32, r2, zs)),
    Equal.cong(Nat, Nat, z => (C1 + z : Nat), C.count(m, List.append(&2, U32, r2, zs)),
      (C.count(m, r2) + C.count(m, zs) : Nat), Laws.count_append(m, r2, zs)))

# merging r1 and r2, then passing over the rest: the counts of r1, r2 and
# the rest, where ih covers the rest
def pass_count.merge(+m: Maybe<&2, U32>, +n: Nat, +r1: +List<U32>, +r2: +List<U32>,
  +pr: +List<U32>, +cr: +List<U32>, ih: {C.count(m, pr) == C.count(m, cr) : Nat}) ->
  {C.count(m, List.append(&2, U32, List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2)), pr))
    == (C.count(m, r1) + (C.count(m, r2) + C.count(m, cr)) : Nat) : Nat}:
  +mg = List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2))
  +C1 = C.count(m, r1)
  +C2 = C.count(m, r2)
  +RHS = (C1 + (C2 + C.count(m, cr)) : Nat)
  %Equal.sym(Nat, C.count(m, List.append(&2, U32, mg, pr)), (C.count(m, mg) + C.count(m, pr) : Nat),
    Laws.count_append(m, mg, pr)) : {_ == RHS : Nat}
  %Equal.sym(Nat, C.count(m, mg), parts(m, Nil{}, r1, r2), Laws.merge_count(m, n, Nil{}, r1, r2))
    : {(_ + C.count(m, pr) : Nat) == RHS : Nat}
  %Equal.sym(Nat, C.count(m, pr), C.count(m, cr), ih)
    : {(parts(m, Nil{}, r1, r2) + _ : Nat) == RHS : Nat}
  # (C1 + C2) + CR == C1 + (C2 + CR)
  Equal.sym(Nat, RHS, ((C1 + C2) + C.count(m, cr) : Nat), N.add_assoc(C1, C2, C.count(m, cr)))

def Laws.pass_count(m, n, runs):
  match runs:
    case Nil{}:
      {==}
    case r <> Nil{}:
      {==}
    case +r1 <> +r2 <> rest:
      +pr = List.concat(&2, U32, List.sort.pass(~U32, ~U32.is_le, n, rest))
      +cr = List.concat(&2, U32, rest)
      Equal.trans(Nat,
        C.count(m, List.append(&2, U32, List.merge.go(~U32, ~U32.is_le, n, (Nil{}, r1, r2)), pr)),
        (C.count(m, r1) + (C.count(m, r2) + C.count(m, cr)) : Nat),
        C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, cr))),
        pass_count.merge(m, n, r1, r2, pr, cr, Laws.pass_count(m, n, rest)),
        Equal.sym(Nat, C.count(m, List.append(&2, U32, r1, List.append(&2, U32, r2, cr))),
          (C.count(m, r1) + (C.count(m, r2) + C.count(m, cr)) : Nat), count_append3(m, r1, r2, cr)))

# the loop's last run is r ++ [] once flattened
def Laws.sort_go_count(m, fuel, n, runs):
  match fuel runs:
    case 0n _:
      {==}
    case 1n++f Nil{}:
      {==}
    case 1n++f +r <> Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, r, Nil{}), r, Laws.append_nil(&2, U32, r))
        : {C.count(m, r) == C.count(m, _) : Nat}
      {==}
    case 1n++f +r1 <> +r2 <> rest:
      +passed = List.sort.pass(~U32, ~U32.is_le, n, r1 <> r2 <> rest)
      Equal.trans(Nat, C.count(m, List.sort.go(~U32, ~U32.is_le, f, n, passed)),
        C.count(m, List.concat(&2, U32, passed)),
        C.count(m, List.concat(&2, U32, r1 <> r2 <> rest)),
        Laws.sort_go_count(m, f, n, passed), Laws.pass_count(m, n, r1 <> r2 <> rest))

def Laws.sort_runs(A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.sort_runs(A, t)
        : {h <> List.concat(&2, A, List.sort.runs(A, t)) == h <> _ : List<&2, A>}
      {==}

def Laws.count_all(xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.count_all(t) : {1n+C.count(None{}, t) == 1n+_ : Nat}
      {==}

# sort is the pass loop over the runs of xs, and the runs flatten to xs
def Laws.sort_count(m, xs):
  +n = List.length(&2, U32, xs)
  +runs = List.sort.runs(U32, xs)
  Equal.trans(Nat, C.count(m, List.sort.go(~U32, ~U32.is_le, n, n, runs)),
    C.count(m, List.concat(&2, U32, runs)), C.count(m, xs),
    Laws.sort_go_count(m, n, n, runs),
    Equal.cong(List<&2, U32>, Nat, z => C.count(m, z), List.concat(&2, U32, runs), xs,
      Laws.sort_runs(U32, xs)))

def Laws.sort_perm(x, xs):
  Laws.sort_count(Some{x}, xs)

# counting everything is the length
def Laws.sort_length(xs):
  +s = C.sort(xs)
  Equal.trans(Nat, List.length(&2, U32, s), C.count(None{}, s), List.length(&2, U32, xs),
    Equal.sym(Nat, C.count(None{}, s), List.length(&2, U32, s), Laws.count_all(s)),
    Equal.trans(Nat, C.count(None{}, s), C.count(None{}, xs), List.length(&2, U32, xs),
      Laws.sort_count(None{}, xs), Laws.count_all(xs)))

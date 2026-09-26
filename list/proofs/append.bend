# append.bend: append and concat. Each proof is an induction on the first
# list, which is the only one append looks at.

import Base
import ../LAWS.bend as Laws

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
      %Laws.append_assoc(a, A, t, ys, zs)
        : {h <> List.append(a, A, List.append(a, A, t, ys), zs) == h <> _ : List<a, A>}
      {==}

def Laws.length_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.length_append(a, A, t, ys)
        : {1n+List.length(a, A, List.append(a, A, t, ys)) == 1n+_ : Nat}
      {==}

# concat(h :: t ++ yss) == h ++ (concat t ++ concat yss), then append_assoc
def Laws.concat_append(a, A, xss, yss):
  match xss:
    case Nil{}:
      {==}
    case h <> t:
      -ct = List.concat(a, A, t)
      -cy = List.concat(a, A, yss)
      -L = List.append(a, A, h, List.concat(a, A, List.append(a, List<a, A>, t, yss)))
      %Equal.sym(List<a, A>, List.append(a, A, List.append(a, A, h, ct), cy),
        List.append(a, A, h, List.append(a, A, ct, cy)), Laws.append_assoc(a, A, h, ct, cy))
        : {L == _ : List<a, A>}
      %Laws.concat_append(a, A, t, yss) : {L == List.append(a, A, h, _) : List<a, A>}
      {==}

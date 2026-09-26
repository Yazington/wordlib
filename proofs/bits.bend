# bits.bend: the bitwise laws. Each is an induction on the width: the
# head bits agree by a Bool lemma, the tails by the law one bit narrower,
# and cons_eq puts the two together.

import Base
import ../LAWS.bend as Laws

# equal heads and equal tails make equal words
def cons_eq(-p: Nat, -x: Bool, -y: Bool, -t: Word(p), -u: Word(p),
  hx: {x == y : Bool}, ht: {t == u : Word(p)}) -> {WCon{x, t} == WCon{y, u} : Word.Con<p>}:
  %hx : {WCon{x, t} == WCon{_, u} : Word.Con<p>}
  %ht : {WCon{x, t} == WCon{x, _} : Word.Con<p>}
  {==}

# Bool lemmas, by truth table
# ---------------------------

def xor_comm.bit(a: Bool, b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def and_comm.bit(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def or_comm.bit(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def not_and.bit(a: Bool, b: Bool) ->
  {Bool.not(Bool.and(a, b)) == Bool.or(Bool.not(a), Bool.not(b)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# an associative Bool operation, by its value on the first argument
def xor_assoc.bit(a: Bool, b: Bool, c: Bool) ->
  {Bool.xor(a, Bool.xor(b, c)) == Bool.xor(Bool.xor(a, b), c) : Bool}:
  match a b:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}

def and_assoc.bit(a: Bool, -b: Bool, -c: Bool) ->
  {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_assoc.bit(a: Bool, -b: Bool, -c: Bool) ->
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def xor_zero.bit(a: Bool) -> {Bool.xor(a, False{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def xor_self.bit(a: Bool) -> {Bool.xor(a, a) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def not_not.bit(a: Bool) -> {Bool.not(Bool.not(a)) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Word laws
# ---------

def Laws.xor_comm(n, a, b):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u}:
      cons_eq(p, Bool.xor(x, y), Bool.xor(y, x), Word.xor(p, t, u), Word.xor(p, u, t),
        xor_comm.bit(x, y), Laws.xor_comm(p, t, u))

def Laws.and_comm(n, a, b):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u}:
      cons_eq(p, Bool.and(x, y), Bool.and(y, x), Word.and(p, t, u), Word.and(p, u, t),
        and_comm.bit(x, y), Laws.and_comm(p, t, u))

def Laws.or_comm(n, a, b):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u}:
      cons_eq(p, Bool.or(x, y), Bool.or(y, x), Word.or(p, t, u), Word.or(p, u, t),
        or_comm.bit(x, y), Laws.or_comm(p, t, u))

def Laws.xor_assoc(n, a, b, c):
  match n a b c:
    case 0n WNil{} WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u} WCon{z, v}:
      cons_eq(p, Bool.xor(x, Bool.xor(y, z)), Bool.xor(Bool.xor(x, y), z),
        Word.xor(p, t, Word.xor(p, u, v)), Word.xor(p, Word.xor(p, t, u), v),
        xor_assoc.bit(x, y, z), Laws.xor_assoc(p, t, u, v))

def Laws.and_assoc(n, a, b, c):
  match n a b c:
    case 0n WNil{} WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u} WCon{z, v}:
      cons_eq(p, Bool.and(x, Bool.and(y, z)), Bool.and(Bool.and(x, y), z),
        Word.and(p, t, Word.and(p, u, v)), Word.and(p, Word.and(p, t, u), v),
        and_assoc.bit(x, y, z), Laws.and_assoc(p, t, u, v))

def Laws.or_assoc(n, a, b, c):
  match n a b c:
    case 0n WNil{} WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u} WCon{z, v}:
      cons_eq(p, Bool.or(x, Bool.or(y, z)), Bool.or(Bool.or(x, y), z),
        Word.or(p, t, Word.or(p, u, v)), Word.or(p, Word.or(p, t, u), v),
        or_assoc.bit(x, y, z), Laws.or_assoc(p, t, u, v))

def Laws.xor_zero(n, a):
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{x, t}:
      cons_eq(p, Bool.xor(x, False{}), x, Word.xor(p, t, Word.zero(p)), t,
        xor_zero.bit(x), Laws.xor_zero(p, t))

def Laws.xor_self(n, a):
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{x, t}:
      cons_eq(p, Bool.xor(x, x), False{}, Word.xor(p, t, t), Word.zero(p),
        xor_self.bit(x), Laws.xor_self(p, t))

def Laws.not_not(n, a):
  match n a:
    case 0n WNil{}:
      {==}
    case 1n+p WCon{x, t}:
      cons_eq(p, Bool.not(Bool.not(x)), x, Word.not(p, Word.not(p, t)), t,
        not_not.bit(x), Laws.not_not(p, t))

def Laws.not_and(n, a, b):
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, t} WCon{y, u}:
      cons_eq(p, Bool.not(Bool.and(x, y)), Bool.or(Bool.not(x), Bool.not(y)),
        Word.not(p, Word.and(p, t, u)), Word.or(p, Word.not(p, t), Word.not(p, u)),
        not_and.bit(x, y), Laws.not_and(p, t, u))

# wordlib: the proofs of LAWS.bend. Each word law is an induction on the
# width: the head bit follows from a Bool lemma, the tail from the
# self-call.

import Base
import ./LAWS.bend as Laws
import ./word.bend as W
import ./nat.bend as N
import ./ac.bend as A

# Bool
# ----

def bool_xor_comm(a: Bool, b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def bool_xor_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.xor(a, Bool.xor(b, c)) == Bool.xor(Bool.xor(a, b), c) : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def bool_and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def bool_and_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def bool_or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def bool_or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def bool_not_and(a: Bool, b: Bool) -> {Bool.not(Bool.and(a, b)) == Bool.or(Bool.not(a), Bool.not(b)) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Bitwise algebra
# ---------------

def Laws.xor_comm(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, at} WCon{+bb, bt}:
          %bool_xor_comm(ab, bb) : {WCon{Bool.xor(ab, bb), Word.xor(p, at, bt)} == WCon{_, Word.xor(p, bt, at)} : Word.Con<p>}
          %Laws.xor_comm(p, at, bt) : {WCon{Bool.xor(ab, bb), Word.xor(p, at, bt)} == WCon{Bool.xor(ab, bb), _} : Word.Con<p>}
          {==}

def Laws.xor_assoc(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ab, at} WCon{+bb, bt} WCon{+cb, ct}:
          %bool_xor_assoc(ab, bb, cb) : {WCon{Bool.xor(ab, Bool.xor(bb, cb)), Word.xor(p, at, Word.xor(p, bt, ct))} == WCon{_, Word.xor(p, Word.xor(p, at, bt), ct)} : Word.Con<p>}
          %Laws.xor_assoc(p, at, bt, ct) : {WCon{Bool.xor(ab, Bool.xor(bb, cb)), Word.xor(p, at, Word.xor(p, bt, ct))} == WCon{Bool.xor(ab, Bool.xor(bb, cb)), _} : Word.Con<p>}
          {==}

def Laws.xor_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, at}:
          %Laws.xor_zero(p, at) : {WCon{False{}, Word.xor(p, at, Word.zero(p))} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, at}:
          %Laws.xor_zero(p, at) : {WCon{True{}, Word.xor(p, at, Word.zero(p))} == WCon{True{}, _} : Word.Con<p>}
          {==}

def Laws.xor_self(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, at}:
          %Laws.xor_self(p, at) : {WCon{False{}, Word.xor(p, at, at)} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, at}:
          %Laws.xor_self(p, at) : {WCon{False{}, Word.xor(p, at, at)} == WCon{False{}, _} : Word.Con<p>}
          {==}

def Laws.and_comm(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, at} WCon{+bb, bt}:
          %bool_and_comm(ab, bb) : {WCon{Bool.and(ab, bb), Word.and(p, at, bt)} == WCon{_, Word.and(p, bt, at)} : Word.Con<p>}
          %Laws.and_comm(p, at, bt) : {WCon{Bool.and(ab, bb), Word.and(p, at, bt)} == WCon{Bool.and(ab, bb), _} : Word.Con<p>}
          {==}

def Laws.and_assoc(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ab, at} WCon{+bb, bt} WCon{+cb, ct}:
          %bool_and_assoc(ab, bb, cb) : {WCon{Bool.and(ab, Bool.and(bb, cb)), Word.and(p, at, Word.and(p, bt, ct))} == WCon{_, Word.and(p, Word.and(p, at, bt), ct)} : Word.Con<p>}
          %Laws.and_assoc(p, at, bt, ct) : {WCon{Bool.and(ab, Bool.and(bb, cb)), Word.and(p, at, Word.and(p, bt, ct))} == WCon{Bool.and(ab, Bool.and(bb, cb)), _} : Word.Con<p>}
          {==}

def Laws.or_comm(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, at} WCon{+bb, bt}:
          %bool_or_comm(ab, bb) : {WCon{Bool.or(ab, bb), Word.or(p, at, bt)} == WCon{_, Word.or(p, bt, at)} : Word.Con<p>}
          %Laws.or_comm(p, at, bt) : {WCon{Bool.or(ab, bb), Word.or(p, at, bt)} == WCon{Bool.or(ab, bb), _} : Word.Con<p>}
          {==}

def Laws.or_assoc(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ab, at} WCon{+bb, bt} WCon{+cb, ct}:
          %bool_or_assoc(ab, bb, cb) : {WCon{Bool.or(ab, Bool.or(bb, cb)), Word.or(p, at, Word.or(p, bt, ct))} == WCon{_, Word.or(p, Word.or(p, at, bt), ct)} : Word.Con<p>}
          %Laws.or_assoc(p, at, bt, ct) : {WCon{Bool.or(ab, Bool.or(bb, cb)), Word.or(p, at, Word.or(p, bt, ct))} == WCon{Bool.or(ab, Bool.or(bb, cb)), _} : Word.Con<p>}
          {==}

def Laws.not_not(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, at}:
          %Laws.not_not(p, at) : {WCon{False{}, Word.not(p, Word.not(p, at))} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, at}:
          %Laws.not_not(p, at) : {WCon{True{}, Word.not(p, Word.not(p, at))} == WCon{True{}, _} : Word.Con<p>}
          {==}

def Laws.not_and(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, at} WCon{+bb, bt}:
          %bool_not_and(ab, bb) : {WCon{Bool.not(Bool.and(ab, bb)), Word.not(p, Word.and(p, at, bt))} == WCon{_, Word.or(p, Word.not(p, at), Word.not(p, bt))} : Word.Con<p>}
          %Laws.not_and(p, at, bt) : {WCon{Bool.not(Bool.and(ab, bb)), Word.not(p, Word.and(p, at, bt))} == WCon{Bool.not(Bool.and(ab, bb)), _} : Word.Con<p>}
          {==}

# Arithmetic
# ----------

def Laws.add_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, at}:
          %Laws.add_zero(p, at) : {WCon{False{}, Word.add(p, at, Word.zero(p))} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, at}:
          %Laws.add_zero(p, at) : {WCon{True{}, Word.add(p, at, Word.zero(p))} == WCon{True{}, _} : Word.Con<p>}
          {==}

# The adder is exact
# ------------------

def scale_dbl(K: Bool, +P: Nat) -> {Nat.double(W.scale(K, P)) == W.scale(K, Nat.double(P)) : Nat}:
  match K:
    case False{}:
      {==}
    case True{}:
      {==}

# one bit of the adder, over Nats: S and k are the sum and carry bits,
# a0 b0 c the input bits, R the tail sum, K its carry, P = 2^p
def adc_step(+S: Nat, +k: Nat, +a0: Nat, +b0: Nat, +c: Nat, +R: Nat, +K: Bool, +P: Nat, +A0: Nat, +B0: Nat,
  ih: {Nat.add(R, W.scale(K, P)) == Nat.add(A0, Nat.add(B0, k)) : Nat},
  fa: {Nat.add(S, Nat.double(k)) == Nat.add(a0, Nat.add(b0, c)) : Nat}) ->
  {Nat.add(Nat.add(S, Nat.double(R)), W.scale(K, Nat.double(P))) == Nat.add(Nat.add(a0, Nat.double(A0)), Nat.add(Nat.add(b0, Nat.double(B0)), c)) : Nat}:
  %scale_dbl(K, P) : {Nat.add(Nat.add(S, Nat.double(R)), _) == Nat.add(Nat.add(a0, Nat.double(A0)), Nat.add(Nat.add(b0, Nat.double(B0)), c)) : Nat}
  %A.ac([S, R, W.scale(K, P)], A.EAdd{A.EAtom{0n}, A.EDbl{A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{1n}}}, A.EDbl{A.EAtom{2n}}}, {==}) : {_ == Nat.add(Nat.add(a0, Nat.double(A0)), Nat.add(Nat.add(b0, Nat.double(B0)), c)) : Nat}
  %Equal.sym(Nat, Nat.add(R, W.scale(K, P)), Nat.add(A0, Nat.add(B0, k)), ih) : {Nat.add(S, Nat.double(_)) == Nat.add(Nat.add(a0, Nat.double(A0)), Nat.add(Nat.add(b0, Nat.double(B0)), c)) : Nat}
  %A.ac([a0, A0, b0, B0, c], A.EAdd{A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{2n}, A.EAtom{4n}}}, A.EAdd{A.EDbl{A.EAtom{1n}}, A.EDbl{A.EAtom{3n}}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{1n}}}, A.EAdd{A.EAdd{A.EAtom{2n}, A.EDbl{A.EAtom{3n}}}, A.EAtom{4n}}}, {==}) : {Nat.add(S, Nat.double(Nat.add(A0, Nat.add(B0, k)))) == _ : Nat}
  %fa : {Nat.add(S, Nat.double(Nat.add(A0, Nat.add(B0, k)))) == Nat.add(_, Nat.add(Nat.double(A0), Nat.double(B0))) : Nat}
  A.ac([S, A0, B0, k], A.EAdd{A.EAtom{0n}, A.EDbl{A.EAdd{A.EAtom{1n}, A.EAdd{A.EAtom{2n}, A.EAtom{3n}}}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{3n}}}, A.EAdd{A.EDbl{A.EAtom{1n}}, A.EDbl{A.EAtom{2n}}}}, {==})

def Laws.adc_nat(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          {==}
    case 1n++p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          adc_step(0n, 0n, 0n, 0n, 0n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), W.carry(p, at, bt, False{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          adc_step(1n, 0n, 0n, 0n, 1n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), W.carry(p, at, bt, False{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          adc_step(1n, 0n, 0n, 1n, 0n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), W.carry(p, at, bt, False{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, False{}), {==})
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          adc_step(0n, 1n, 0n, 1n, 1n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), W.carry(p, at, bt, True{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          adc_step(1n, 0n, 1n, 0n, 0n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), W.carry(p, at, bt, False{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, False{}), {==})
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          adc_step(0n, 1n, 1n, 0n, 1n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), W.carry(p, at, bt, True{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          adc_step(0n, 1n, 1n, 1n, 0n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), W.carry(p, at, bt, True{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, True{}), {==})
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          adc_step(1n, 1n, 1n, 1n, 1n,
            Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), W.carry(p, at, bt, True{}), W.pow2(p),
            Word.to_nat(p, at), Word.to_nat(p, bt),
            Laws.adc_nat(p, at, bt, True{}), {==})

# Bounds and injectivity
# ----------------------

def Laws.not_nat(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          %Laws.not_nat(p, t) : {1n+Nat.add(Nat.double(Word.to_nat(p, t)), 1n+Nat.double(Word.to_nat(p, Word.not(p, t)))) == Nat.double(_) : Nat}
          A.ac([Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)), 1n],
            A.EAdd{A.EAtom{2n}, A.EAdd{A.EDbl{A.EAtom{0n}}, A.EAdd{A.EAtom{2n}, A.EDbl{A.EAtom{1n}}}}},
            A.EDbl{A.EAdd{A.EAtom{2n}, A.EAdd{A.EAtom{0n}, A.EAtom{1n}}}}, {==})
        case WCon{True{}, +t}:
          %Laws.not_nat(p, t) : {1n+Nat.add(1n+Nat.double(Word.to_nat(p, t)), Nat.double(Word.to_nat(p, Word.not(p, t)))) == Nat.double(_) : Nat}
          A.ac([Word.to_nat(p, t), Word.to_nat(p, Word.not(p, t)), 1n],
            A.EAdd{A.EAtom{2n}, A.EAdd{A.EAdd{A.EAtom{2n}, A.EDbl{A.EAtom{0n}}}, A.EDbl{A.EAtom{1n}}}},
            A.EDbl{A.EAdd{A.EAtom{2n}, A.EAdd{A.EAtom{0n}, A.EAtom{1n}}}}, {==})

def Laws.to_nat_inj(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %Laws.to_nat_inj(p, at, bt, N.double_inj(Word.to_nat(p, at), Word.to_nat(p, bt), h)) : {WCon{False{}, at} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %Laws.to_nat_inj(p, at, bt, N.double_inj(Word.to_nat(p, at), Word.to_nat(p, bt), N.succ_inj(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), h))) : {WCon{True{}, at} == WCon{True{}, _} : Word.Con<p>}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, N.parity(Word.to_nat(p, at), Word.to_nat(p, bt), h))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, N.parity(Word.to_nat(p, bt), Word.to_nat(p, at), Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), h)))

# Subtraction
# -----------

def Laws.adc_sub(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          %Laws.adc_sub(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, at, Word.not(p, bt), False{}, False{})} == WCon{True{}, _} : Word.Con<p>}
          {==}
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          %Laws.adc_sub(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, at, Word.not(p, bt), False{}, True{})} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          %Laws.adc_sub(p, at, bt, False{}) : {WCon{False{}, Word.adc(p, at, Word.not(p, bt), False{}, False{})} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          %Laws.adc_sub(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, at, Word.not(p, bt), False{}, False{})} == WCon{True{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          %Laws.adc_sub(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, at, Word.not(p, bt), False{}, True{})} == WCon{False{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          %Laws.adc_sub(p, at, bt, True{}) : {WCon{True{}, Word.adc(p, at, Word.not(p, bt), False{}, True{})} == WCon{True{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          %Laws.adc_sub(p, at, bt, False{}) : {WCon{True{}, Word.adc(p, at, Word.not(p, bt), False{}, False{})} == WCon{True{}, _} : Word.Con<p>}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          %Laws.adc_sub(p, at, bt, True{}) : {WCon{False{}, Word.adc(p, at, Word.not(p, bt), False{}, True{})} == WCon{False{}, _} : Word.Con<p>}
          {==}

# a value below P plus a full P cannot fit below P
def no_wrap.eq(+d: Nat, +G: Nat, +P: Nat, e: {1n+Nat.add(Nat.add(d, P), G) == P : Nat}) -> {Nat.add(1n+Nat.add(d, G), P) == Nat.add(0n, P) : Nat}:
  %A.ac([d, G, P, 1n], A.EAdd{A.EAtom{3n}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{2n}}, A.EAtom{1n}}}, A.EAdd{A.EAdd{A.EAtom{3n}, A.EAdd{A.EAtom{0n}, A.EAtom{1n}}}, A.EAtom{2n}}, {==}) : {_ == P : Nat}
  e

def no_wrap(+d: Nat, +G: Nat, +P: Nat, e: {1n+Nat.add(Nat.add(d, P), G) == P : Nat}) -> Empty:
  N.succ_ne_zero(Nat.add(d, G), N.add_cancel_r(1n+Nat.add(d, G), 0n, P, no_wrap.eq(d, G, P, e)))

def wrap_exact.sub(+R: Nat, +d: Nat, +G: Nat, +P: Nat, e: {Nat.add(R, 0n) == Nat.add(d, P) : Nat}, bound: {1n+Nat.add(R, G) == P : Nat}) -> {1n+Nat.add(Nat.add(d, P), G) == P : Nat}:
  %e : {1n+Nat.add(_, G) == P : Nat}
  %N.add_zero(R) : {1n+Nat.add(_, G) == P : Nat}
  bound

# R + K*P == d + P with R below P forces the carry and R == d
def wrap_exact(K: Bool, +R: Nat, +d: Nat, +P: Nat, +G: Nat, e: {Nat.add(R, W.scale(K, P)) == Nat.add(d, P) : Nat}, bound: {1n+Nat.add(R, G) == P : Nat}) -> {R == d : Nat}:
  match K:
    case True{}:
      N.add_cancel_r(R, d, P, e)
    case False{}:
      Empty.absurd({R == d : Nat}, no_wrap(d, G, P, wrap_exact.sub(R, d, G, P, e, bound)))

def sub_eq.rest(+n: Nat, +a: Word(n), +b: Word(n), +d: Nat, h: {Word.to_nat(n, a) == Nat.add(Word.to_nat(n, b), d) : Nat}) -> {Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, Word.not(n, b)), 1n)) == Nat.add(d, W.pow2(n)) : Nat}:
  %Laws.not_nat(n, b) : {Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, Word.not(n, b)), 1n)) == Nat.add(d, _) : Nat}
  %Equal.sym(Nat, Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), d), h) : {Nat.add(_, Nat.add(Word.to_nat(n, Word.not(n, b)), 1n)) == Nat.add(d, 1n+Nat.add(Word.to_nat(n, b), Word.to_nat(n, Word.not(n, b)))) : Nat}
  A.ac([Word.to_nat(n, b), d, Word.to_nat(n, Word.not(n, b)), 1n],
    A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAdd{A.EAtom{2n}, A.EAtom{3n}}},
    A.EAdd{A.EAtom{1n}, A.EAdd{A.EAtom{3n}, A.EAdd{A.EAtom{0n}, A.EAtom{2n}}}}, {==})

def sub_eq(+n: Nat, +a: Word(n), +b: Word(n), +d: Nat, h: {Word.to_nat(n, a) == Nat.add(Word.to_nat(n, b), d) : Nat}) -> {Nat.add(Word.to_nat(n, Word.sub(n, a, b)), W.scale(W.carry(n, a, Word.not(n, b), True{}), W.pow2(n))) == Nat.add(d, W.pow2(n)) : Nat}:
  %Laws.adc_sub(n, a, b, True{}) : {Nat.add(Word.to_nat(n, _), W.scale(W.carry(n, a, Word.not(n, b), True{}), W.pow2(n))) == Nat.add(d, W.pow2(n)) : Nat}
  Equal.trans(Nat,
    Nat.add(Word.to_nat(n, Word.adc(n, a, Word.not(n, b), False{}, True{})), W.scale(W.carry(n, a, Word.not(n, b), True{}), W.pow2(n))),
    Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, Word.not(n, b)), 1n)),
    Nat.add(d, W.pow2(n)),
    Laws.adc_nat(n, a, Word.not(n, b), True{}),
    sub_eq.rest(n, a, b, d, h))

def Laws.sub_nat(n, a, b, d, h):
  wrap_exact(W.carry(n, a, Word.not(n, b), True{}), Word.to_nat(n, Word.sub(n, a, b)), d, W.pow2(n),
    Word.to_nat(n, Word.not(n, Word.sub(n, a, b))), sub_eq(n, a, b, d, h), Laws.not_nat(n, Word.sub(n, a, b)))

# Associativity
# -------------

# X + k*P == Y + j*P with X, Y below P forces X == Y
def uniq.shuffle(+X: Nat, +M: Nat, +Y: Nat, +M2: Nat, +P: Nat, e: {Nat.add(X, Nat.add(P, M)) == Nat.add(Y, Nat.add(P, M2)) : Nat}) -> {Nat.add(Nat.add(X, M), P) == Nat.add(Nat.add(Y, M2), P) : Nat}:
  %A.ac([X, M, P], A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{2n}, A.EAtom{1n}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAtom{2n}}, {==}) : {_ == Nat.add(Nat.add(Y, M2), P) : Nat}
  %A.ac([Y, M2, P], A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{2n}, A.EAtom{1n}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAtom{2n}}, {==}) : {Nat.add(X, Nat.add(P, M)) == _ : Nat}
  e

def uniq.lift(+X: Nat, +Y: Nat, +M: Nat, +P: Nat, e: {Nat.add(X, 0n) == Nat.add(Y, Nat.add(P, M)) : Nat}) -> {Nat.add(X, 0n) == Nat.add(Nat.add(Y, M), P) : Nat}:
  %A.ac([Y, M, P], A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{2n}, A.EAtom{1n}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAtom{2n}}, {==}) : {Nat.add(X, 0n) == _ : Nat}
  e

def uniq(+X: Nat, +Y: Nat, +P: Nat, +GX: Nat, +GY: Nat, +k: Nat, +j: Nat,
  e: {Nat.add(X, Nat.mul(k, P)) == Nat.add(Y, Nat.mul(j, P)) : Nat},
  bX: {1n+Nat.add(X, GX) == P : Nat}, bY: {1n+Nat.add(Y, GY) == P : Nat}) -> {X == Y : Nat}:
  match k j:
    case 0n 0n:
      N.add_cancel_r(X, Y, 0n, e)
    case 1n++kp 1n++jp:
      uniq(X, Y, P, GX, GY, kp, jp,
        N.add_cancel_r(Nat.add(X, Nat.mul(kp, P)), Nat.add(Y, Nat.mul(jp, P)), P,
          uniq.shuffle(X, Nat.mul(kp, P), Y, Nat.mul(jp, P), P, e)), bX, bY)
    case 0n 1n++jp:
      Empty.absurd({X == Y : Nat}, no_wrap(Nat.add(Y, Nat.mul(jp, P)), GX, P,
        wrap_exact.sub(X, Nat.add(Y, Nat.mul(jp, P)), GX, P, uniq.lift(X, Y, Nat.mul(jp, P), P, e), bX)))
    case 1n++kp 0n:
      Empty.absurd({X == Y : Nat}, no_wrap(Nat.add(X, Nat.mul(kp, P)), GY, P,
        wrap_exact.sub(Y, Nat.add(X, Nat.mul(kp, P)), GY, P,
          uniq.lift(Y, X, Nat.mul(kp, P), P, Equal.sym(Nat, Nat.add(X, Nat.add(P, Nat.mul(kp, P))), Nat.add(Y, 0n), e)), bY)))

def uniq.conv(+X: Nat, +Y: Nat, +L: Nat, +L2: Nat, +R: Nat, +R2: Nat, e: {Nat.add(X, L) == Nat.add(Y, R) : Nat}, hl: {L == L2 : Nat}, hr: {R == R2 : Nat}) -> {Nat.add(X, L2) == Nat.add(Y, R2) : Nat}:
  %hl : {Nat.add(X, _) == Nat.add(Y, R2) : Nat}
  %hr : {Nat.add(X, L) == Nat.add(Y, _) : Nat}
  e
def assoc.cases(J2: Bool, J1: Bool, K2: Bool, K1: Bool, +Y: Nat, +X: Nat, +P: Nat, +GY: Nat, +GX: Nat,
  e: {Nat.add(Y, Nat.add(W.scale(J2, P), W.scale(J1, P))) == Nat.add(X, Nat.add(W.scale(K2, P), W.scale(K1, P))) : Nat},
  bY: {1n+Nat.add(Y, GY) == P : Nat}, bX: {1n+Nat.add(X, GX) == P : Nat}) -> {Y == X : Nat}:
  match J2 J1 K2 K1:
    case False{} False{} False{} False{}:
      uniq(Y, X, P, GY, GX, 0n, 0n,
        uniq.conv(Y, X, Nat.add(0n, 0n), Nat.mul(0n, P), Nat.add(0n, 0n), Nat.mul(0n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==})), bY, bX)
    case False{} False{} False{} True{}:
      uniq(Y, X, P, GY, GX, 0n, 1n,
        uniq.conv(Y, X, Nat.add(0n, 0n), Nat.mul(0n, P), Nat.add(0n, P), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case False{} False{} True{} False{}:
      uniq(Y, X, P, GY, GX, 0n, 1n,
        uniq.conv(Y, X, Nat.add(0n, 0n), Nat.mul(0n, P), Nat.add(P, 0n), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case False{} False{} True{} True{}:
      uniq(Y, X, P, GY, GX, 0n, 2n,
        uniq.conv(Y, X, Nat.add(0n, 0n), Nat.mul(0n, P), Nat.add(P, P), Nat.mul(2n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==})), bY, bX)
    case False{} True{} False{} False{}:
      uniq(Y, X, P, GY, GX, 1n, 0n,
        uniq.conv(Y, X, Nat.add(0n, P), Nat.mul(1n, P), Nat.add(0n, 0n), Nat.mul(0n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==})), bY, bX)
    case False{} True{} False{} True{}:
      uniq(Y, X, P, GY, GX, 1n, 1n,
        uniq.conv(Y, X, Nat.add(0n, P), Nat.mul(1n, P), Nat.add(0n, P), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case False{} True{} True{} False{}:
      uniq(Y, X, P, GY, GX, 1n, 1n,
        uniq.conv(Y, X, Nat.add(0n, P), Nat.mul(1n, P), Nat.add(P, 0n), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case False{} True{} True{} True{}:
      uniq(Y, X, P, GY, GX, 1n, 2n,
        uniq.conv(Y, X, Nat.add(0n, P), Nat.mul(1n, P), Nat.add(P, P), Nat.mul(2n, P), e,
          A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==})), bY, bX)
    case True{} False{} False{} False{}:
      uniq(Y, X, P, GY, GX, 1n, 0n,
        uniq.conv(Y, X, Nat.add(P, 0n), Nat.mul(1n, P), Nat.add(0n, 0n), Nat.mul(0n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==})), bY, bX)
    case True{} False{} False{} True{}:
      uniq(Y, X, P, GY, GX, 1n, 1n,
        uniq.conv(Y, X, Nat.add(P, 0n), Nat.mul(1n, P), Nat.add(0n, P), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case True{} False{} True{} False{}:
      uniq(Y, X, P, GY, GX, 1n, 1n,
        uniq.conv(Y, X, Nat.add(P, 0n), Nat.mul(1n, P), Nat.add(P, 0n), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case True{} False{} True{} True{}:
      uniq(Y, X, P, GY, GX, 1n, 2n,
        uniq.conv(Y, X, Nat.add(P, 0n), Nat.mul(1n, P), Nat.add(P, P), Nat.mul(2n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==})), bY, bX)
    case True{} True{} False{} False{}:
      uniq(Y, X, P, GY, GX, 2n, 0n,
        uniq.conv(Y, X, Nat.add(P, P), Nat.mul(2n, P), Nat.add(0n, 0n), Nat.mul(0n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EZero{}}, A.EZero{}, {==})), bY, bX)
    case True{} True{} False{} True{}:
      uniq(Y, X, P, GY, GX, 2n, 1n,
        uniq.conv(Y, X, Nat.add(P, P), Nat.mul(2n, P), Nat.add(0n, P), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==}), A.ac([P], A.EAdd{A.EZero{}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case True{} True{} True{} False{}:
      uniq(Y, X, P, GY, GX, 2n, 1n,
        uniq.conv(Y, X, Nat.add(P, P), Nat.mul(2n, P), Nat.add(P, 0n), Nat.mul(1n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EZero{}}, A.EAdd{A.EAtom{0n}, A.EZero{}}, {==})), bY, bX)
    case True{} True{} True{} True{}:
      uniq(Y, X, P, GY, GX, 2n, 2n,
        uniq.conv(Y, X, Nat.add(P, P), Nat.mul(2n, P), Nat.add(P, P), Nat.mul(2n, P), e,
          A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==}), A.ac([P], A.EAdd{A.EAtom{0n}, A.EAtom{0n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, {==})), bY, bX)
# (a + b) + c, by value: X + 2^n*(K2 + K1) == A + (B + C)
def assoc.r(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) -> {Nat.add(Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), Nat.add(W.scale(W.carry(n, Word.add(n, a, b), c, False{}), W.pow2(n)), W.scale(W.carry(n, a, b, False{}), W.pow2(n)))) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}:
  %A.ac([Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), W.scale(W.carry(n, Word.add(n, a, b), c, False{}), W.pow2(n)), W.scale(W.carry(n, a, b, False{}), W.pow2(n))], A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAtom{2n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}, {==}) : {_ == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  %Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), W.scale(W.carry(n, Word.add(n, a, b), c, False{}), W.pow2(n))), Nat.add(Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, c), 0n)), Laws.adc_nat(n, Word.add(n, a, b), c, False{})) : {Nat.add(_, W.scale(W.carry(n, a, b, False{}), W.pow2(n))) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  %A.ac([Word.to_nat(n, Word.add(n, a, b)), Word.to_nat(n, c), W.scale(W.carry(n, a, b, False{}), W.pow2(n))], A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{2n}}, A.EAdd{A.EAtom{1n}, A.EZero{}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EZero{}}}, A.EAtom{2n}}, {==}) : {_ == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  %Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.scale(W.carry(n, a, b, False{}), W.pow2(n))), Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), 0n)), Laws.adc_nat(n, a, b, False{})) : {Nat.add(_, Nat.add(Word.to_nat(n, c), 0n)) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  A.ac([Word.to_nat(n, a), Word.to_nat(n, b), Word.to_nat(n, c)], A.EAdd{A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EZero{}}}, A.EAdd{A.EAtom{2n}, A.EZero{}}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}, {==})

# a + (b + c), by value: Y + 2^n*(J2 + J1) == A + (B + C)
def assoc.l(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) -> {Nat.add(Word.to_nat(n, Word.add(n, a, Word.add(n, b, c))), Nat.add(W.scale(W.carry(n, a, Word.add(n, b, c), False{}), W.pow2(n)), W.scale(W.carry(n, b, c, False{}), W.pow2(n)))) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}:
  %A.ac([Word.to_nat(n, Word.add(n, a, Word.add(n, b, c))), W.scale(W.carry(n, a, Word.add(n, b, c), False{}), W.pow2(n)), W.scale(W.carry(n, b, c, False{}), W.pow2(n))], A.EAdd{A.EAdd{A.EAtom{0n}, A.EAtom{1n}}, A.EAtom{2n}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}, {==}) : {_ == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  %Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.add(n, a, Word.add(n, b, c))), W.scale(W.carry(n, a, Word.add(n, b, c), False{}), W.pow2(n))), Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, Word.add(n, b, c)), 0n)), Laws.adc_nat(n, a, Word.add(n, b, c), False{})) : {Nat.add(_, W.scale(W.carry(n, b, c, False{}), W.pow2(n))) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  %A.ac([Word.to_nat(n, a), Word.to_nat(n, Word.add(n, b, c)), W.scale(W.carry(n, b, c, False{}), W.pow2(n))], A.EAdd{A.EAdd{A.EAtom{1n}, A.EAtom{2n}}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EZero{}}}, A.EAtom{2n}}, {==}) : {_ == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  %Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.add(n, b, c)), W.scale(W.carry(n, b, c, False{}), W.pow2(n))), Nat.add(Word.to_nat(n, b), Nat.add(Word.to_nat(n, c), 0n)), Laws.adc_nat(n, b, c, False{})) : {Nat.add(_, Nat.add(Word.to_nat(n, a), 0n)) == Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))) : Nat}
  A.ac([Word.to_nat(n, a), Word.to_nat(n, b), Word.to_nat(n, c)], A.EAdd{A.EAdd{A.EAtom{1n}, A.EAdd{A.EAtom{2n}, A.EZero{}}}, A.EAdd{A.EAtom{0n}, A.EZero{}}}, A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}, {==})

def assoc.eq(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) -> {Nat.add(Word.to_nat(n, Word.add(n, a, Word.add(n, b, c))), Nat.add(W.scale(W.carry(n, a, Word.add(n, b, c), False{}), W.pow2(n)), W.scale(W.carry(n, b, c, False{}), W.pow2(n)))) == Nat.add(Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), Nat.add(W.scale(W.carry(n, Word.add(n, a, b), c, False{}), W.pow2(n)), W.scale(W.carry(n, a, b, False{}), W.pow2(n)))) : Nat}:
  Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.add(n, a, Word.add(n, b, c))), Nat.add(W.scale(W.carry(n, a, Word.add(n, b, c), False{}), W.pow2(n)), W.scale(W.carry(n, b, c, False{}), W.pow2(n)))), Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))), Nat.add(Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), Nat.add(W.scale(W.carry(n, Word.add(n, a, b), c, False{}), W.pow2(n)), W.scale(W.carry(n, a, b, False{}), W.pow2(n)))),
    assoc.l(n, a, b, c), Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), Nat.add(W.scale(W.carry(n, Word.add(n, a, b), c, False{}), W.pow2(n)), W.scale(W.carry(n, a, b, False{}), W.pow2(n)))), Nat.add(Word.to_nat(n, a), Nat.add(Word.to_nat(n, b), Word.to_nat(n, c))), assoc.r(n, a, b, c)))

def Laws.add_assoc(n, a, b, c):
  Laws.to_nat_inj(n, Word.add(n, a, Word.add(n, b, c)), Word.add(n, Word.add(n, a, b), c),
    assoc.cases(W.carry(n, a, Word.add(n, b, c), False{}), W.carry(n, b, c, False{}), W.carry(n, Word.add(n, a, b), c, False{}), W.carry(n, a, b, False{}),
      Word.to_nat(n, Word.add(n, a, Word.add(n, b, c))), Word.to_nat(n, Word.add(n, Word.add(n, a, b), c)), W.pow2(n), Word.to_nat(n, Word.not(n, Word.add(n, a, Word.add(n, b, c)))), Word.to_nat(n, Word.not(n, Word.add(n, Word.add(n, a, b), c))),
      assoc.eq(n, a, b, c), Laws.not_nat(n, Word.add(n, a, Word.add(n, b, c))), Laws.not_nat(n, Word.add(n, Word.add(n, a, b), c))))

# Addition without overflow
# -------------------------

def no_carry.sub(+R: Nat, +S: Nat, +P: Nat, +g: Nat, e: {Nat.add(R, P) == S : Nat}, h: {1n+Nat.add(S, g) == P : Nat}) -> {1n+Nat.add(Nat.add(R, P), g) == P : Nat}:
  %Equal.sym(Nat, Nat.add(R, P), S, e) : {1n+Nat.add(_, g) == P : Nat}
  h

# R + K*P == S with S below P rules the carry out
def no_carry(K: Bool, +R: Nat, +S: Nat, +P: Nat, +g: Nat, e: {Nat.add(R, W.scale(K, P)) == S : Nat}, h: {1n+Nat.add(S, g) == P : Nat}) -> {R == S : Nat}:
  match K:
    case False{}:
      Equal.trans(Nat, R, Nat.add(R, 0n), S, N.add_zero(R), e)
    case True{}:
      Empty.absurd({R == S : Nat}, no_wrap(R, g, P, no_carry.sub(R, S, P, g, e, h)))

def add_eq(+n: Nat, +a: Word(n), +b: Word(n)) -> {Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.scale(W.carry(n, a, b, False{}), W.pow2(n))) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  %Equal.sym(Nat, Word.to_nat(n, b), Nat.add(Word.to_nat(n, b), 0n), N.add_zero(Word.to_nat(n, b))) : {Nat.add(Word.to_nat(n, Word.add(n, a, b)), W.scale(W.carry(n, a, b, False{}), W.pow2(n))) == Nat.add(Word.to_nat(n, a), _) : Nat}
  Laws.adc_nat(n, a, b, False{})

def Laws.add_exact(n, a, b, g, h):
  no_carry(W.carry(n, a, b, False{}), Word.to_nat(n, Word.add(n, a, b)), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), W.pow2(n), g, add_eq(n, a, b), h)

# Shifts
# ------

# one step of shl.put over Nats: c the bit shifted in, R the tail, K the
# bit shifted out, P = 2^p, bb and T the input's head and tail
def shl_step(+c: Nat, +R: Nat, +K: Bool, +P: Nat, +bb: Nat, +T: Nat, ih: {Nat.add(R, W.scale(K, P)) == Nat.add(bb, Nat.double(T)) : Nat}) ->
  {Nat.add(Nat.add(c, Nat.double(R)), W.scale(K, Nat.double(P))) == Nat.add(c, Nat.double(Nat.add(bb, Nat.double(T)))) : Nat}:
  %scale_dbl(K, P) : {Nat.add(Nat.add(c, Nat.double(R)), _) == Nat.add(c, Nat.double(Nat.add(bb, Nat.double(T)))) : Nat}
  %A.ac([c, R, W.scale(K, P)], A.EAdd{A.EAtom{0n}, A.EDbl{A.EAdd{A.EAtom{1n}, A.EAtom{2n}}}}, A.EAdd{A.EAdd{A.EAtom{0n}, A.EDbl{A.EAtom{1n}}}, A.EDbl{A.EAtom{2n}}}, {==}) : {_ == Nat.add(c, Nat.double(Nat.add(bb, Nat.double(T)))) : Nat}
  %Equal.sym(Nat, Nat.add(R, W.scale(K, P)), Nat.add(bb, Nat.double(T)), ih) : {Nat.add(c, Nat.double(_)) == Nat.add(c, Nat.double(Nat.add(bb, Nat.double(T)))) : Nat}
  {==}

def Laws.shl_put(n, c, w):
  match n:
    case 0n:
      match c w:
        case False{} WNil{}:
          {==}
        case True{} WNil{}:
          {==}
    case 1n++p:
      match c w:
        case False{} WCon{False{}, +t}:
          shl_step(0n, Word.to_nat(p, Word.shl.put(p, False{}, t)), W.top(p, False{}, t), W.pow2(p), 0n, Word.to_nat(p, t), Laws.shl_put(p, False{}, t))
        case False{} WCon{True{}, +t}:
          shl_step(0n, Word.to_nat(p, Word.shl.put(p, True{}, t)), W.top(p, True{}, t), W.pow2(p), 1n, Word.to_nat(p, t), Laws.shl_put(p, True{}, t))
        case True{} WCon{False{}, +t}:
          shl_step(1n, Word.to_nat(p, Word.shl.put(p, False{}, t)), W.top(p, False{}, t), W.pow2(p), 0n, Word.to_nat(p, t), Laws.shl_put(p, False{}, t))
        case True{} WCon{True{}, +t}:
          shl_step(1n, Word.to_nat(p, Word.shl.put(p, True{}, t)), W.top(p, True{}, t), W.pow2(p), 1n, Word.to_nat(p, t), Laws.shl_put(p, True{}, t))

def Laws.shl_nat(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{+b, +t}:
          Laws.shl_put(1n+p, False{}, WCon{b, t})

def Laws.shr_pad(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          %Laws.shr_pad(p, t) : {Nat.double(Word.to_nat(1n+p, Word.shr.pad(p, t))) == Nat.double(_) : Nat}
          {==}
        case WCon{True{}, +t}:
          %Laws.shr_pad(p, t) : {1n+Nat.double(Word.to_nat(1n+p, Word.shr.pad(p, t))) == 1n+Nat.double(_) : Nat}
          {==}

def Laws.shr_nat(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          %Laws.shr_pad(p, t) : {Nat.double(Word.to_nat(1n+p, Word.shr.pad(p, t))) == Nat.double(_) : Nat}
          {==}
        case WCon{True{}, +t}:
          %Laws.shr_pad(p, t) : {1n+Nat.double(Word.to_nat(1n+p, Word.shr.pad(p, t))) == 1n+Nat.double(_) : Nat}
          {==}

# Comparison
# ----------

def cmp_bits_00(+x: Nat, +y: Nat) -> {Word.cmp.fin(False{}, False{}, Nat.cmp(x, y)) == Nat.cmp(Nat.double(x), Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      cmp_bits_00(p, q)

def cmp_bits_01(+x: Nat, +y: Nat) -> {Word.cmp.fin(False{}, True{}, Nat.cmp(x, y)) == Nat.cmp(Nat.double(x), 1n+Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      cmp_bits_01(p, q)

def cmp_bits_10(+x: Nat, +y: Nat) -> {Word.cmp.fin(True{}, False{}, Nat.cmp(x, y)) == Nat.cmp(1n+Nat.double(x), Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      cmp_bits_10(p, q)

def cmp_bits_11(+x: Nat, +y: Nat) -> {Word.cmp.fin(True{}, True{}, Nat.cmp(x, y)) == Nat.cmp(1n+Nat.double(x), 1n+Nat.double(y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      cmp_bits_11(p, q)

def Laws.cmp_nat(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %cmp_bits_00(Word.to_nat(p, at), Word.to_nat(p, bt)) : {Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt)) == _ : Cmp}
          %Laws.cmp_nat(p, at, bt) : {Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt)) == Word.cmp.fin(False{}, False{}, _) : Cmp}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %cmp_bits_01(Word.to_nat(p, at), Word.to_nat(p, bt)) : {Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt)) == _ : Cmp}
          %Laws.cmp_nat(p, at, bt) : {Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt)) == Word.cmp.fin(False{}, True{}, _) : Cmp}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %cmp_bits_10(Word.to_nat(p, at), Word.to_nat(p, bt)) : {Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt)) == _ : Cmp}
          %Laws.cmp_nat(p, at, bt) : {Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt)) == Word.cmp.fin(True{}, False{}, _) : Cmp}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %cmp_bits_11(Word.to_nat(p, at), Word.to_nat(p, bt)) : {Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt)) == _ : Cmp}
          %Laws.cmp_nat(p, at, bt) : {Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt)) == Word.cmp.fin(True{}, True{}, _) : Cmp}
          {==}

# U32
# ---

def Laws.u32_xor_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      %Laws.xor_comm(32n, x, y) : {U32{Word.xor(32n, x, y)} == U32{_} : U32}
      {==}

def Laws.u32_and_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      %Laws.and_comm(32n, x, y) : {U32{Word.and(32n, x, y)} == U32{_} : U32}
      {==}

def Laws.u32_or_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      %Laws.or_comm(32n, x, y) : {U32{Word.or(32n, x, y)} == U32{_} : U32}
      {==}

def Laws.u32_xor_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      %Laws.xor_assoc(32n, x, y, z) : {U32{Word.xor(32n, x, Word.xor(32n, y, z))} == U32{_} : U32}
      {==}

def Laws.u32_and_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      %Laws.and_assoc(32n, x, y, z) : {U32{Word.and(32n, x, Word.and(32n, y, z))} == U32{_} : U32}
      {==}

def Laws.u32_or_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      %Laws.or_assoc(32n, x, y, z) : {U32{Word.or(32n, x, Word.or(32n, y, z))} == U32{_} : U32}
      {==}

def Laws.u32_add_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      %Laws.add_assoc(32n, x, y, z) : {U32{Word.add(32n, x, Word.add(32n, y, z))} == U32{_} : U32}
      {==}

def Laws.u32_add_zero(a):
  match a:
    case U32{x}:
      %Laws.add_zero(32n, x) : {U32{Word.add(32n, x, Word.zero(32n))} == U32{_} : U32}
      {==}

def Laws.u32_xor_zero(a):
  match a:
    case U32{x}:
      %Laws.xor_zero(32n, x) : {U32{Word.xor(32n, x, Word.zero(32n))} == U32{_} : U32}
      {==}

def Laws.u32_xor_self(a):
  match a:
    case U32{+x}:
      %Laws.xor_self(32n, x) : {U32{Word.xor(32n, x, x)} == U32{_} : U32}
      {==}

def Laws.u32_not_not(a):
  match a:
    case U32{x}:
      %Laws.not_not(32n, x) : {U32{Word.not(32n, Word.not(32n, x))} == U32{_} : U32}
      {==}

def Laws.u32_to_nat_inj(a, b, h):
  match a b:
    case U32{+x} U32{+y}:
      %Laws.to_nat_inj(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def Laws.u32_sub_nat(a, b, d, h):
  match a b:
    case U32{+x} U32{+y}:
      Laws.sub_nat(32n, x, y, d, h)

def Laws.u32_cmp_nat(a, b):
  match a b:
    case U32{x} U32{y}:
      Laws.cmp_nat(32n, x, y)

def Laws.u32_lt_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      %Laws.cmp_nat(32n, x, y) : {Cmp.is_lt(Word.cmp(32n, x, y)) == Cmp.is_lt(_) : Bool}
      {==}

def Laws.u32_le_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      %Laws.cmp_nat(32n, x, y) : {Cmp.is_le(Word.cmp(32n, x, y)) == Cmp.is_le(_) : Bool}
      {==}

#!/usr/bin/env python3
"""Emits the proof of Laws.add_assoc (appended to PROOF.bend by hand).
Route: both sides' values equal A + B + C up to multiples of 2^n
(adc_nat), both are below 2^n (not_nat), so they are equal (uniq) and
the words are equal (to_nat_inj)."""

def at(i): return f"A.EAtom{{{i}n}}"
def add(x, y): return f"A.EAdd{{{x}, {y}}}"
Z = "A.EZero{}"
def ac(env, new, old): return f"A.ac([{', '.join(env)}], {new}, {old}, {{==}})"
def nadd(x, y): return f"Nat.add({x}, {y})"
def sym(a, b, e): return f"Equal.sym(Nat, {a}, {b}, {e})"

P = "W.pow2(n)"
A, B, C = (f"Word.to_nat(n, {v})" for v in "abc")
wab, wbc = "Word.add(n, a, b)", "Word.add(n, b, c)"
wL = f"Word.add(n, a, {wbc})"          # law left side:  a + (b + c)
wR = f"Word.add(n, {wab}, c)"          # law right side: (a + b) + c
YL, XR = f"Word.to_nat(n, {wL})", f"Word.to_nat(n, {wR})"
AB, BC = f"Word.to_nat(n, {wab})", f"Word.to_nat(n, {wbc})"
def sc(x, y): return f"W.scale(W.carry(n, {x}, {y}, False{{}}), {P})"
sK1, sK2 = sc("a", "b"), sc(wab, "c")     # carries of (a+b), then of (a+b)+c
sJ1, sJ2 = sc("b", "c"), sc("a", wbc)     # carries of (b+c), then of a+(b+c)
def E(x, y): return f"Laws.adc_nat(n, {x}, {y}, False{{}})"
T = nadd(A, nadd(B, C))
Z0 = "0n"

out = []
w = out.append
sig = "(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n))"

w(f"""
# Associativity
# -------------

# X + k*P == Y + j*P with X, Y below P forces X == Y
def uniq.shuffle(+X: Nat, +M: Nat, +Y: Nat, +M2: Nat, +P: Nat, e: {{{nadd('X', nadd('P', 'M'))} == {nadd('Y', nadd('P', 'M2'))} : Nat}}) -> {{{nadd(nadd('X', 'M'), 'P')} == {nadd(nadd('Y', 'M2'), 'P')} : Nat}}:
  %{ac(['X', 'M', 'P'], add(at(0), add(at(2), at(1))), add(add(at(0), at(1)), at(2)))} : {{_ == {nadd(nadd('Y', 'M2'), 'P')} : Nat}}
  %{ac(['Y', 'M2', 'P'], add(at(0), add(at(2), at(1))), add(add(at(0), at(1)), at(2)))} : {{{nadd('X', nadd('P', 'M'))} == _ : Nat}}
  e

def uniq.lift(+X: Nat, +Y: Nat, +M: Nat, +P: Nat, e: {{{nadd('X', Z0)} == {nadd('Y', nadd('P', 'M'))} : Nat}}) -> {{{nadd('X', Z0)} == {nadd(nadd('Y', 'M'), 'P')} : Nat}}:
  %{ac(['Y', 'M', 'P'], add(at(0), add(at(2), at(1))), add(add(at(0), at(1)), at(2)))} : {{{nadd('X', Z0)} == _ : Nat}}
  e

def uniq(+X: Nat, +Y: Nat, +P: Nat, +GX: Nat, +GY: Nat, +k: Nat, +j: Nat,
  e: {{Nat.add(X, Nat.mul(k, P)) == Nat.add(Y, Nat.mul(j, P)) : Nat}},
  bX: {{1n+Nat.add(X, GX) == P : Nat}}, bY: {{1n+Nat.add(Y, GY) == P : Nat}}) -> {{X == Y : Nat}}:
  match k j:
    case 0n 0n:
      N.add_cancel_r(X, Y, 0n, e)
    case 1n++kp 1n++jp:
      uniq(X, Y, P, GX, GY, kp, jp,
        N.add_cancel_r(Nat.add(X, Nat.mul(kp, P)), Nat.add(Y, Nat.mul(jp, P)), P,
          uniq.shuffle(X, Nat.mul(kp, P), Y, Nat.mul(jp, P), P, e)), bX, bY)
    case 0n 1n++jp:
      Empty.absurd({{X == Y : Nat}}, no_wrap(Nat.add(Y, Nat.mul(jp, P)), GX, P,
        wrap_exact.sub(X, Nat.add(Y, Nat.mul(jp, P)), GX, P, uniq.lift(X, Y, Nat.mul(jp, P), P, e), bX)))
    case 1n++kp 0n:
      Empty.absurd({{X == Y : Nat}}, no_wrap(Nat.add(X, Nat.mul(kp, P)), GY, P,
        wrap_exact.sub(Y, Nat.add(X, Nat.mul(kp, P)), GY, P,
          uniq.lift(Y, X, Nat.mul(kp, P), P, Equal.sym(Nat, Nat.add(X, Nat.add(P, Nat.mul(kp, P))), Nat.add(Y, 0n), e)), bY)))

def uniq.conv(+X: Nat, +Y: Nat, +L: Nat, +L2: Nat, +R: Nat, +R2: Nat, e: {{Nat.add(X, L) == Nat.add(Y, R) : Nat}}, hl: {{L == L2 : Nat}}, hr: {{R == R2 : Nat}}) -> {{Nat.add(X, L2) == Nat.add(Y, R2) : Nat}}:
  %hl : {{Nat.add(X, _) == Nat.add(Y, R2) : Nat}}
  %hr : {{Nat.add(X, L) == Nat.add(Y, _) : Nat}}
  e
""")

# the 16 carry cases
def red(b1, b2):  # (scale b1 P) + (scale b2 P), reduced; and its ac Expr
    t = lambda b: "P" if b else "0n"
    ex = lambda b: at(0) if b else Z
    return nadd(t(b1), t(b2)), add(ex(b1), ex(b2))
def mulx(k):      # ac Expr for Nat.mul(kn, P), unfolded
    e = Z
    for _ in range(k): e = add(at(0), e)
    return e
B_ = lambda b: "True{}" if b else "False{}"
cases = []
for J2 in (0, 1):
  for J1 in (0, 1):
    for K2 in (0, 1):
      for K1 in (0, 1):
        Lr, Le = red(J2, J1); Rr, Re = red(K2, K1)
        k, j = J2 + J1, K2 + K1
        cases.append(f"""    case {B_(J2)} {B_(J1)} {B_(K2)} {B_(K1)}:
      uniq(Y, X, P, GY, GX, {k}n, {j}n,
        uniq.conv(Y, X, {Lr}, Nat.mul({k}n, P), {Rr}, Nat.mul({j}n, P), e,
          {ac(['P'], Le, mulx(k))}, {ac(['P'], Re, mulx(j))}), bY, bX)""")
w(f"""def assoc.cases(J2: Bool, J1: Bool, K2: Bool, K1: Bool, +Y: Nat, +X: Nat, +P: Nat, +GY: Nat, +GX: Nat,
  e: {{Nat.add(Y, Nat.add(W.scale(J2, P), W.scale(J1, P))) == Nat.add(X, Nat.add(W.scale(K2, P), W.scale(K1, P))) : Nat}},
  bY: {{1n+Nat.add(Y, GY) == P : Nat}}, bX: {{1n+Nat.add(X, GX) == P : Nat}}) -> {{Y == X : Nat}}:
  match J2 J1 K2 K1:
""" + "\n".join(cases) + "\n")

# the two value chains
w(f"""# (a + b) + c, by value: X + 2^n*(K2 + K1) == A + (B + C)
def assoc.r{sig} -> {{{nadd(XR, nadd(sK2, sK1))} == {T} : Nat}}:
  %{ac([XR, sK2, sK1], add(add(at(0), at(1)), at(2)), add(at(0), add(at(1), at(2))))} : {{_ == {T} : Nat}}
  %{sym(nadd(XR, sK2), nadd(AB, nadd(C, Z0)), E(wab, 'c'))} : {{Nat.add(_, {sK1}) == {T} : Nat}}
  %{ac([AB, C, sK1], add(add(at(0), at(2)), add(at(1), Z)), add(add(at(0), add(at(1), Z)), at(2)))} : {{_ == {T} : Nat}}
  %{sym(nadd(AB, sK1), nadd(A, nadd(B, Z0)), E('a', 'b'))} : {{Nat.add(_, {nadd(C, Z0)}) == {T} : Nat}}
  {ac([A, B, C], add(add(at(0), add(at(1), Z)), add(at(2), Z)), add(at(0), add(at(1), at(2))))}

# a + (b + c), by value: Y + 2^n*(J2 + J1) == A + (B + C)
def assoc.l{sig} -> {{{nadd(YL, nadd(sJ2, sJ1))} == {T} : Nat}}:
  %{ac([YL, sJ2, sJ1], add(add(at(0), at(1)), at(2)), add(at(0), add(at(1), at(2))))} : {{_ == {T} : Nat}}
  %{sym(nadd(YL, sJ2), nadd(A, nadd(BC, Z0)), E('a', wbc))} : {{Nat.add(_, {sJ1}) == {T} : Nat}}
  %{ac([A, BC, sJ1], add(add(at(1), at(2)), add(at(0), Z)), add(add(at(0), add(at(1), Z)), at(2)))} : {{_ == {T} : Nat}}
  %{sym(nadd(BC, sJ1), nadd(B, nadd(C, Z0)), E('b', 'c'))} : {{Nat.add(_, {nadd(A, Z0)}) == {T} : Nat}}
  {ac([A, B, C], add(add(at(1), add(at(2), Z)), add(at(0), Z)), add(at(0), add(at(1), at(2))))}

def assoc.eq{sig} -> {{{nadd(YL, nadd(sJ2, sJ1))} == {nadd(XR, nadd(sK2, sK1))} : Nat}}:
  Equal.trans(Nat, {nadd(YL, nadd(sJ2, sJ1))}, {T}, {nadd(XR, nadd(sK2, sK1))},
    assoc.l(n, a, b, c), Equal.sym(Nat, {nadd(XR, nadd(sK2, sK1))}, {T}, assoc.r(n, a, b, c)))

def Laws.add_assoc(n, a, b, c):
  Laws.to_nat_inj(n, {wL}, {wR},
    assoc.cases(W.carry(n, a, {wbc}, False{{}}), W.carry(n, b, c, False{{}}), W.carry(n, {wab}, c, False{{}}), W.carry(n, a, b, False{{}}),
      {YL}, {XR}, {P}, Word.to_nat(n, Word.not(n, {wL})), Word.to_nat(n, Word.not(n, {wR})),
      assoc.eq(n, a, b, c), Laws.not_nat(n, {wL}), Laws.not_nat(n, {wR})))
""")
print("".join(out), end="")

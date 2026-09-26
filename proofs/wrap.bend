# wrap.bend: arithmetic of values below P = 2^n. A word's value is below P
# (not_nat names the gap), so an equation that adds whole multiples of P
# to such values pins down the values and the multiples. Carries, wraps
# and overflow all come down to the lemmas here.

import Base
import ../word.bend as W
import ../lib/nat.bend as N
import ../lib/ac.bend as A

# 2 scale(K, P) == scale(K, 2P)
def scale_dbl(K: Bool, +P: Nat) -> {Nat.double(W.scale(K, P)) == W.scale(K, Nat.double(P)) : Nat}:
  match K:
    case False{}:
      {==}
    case True{}:
      {==}

# scale(K, P) == b2n(K) * P
def scale_mul(K: Bool, +P: Nat) -> {W.scale(K, P) == (W.b2n(K) * P : Nat) : Nat}:
  match K:
    case False{}:
      {==}
    case True{}:
      N.add_zero(P)

# s + 2(R + X) == (s + 2R) + 2X
def double_sum(+s: Nat, +R: Nat, +X: Nat) ->
  {(s + Nat.double((R + X : Nat)) : Nat) == ((s + Nat.double(R)) + Nat.double(X) : Nat) : Nat}:
  A.ac([s, R, X], A.add(A.x0(), A.dbl(A.add(A.x1(), A.x2()))),
    A.add(A.add(A.x0(), A.dbl(A.x1())), A.dbl(A.x2())), {==})

# 1 + ((d + P) + G) == P, restated as (1 + (d + G)) + P == 0 + P
def no_wrap.shift(+d: Nat, +G: Nat, +P: Nat, e: {1n+((d + P) + G : Nat) == P : Nat}) ->
  {Nat.add(1n+(d + G : Nat), P) == (0n + P : Nat) : Nat}:
  # 1 + ((d + P) + G) == (1 + (d + G)) + P
  %A.ac([d, G, P, 1n], A.add(A.x3(), A.add(A.add(A.x0(), A.x2()), A.x1())),
    A.add(A.add(A.x3(), A.add(A.x0(), A.x1())), A.x2()), {==}) : {_ == P : Nat}
  e

# a value plus a whole P cannot fit below P: 1 + ((d + P) + G) != P
def no_wrap(+d: Nat, +G: Nat, +P: Nat, e: {1n+((d + P) + G : Nat) == P : Nat}) -> Empty:
  N.succ_ne_zero((d + G : Nat), N.add_cancel_r(1n+(d + G : Nat), 0n, P, no_wrap.shift(d, G, P, e)))

# with R + 0 == d + P, R's bound becomes one for d + P
def wrap_exact.lift(+R: Nat, +d: Nat, +G: Nat, +P: Nat,
  e: {(R + 0n : Nat) == (d + P : Nat) : Nat}, bound: {1n+(R + G : Nat) == P : Nat}) ->
  {1n+((d + P) + G : Nat) == P : Nat}:
  %e : {1n+(_ + G : Nat) == P : Nat}
  %N.add_zero(R) : {1n+(_ + G : Nat) == P : Nat}
  bound

# R + scale(K, P) == d + P with R below P forces the carry: R == d
def wrap_exact(K: Bool, +R: Nat, +d: Nat, +P: Nat, +G: Nat,
  e: {(R + W.scale(K, P) : Nat) == (d + P : Nat) : Nat}, bound: {1n+(R + G : Nat) == P : Nat}) ->
  {R == d : Nat}:
  match K:
    case True{}:
      N.add_cancel_r(R, d, P, e)
    case False{}:
      Empty.absurd({R == d : Nat}, no_wrap(d, G, P, wrap_exact.lift(R, d, G, P, e, bound)))

# with R + P == S, S's bound becomes one for R + P
def no_carry.lift(+R: Nat, +S: Nat, +P: Nat, +g: Nat,
  e: {(R + P : Nat) == S : Nat}, h: {1n+(S + g : Nat) == P : Nat}) ->
  {1n+((R + P) + g : Nat) == P : Nat}:
  %Equal.sym(Nat, (R + P : Nat), S, e) : {1n+(_ + g : Nat) == P : Nat}
  h

# R + scale(K, P) == S with S below P rules the carry out: R == S
def no_carry(K: Bool, +R: Nat, +S: Nat, +P: Nat, +g: Nat,
  e: {(R + W.scale(K, P) : Nat) == S : Nat}, h: {1n+(S + g : Nat) == P : Nat}) -> {R == S : Nat}:
  match K:
    case False{}:
      Equal.trans(Nat, R, (R + 0n : Nat), S, N.add_zero(R), e)
    case True{}:
      Empty.absurd({R == S : Nat}, no_wrap(R, g, P, no_carry.lift(R, S, P, g, e, h)))

# X + (P + M) == Y + (P + M2) gives (X + M) + P == (Y + M2) + P
def uniq.shuffle(+X: Nat, +M: Nat, +Y: Nat, +M2: Nat, +P: Nat,
  e: {(X + (P + M) : Nat) == (Y + (P + M2) : Nat) : Nat}) ->
  {((X + M) + P : Nat) == ((Y + M2) + P : Nat) : Nat}:
  # a + (c + b) == (a + b) + c, once per side
  %A.ac([X, M, P],
    A.add(A.x0(), A.add(A.x2(), A.x1())), A.add(A.add(A.x0(), A.x1()), A.x2()), {==})
    : {_ == ((Y + M2) + P : Nat) : Nat}
  %A.ac([Y, M2, P],
    A.add(A.x0(), A.add(A.x2(), A.x1())), A.add(A.add(A.x0(), A.x1()), A.x2()), {==})
    : {(X + (P + M) : Nat) == _ : Nat}
  e

# X + 0 == Y + (P + M) gives X + 0 == (Y + M) + P
def uniq.lift(+X: Nat, +Y: Nat, +M: Nat, +P: Nat,
  e: {(X + 0n : Nat) == (Y + (P + M) : Nat) : Nat}) ->
  {(X + 0n : Nat) == ((Y + M) + P : Nat) : Nat}:
  %A.ac([Y, M, P],
    A.add(A.x0(), A.add(A.x2(), A.x1())), A.add(A.add(A.x0(), A.x1()), A.x2()), {==})
    : {(X + 0n : Nat) == _ : Nat}
  e

# X + k P == Y + j P with X and Y below P forces X == Y
def uniq(+X: Nat, +Y: Nat, +P: Nat, +GX: Nat, +GY: Nat, +k: Nat, +j: Nat,
  e: {(X + (k * P) : Nat) == (Y + (j * P) : Nat) : Nat},
  bX: {1n+(X + GX : Nat) == P : Nat}, bY: {1n+(Y + GY : Nat) == P : Nat}) -> {X == Y : Nat}:
  match k j:
    case 0n 0n:
      N.add_cancel_r(X, Y, 0n, e)
    case 1n++kp 1n++jp:
      +KP = (kp * P : Nat)
      +JP = (jp * P : Nat)
      +e2 = N.add_cancel_r((X + KP : Nat), (Y + JP : Nat), P, uniq.shuffle(X, KP, Y, JP, P, e))
      uniq(X, Y, P, GX, GY, kp, jp, e2, bX, bY)
    case 0n 1n++jp:
      +JP = (jp * P : Nat)
      +e2 = wrap_exact.lift(X, (Y + JP : Nat), GX, P, uniq.lift(X, Y, JP, P, e), bX)
      Empty.absurd({X == Y : Nat}, no_wrap((Y + JP : Nat), GX, P, e2))
    case 1n++kp 0n:
      +KP = (kp * P : Nat)
      +e1 = Equal.sym(Nat, (X + (P + KP) : Nat), (Y + 0n : Nat), e)
      +e2 = wrap_exact.lift(Y, (X + KP : Nat), GY, P, uniq.lift(Y, X, KP, P, e1), bY)
      Empty.absurd({X == Y : Nat}, no_wrap((X + KP : Nat), GY, P, e2))

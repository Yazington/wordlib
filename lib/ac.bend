# ac.bend: equations between sums, decided by computation.
#
# An Expr is a sum of atoms, with doubling. eval gives its value in an
# environment (a list of Nats), and norm counts how often each atom occurs,
# so two Exprs with the same counts are equal in every environment. ac turns
# that into a proof: write both sides of a goal as Exprs over the goal's own
# terms, Bend checks {norm(e1) == norm(e2)} by computing, and ac returns
# {eval(env, e1) == eval(env, e2)}, which is the goal once eval unfolds.
#
#   A.ac([a, b, c], A.add(A.x0(), A.add(A.x1(), A.x2())),
#                   A.add(A.x2(), A.add(A.x1(), A.x0())), {==})
#     : {(a + (b + c) : Nat) == (c + (b + a) : Nat) : Nat}
#
# Numerals go in as atoms too: with 1n in the environment, 1n+x is x plus
# that atom.

import Base
import ./nat.bend as N

type Expr is Data:
  EAtom{i: Nat}
  EAdd{a: Expr, b: Expr}
  EDbl{a: Expr}
  EZero{}

# Building Exprs: x0() to x7() are atoms 0 to 7, and add, dbl and zero
# stand for Nat.add, Nat.double and 0n.

def x0() -> Expr:
  EAtom{0n}

def x1() -> Expr:
  EAtom{1n}

def x2() -> Expr:
  EAtom{2n}

def x3() -> Expr:
  EAtom{3n}

def x4() -> Expr:
  EAtom{4n}

def x5() -> Expr:
  EAtom{5n}

def x6() -> Expr:
  EAtom{6n}

def x7() -> Expr:
  EAtom{7n}

def add(a: Expr, b: Expr) -> Expr:
  EAdd{a, b}

def dbl(a: Expr) -> Expr:
  EDbl{a}

def zero() -> Expr:
  EZero{}

# Meaning
# -------

# the i-th atom; atoms past the end are 0n
def nth(env: +List<Nat>, i: Nat) -> Nat:
  match env i:
    case Nil{} _:
      0n
    case Con{x, xs} 0n:
      x
    case Con{x, xs} 1n+j:
      nth(xs, j)

def eval(+env: +List<Nat>, e: Expr) -> Nat:
  match e:
    case EAtom{i}:
      nth(env, i)
    case EAdd{a, b}:
      (eval(env, a) + eval(env, b) : Nat)
    case EDbl{a}:
      Nat.double(eval(env, a))
    case EZero{}:
      0n

# Normal form: cs[i] counts atom i, with no trailing zeros
# --------------------------------------------------------

def unit(i: Nat) -> +List<Nat>:
  match i:
    case 0n:
      Con{1n, Nil{}}
    case 1n+j:
      Con{0n, unit(j)}

def vadd(u: +List<Nat>, v: +List<Nat>) -> +List<Nat>:
  match u v:
    case Nil{} _:
      v
    case Con{a, us} Nil{}:
      Con{a, us}
    case Con{a, us} Con{b, vs}:
      Con{(a + b : Nat), vadd(us, vs)}

def norm(e: Expr) -> +List<Nat>:
  match e:
    case EAtom{i}:
      unit(i)
    case EAdd{a, b}:
      vadd(norm(a), norm(b))
    case EDbl{a}:
      +v = norm(a)
      vadd(v, v)
    case EZero{}:
      Nil{}

# the value of a normal form: the sum of cs[i] * env[i]
def evalc(cs: +List<Nat>, +env: +List<Nat>) -> Nat:
  match cs env:
    case Nil{} _:
      0n
    case Con{c, rest} Nil{}:
      0n
    case Con{c, rest} Con{x, xs}:
      ((c * x) + evalc(rest, xs) : Nat)

# Soundness
# ---------

# a unit vector picks its atom
def unit_ok(+env: +List<Nat>, +i: Nat) -> {evalc(unit(i), env) == nth(env, i) : Nat}:
  match env i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{x, xs} 0n:
      %N.add_zero(x) : {(_ + 0n : Nat) == x : Nat}
      %N.add_zero(x) : {_ == x : Nat}
      {==}
    case Con{x, xs} 1n+j:
      unit_ok(xs, j)

# adding count vectors adds their values
def vadd_ok(+u: +List<Nat>, +v: +List<Nat>, +env: +List<Nat>) ->
  {evalc(vadd(u, v), env) == (evalc(u, env) + evalc(v, env) : Nat) : Nat}:
  match u v env:
    case Nil{} _ _:
      {==}
    case Con{a, us} Nil{} _:
      %N.add_zero(evalc(Con{a, us}, env)) : {evalc(Con{a, us}, env) == _ : Nat}
      {==}
    case Con{a, us} Con{b, vs} Nil{}:
      {==}
    case Con{a, us} Con{b, vs} Con{x, xs}:
      +W = evalc(vadd(us, vs), xs)
      +U = evalc(us, xs)
      +V = evalc(vs, xs)
      %N.add_4((a * x : Nat), (b * x : Nat), U, V) : {(((a + b) * x) + W : Nat) == _ : Nat}
      %N.mul_add_r(a, b, x) : {(((a + b) * x) + W : Nat) == (_ + (U + V) : Nat) : Nat}
      %vadd_ok(us, vs, xs) : {(((a + b) * x) + W : Nat) == (((a + b) * x) + _ : Nat) : Nat}
      {==}

# a normal form has its Expr's value
def norm_ok(+e: Expr, +env: +List<Nat>) -> {evalc(norm(e), env) == eval(env, e) : Nat}:
  match e:
    case EAtom{i}:
      unit_ok(env, i)
    case EAdd{a, b}:
      +L = evalc(norm(EAdd{a, b}), env)
      %norm_ok(a, env) : {L == (_ + eval(env, b) : Nat) : Nat}
      %norm_ok(b, env) : {L == (evalc(norm(a), env) + _ : Nat) : Nat}
      vadd_ok(norm(a), norm(b), env)
    case EDbl{a}:
      +L = evalc(norm(EDbl{a}), env)
      %N.double_add_self(eval(env, a)) : {L == _ : Nat}
      %norm_ok(a, env) : {L == (_ + _ : Nat) : Nat}
      vadd_ok(norm(a), norm(a), env)
    case EZero{}:
      {==}

# two sums with the same atom counts are equal
def ac(+env: +List<Nat>, +e1: Expr, +e2: Expr, h: {norm(e1) == norm(e2) : +List<Nat>}) ->
  {eval(env, e1) == eval(env, e2) : Nat}:
  %norm_ok(e1, env) : {_ == eval(env, e2) : Nat}
  %norm_ok(e2, env) : {evalc(norm(e1), env) == _ : Nat}
  %h : {evalc(norm(e1), env) == evalc(_, env) : Nat}
  {==}

# ac.bend: sums over Nat decided by reflection. An Expr is a sum of atoms,
# with doubling; `norm` counts each atom, so two Exprs with the same
# counts denote the same Nat. `ac` turns that computation into a proof:
# Bend checks {norm(e1) == norm(e2)} with {==}, and the goal
# {eval(env, e1) == eval(env, e2)} follows for every env.

import Base
import ./nat.bend as N

type Expr is Data:
  EAtom{i: Nat}
  EAdd{a: Expr, b: Expr}
  EDbl{a: Expr}
  EZero{}

# the i-th atom's value; atoms past the end are 0n
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
      Nat.add(eval(env, a), eval(env, b))
    case EDbl{a}:
      Nat.double(eval(env, a))
    case EZero{}:
      0n

# Normal form: cs[i] counts atom i; no trailing zeros
# ----------------------------------------------------

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
      Con{Nat.add(a, b), vadd(us, vs)}

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

# the value of a normal form: sum of cs[i] * env[i]
def evalc(cs: +List<Nat>, +env: +List<Nat>) -> Nat:
  match cs env:
    case Nil{} _:
      0n
    case Con{c, rest} Nil{}:
      0n
    case Con{c, rest} Con{x, xs}:
      Nat.add(Nat.mul(c, x), evalc(rest, xs))

# Soundness
# ---------

def unit_ok(+env: +List<Nat>, +i: Nat) -> {evalc(unit(i), env) == nth(env, i) : Nat}:
  match env i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{x, xs} 0n:
      %N.add_zero(x) : {Nat.add(_, 0n) == x : Nat}
      %N.add_zero(x) : {_ == x : Nat}
      {==}
    case Con{x, xs} 1n+j:
      unit_ok(xs, j)

def vadd_ok(+u: +List<Nat>, +v: +List<Nat>, +env: +List<Nat>) -> {evalc(vadd(u, v), env) == Nat.add(evalc(u, env), evalc(v, env)) : Nat}:
  match u v env:
    case Nil{} _ _:
      {==}
    case Con{a, us} Nil{} _:
      %N.add_zero(evalc(Con{a, us}, env)) : {evalc(Con{a, us}, env) == _ : Nat}
      {==}
    case Con{a, us} Con{b, vs} Nil{}:
      {==}
    case Con{a, us} Con{b, vs} Con{x, xs}:
      %N.add_4(Nat.mul(a, x), Nat.mul(b, x), evalc(us, xs), evalc(vs, xs)) : {Nat.add(Nat.mul(Nat.add(a, b), x), evalc(vadd(us, vs), xs)) == _ : Nat}
      %N.mul_add_r(a, b, x) : {Nat.add(Nat.mul(Nat.add(a, b), x), evalc(vadd(us, vs), xs)) == Nat.add(_, Nat.add(evalc(us, xs), evalc(vs, xs))) : Nat}
      %vadd_ok(us, vs, xs) : {Nat.add(Nat.mul(Nat.add(a, b), x), evalc(vadd(us, vs), xs)) == Nat.add(Nat.mul(Nat.add(a, b), x), _) : Nat}
      {==}

def norm_ok(+e: Expr, +env: +List<Nat>) -> {evalc(norm(e), env) == eval(env, e) : Nat}:
  match e:
    case EAtom{i}:
      unit_ok(env, i)
    case EAdd{a, b}:
      %norm_ok(a, env) : {evalc(norm(EAdd{a, b}), env) == Nat.add(_, eval(env, b)) : Nat}
      %norm_ok(b, env) : {evalc(norm(EAdd{a, b}), env) == Nat.add(evalc(norm(a), env), _) : Nat}
      vadd_ok(norm(a), norm(b), env)
    case EDbl{a}:
      %N.double_add_self(eval(env, a)) : {evalc(norm(EDbl{a}), env) == _ : Nat}
      %norm_ok(a, env) : {evalc(norm(EDbl{a}), env) == Nat.add(_, _) : Nat}
      vadd_ok(norm(a), norm(a), env)
    case EZero{}:
      {==}

# LAW-shaped entry point: two sums with equal atom counts are equal
def ac(+env: +List<Nat>, +e1: Expr, +e2: Expr, h: {norm(e1) == norm(e2) : +List<Nat>}) -> {eval(env, e1) == eval(env, e2) : Nat}:
  %norm_ok(e1, env) : {_ == eval(env, e2) : Nat}
  %norm_ok(e2, env) : {evalc(norm(e1), env) == _ : Nat}
  %h : {evalc(norm(e1), env) == evalc(_, env) : Nat}
  {==}

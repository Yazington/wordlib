# wordlib

A verified standard library for Bend: proved laws, proof automation and
property-based testing, so Bend programs ship with guarantees.

Bend promises code that is proved correct. wordlib is the library that makes
that cheap: laws you import instead of re-proving, a prover for the tedious
steps, and tests that catch a false law before you spend time proving it.

Today: 44 laws on machine words (`Word(n)` at every width, and `U32`), the
bridge from machine arithmetic to `Nat`, and `ac`, a prover for sums.
Every law is also property-tested by bendcheck's `lawcheck`, a companion
library, so a wrong law fails with a counterexample in seconds instead of
stalling a proof.

Built against Bend 2.0.28. `./check.sh` runs every check.

## Layout

| File | Contents |
|---|---|
| `LAWS.bend` | the claims (44 laws) |
| `PROOF.bend` | their proofs |
| `word.bend` | vocabulary the laws use: `b2n`, `scale`, `pow2`, `maj`, `carry`, `top`, `lsb`, `mulq` |
| `nat.bend` | `Nat` lemmas: add algebra, cancellation, injectivity, parity, `le_sub` |
| `mul.bend` | `Nat.mul` lemmas: distributivity, associativity, commutativity, doubling |
| `ac.bend` | `ac`: a reflective prover for sums (see below) |
| `examples/withdraw/` | a U32 program whose safety is proved with wordlib |
| `tools/` | proof generators and the U32 differential tester |
| `tests/` | ac tests and mutation tests |

## The laws

**Bitwise** (any width): `xor_comm`, `xor_assoc`, `xor_zero`, `xor_self`,
`and_comm`, `and_assoc`, `or_comm`, `or_assoc`, `not_not`, `not_and` (De Morgan).

**Semantics** (any width; `A = Word.to_nat(n, a)`, `P = 2^n`):

| Law | Statement |
|---|---|
| `adc_nat` | `to_nat(a + b + c) + carry·P == A + B + c`: the adder is exact |
| `not_nat` | `1 + A + to_nat(not a) == P`: every word is below `2^n` |
| `to_nat_inj` | `A == B` implies `a == b` |
| `adc_sub` | `a - b` is `a + not b` with carry-in 1 |
| `sub_nat` | if `A == B + d` then `to_nat(a - b) == d` (no wrap) |
| `add_exact` | if `A + B < P` then `to_nat(a + b) == A + B` (no overflow) |
| `add_assoc` | `a + (b + c) == (a + b) + c` (proved through the bridge, not bitwise) |
| `add_zero` | `a + 0 == a` |
| `shl_put`, `shl_nat` | `to_nat(shl a) + top·P == 2A` |
| `shr_pad`, `shr_nat` | `lsb + 2·to_nat(shr a) == A` |
| `cmp_nat` | `Word.cmp(a, b) == Nat.cmp(A, B)` |
| `mul_go_nat`, `mul_nat` | `to_nat(a * b) + mulq·P == A·B`: the product, less its wraps |
| `mul_exact` | if `A·B < P` then `to_nat(a * b) == A·B` (no overflow) |
| `mul_comm` | `a * b == b * a` (through the bridge) |

**U32** (what Bend programs use): `u32_{xor,and,or}_{comm,assoc}`,
`u32_add_assoc`, `u32_mul_comm`, `u32_add_zero`, `u32_xor_zero`, `u32_xor_self`,
`u32_not_not`, `u32_to_nat_inj`, `u32_sub_nat`, `u32_cmp_nat`, `u32_lt_nat`,
`u32_le_nat`.

## Using it

Import both the claims and the proofs; Bend refuses to use a law whose proof
is not in scope ("an unfilled law is a dead claim"). From BendHub, no clone
needed (the version at the first commit, 39 laws):

```python
import 0x340691c4c9cfde2764a3ed46e48d644a/LAWS.bend as WL
import 0x340691c4c9cfde2764a3ed46e48d644a/PROOF.bend as WP
import 0x340691c4c9cfde2764a3ed46e48d644a/nat.bend as N
```

or from a checkout, `import ../wordlib/LAWS.bend as WL` and so on. Then:

```python
# U32 subtraction that provably does not wrap
WL.u32_sub_nat(bal, amt, d, gap)  # : {U32.to_nat(bal - amt) == d}
```

`examples/withdraw` proves that a guarded withdrawal never wraps: the U32
guard becomes Nat order (`u32_le_nat`), the gap is named (`N.le_sub`), and the
U32 result is exactly that gap (`u32_sub_nat`).

## `ac`: sums by reflection

Bend has no tactics, so rearranging `a + (b + c)` into `c + (b + a)` normally
takes a chain of rewrites. `ac.bend` makes it one call. An `Expr` is a sum of
atoms with doubling; `norm` counts each atom; `ac` is proved sound once, so
Bend checks `{norm(e1) == norm(e2)}` by computation and returns the goal:

```python
A.ac([a, b, c], A.EAdd{A.EAtom{0n}, A.EAdd{A.EAtom{1n}, A.EAtom{2n}}},
                A.EAdd{A.EAtom{2n}, A.EAdd{A.EAtom{1n}, A.EAtom{0n}}}, {==})
# : {Nat.add(a, Nat.add(b, c)) == Nat.add(c, Nat.add(b, a))}
```

Atoms can be any terms and numerals ride along as atoms (`[x, y, 1n]`). A
false identity fails with the two count vectors, e.g. `[1n, 1n]` vs `[2n]`.

## How it is verified

`./check.sh` runs:

1. **The proof gate**: `bend PROOF.bend` and the example's `PROOF.bend` print
   "All terms check." (about 0.3s).
2. **ac tests**: true identities check; a false one is rejected.
3. **Mutation tests** (`tests/mutants.py`): 32 planted bugs in laws,
   definitions, the `ac` normalizer, `Nat` lemmas and the example program.
   Every one must make the checker fail. A surviving mutant means a proof is
   weaker than it looks.
4. **Differential test** (`tools/diff_u32.py`): Bend compiles U32 ops to
   native C and JS, not to the bit-level definitions the proofs are about.
   The same inputs go through native C, JS, and the checker's evaluation of
   Base's definitions, and all are compared with Python's mod-2^32 model over
   add, sub, mul, and, or, xor, div, mod, shifts and comparisons, including
   edge cases (0, 2^31, 2^32-1, division by zero, shifts of 32 and over).
   A 4000-row sweep (`SEED=7 python3 tools/diff_u32.py 4000 40`): 96,480
   comparisons, 0 mismatches.
5. **Property tests** (bendcheck's `lawcheck`, when bendcheck is cloned next
   to wordlib or `BENDCHECK` points to it): each law becomes random tests at
   several widths, with hypotheses as preconditions. Proved laws cannot fail,
   so this checks the compiled code against the definitions and screens new
   laws before anyone proves them. Across widths 1 to 16 the 44 laws give 157
   properties: 153 pass and 4 give up, because their preconditions (two random
   words with the same value, a 16-bit product that fits) almost never hold.

## Notes on Bend 2.0.28

- A JS build of a `do` block with a few hundred steps overflows node's parser
  stack on load (`RangeError: Maximum call stack size exceeded`); splitting
  it into smaller defs works around it.
- Laws whose statement holds 2^32 (like `mul_nat` at `n = 32n`) cannot be
  checked yet: conversion normalizes before comparing, so even identical
  `W.pow2(32n)` terms expand to a unary 2^32 and overflow the stack
  (bendlang/bend#1071). The width-generic laws are unaffected.
- Compiled `Nat` is a native word that stops the program past 2^48-1; the laws
  hold for all `Nat`, and the runtime fails loudly rather than wrapping.

## License

MIT. See `LICENSE`.

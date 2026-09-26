# wordlib

A verified standard library for Bend: proved laws, proof automation and
property-based testing, so Bend programs ship with guarantees.

Bend promises code that is proved correct. wordlib is the library that makes
that cheap: laws you import instead of re-proving, a prover for the tedious
steps, and tests that catch a false law before you spend time proving it.

Today: 70 laws. 44 on machine words (`Word(n)` at every width, and `U32`),
with the bridge from machine arithmetic to `Nat`; 26 on lists, including
that Base's merge sort is a permutation; and `ac`, a prover for sums.
Every law is also property-tested by
[bendcheck](https://github.com/Yazington/bendcheck)'s `lawcheck`, a companion
library, so a wrong law fails with a counterexample in seconds instead of
stalling a proof.

Built against Bend 2.0.28. `./check.sh` runs every check.

## Layout

| Path | Contents |
|---|---|
| `LAWS.bend` | the word laws (44) |
| `PROOF.bend` | the index of their proofs; `bend PROOF.bend` checks them all |
| `word.bend` | the vocabulary the laws use: `b2n`, `scale`, `pow2`, `carry`, `top`, `lsb`, `mulq` |
| `proofs/` | the word proofs by topic: `bits`, `add`, `sub`, `shift`, `compare`, `mul`, `u32`, and `wrap` (arithmetic of values below 2^n, which the others share) |
| `lib/` | general lemmas: `nat` (addition, cancellation, clashes, order), `nat_mul` (multiplication), `ac` (a prover for sums) |
| `list/` | the list laws (26): `LAWS.bend`, `PROOF.bend`, `proofs/` (`append`, `reverse`, `index`, `build`, `sort`), `count.bend` (counting and the U32 sort), `CONJECTURES.bend` (tested, not yet proved) |
| `examples/withdraw/` | a U32 program whose safety is proved with wordlib |
| `tests/`, `tools/` | the ac tests, the mutation tests and the U32 differential tester |

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

**Lists** (`list/`, for every quantity and element type):

| Law | Statement |
|---|---|
| `append_nil`, `append_assoc` | `xs ++ [] == xs`, `(xs ++ ys) ++ zs == xs ++ (ys ++ zs)` |
| `length_append` | `length(xs ++ ys) == length xs + length ys` |
| `concat_append` | `concat(xss ++ yss) == concat xss ++ concat yss` |
| `reverse_go`, `reverse_append` | `reverse(xs ++ ys) == reverse ys ++ reverse xs` |
| `reverse_reverse`, `length_reverse` | `reverse(reverse xs) == xs`; the length is kept |
| `take_drop` | `take(xs, n) ++ drop(xs, n) == xs` |
| `length_take`, `length_drop` | `min(n, length xs)` and `length xs - n` elements |
| `length_set`, `get_set` | `set` keeps the length; `get(set(xs, n, x), n) == Some x` when `n < length xs` |
| `length_zip`, `length_range`, `length_replicate` | `min` of the lengths; `n`; `n` |

**Sorting** (Base's `List.sort` on `U32` by `<=`, a bottom-up merge sort with
fuel):

| Law | Statement |
|---|---|
| `sort_perm` | `count(x, sort xs) == count(x, xs)` for every `x`: sort is a permutation |
| `sort_length` | `length(sort xs) == length xs` |
| `merge_count`, `pass_count`, `sort_go_count`, `sort_runs`, `sort_count` | each stage keeps the counts |
| `count_append`, `count_reverse_go`, `count_all` | the counting lemmas |

The permutation proof holds whatever the fuel does: a merge step only moves
an element from an input to the accumulator. Since the next state depends on
a comparison the proof cannot evaluate, it builds the induction hypothesis
for both outcomes and lets the comparison pick. That the result is *sorted*
needs the fuel to suffice and is still a conjecture: `list/CONJECTURES.bend`
states it (with idempotence, and sorting a sorted list), and `lawcheck` tests
it on every run.

A list of arbitrary elements is affine: a proof may use it once. So the
proofs never call two lemmas on the same list; helpers carry the second use
in an accumulator instead (reversing twice is `rev_rev(xs, acc)`, and the
length of a reversal carries the accumulator's length as a separate `Nat`).
`lawcheck` caught the first draft of `reverse_append`, which kept the order
of the parts, at `([0], [1])` before any proof was attempted.

## Using it

Import both the claims and the proofs; Bend refuses to use a law whose proof
is not in scope ("an unfilled law is a dead claim"). From BendHub, no clone
needed (44 laws):

```python
import 0xb13667d52aa56e002b4d09883d7fce3e/LAWS.bend as WL
import 0xb13667d52aa56e002b4d09883d7fce3e/PROOF.bend as WP
import 0xb13667d52aa56e002b4d09883d7fce3e/nat.bend as N
```

That release predates the `lib/` layout and the list laws. From a checkout:

```python
import ../wordlib/LAWS.bend as WL
import ../wordlib/PROOF.bend as WP
import ../wordlib/lib/nat.bend as N
```

Then:

```python
# U32 subtraction that provably does not wrap
WL.u32_sub_nat(bal, amt, d, gap)  # : {U32.to_nat(bal - amt) == d}
```

`examples/withdraw` proves that a guarded withdrawal never wraps: the U32
guard becomes Nat order (`u32_le_nat`), the gap is named (`N.le_sub`), and the
U32 result is exactly that gap (`u32_sub_nat`).

## `ac`: sums by reflection

Bend has no tactics, so rearranging `a + (b + c)` into `c + (b + a)` normally
takes a chain of rewrites. `lib/ac.bend` makes it one call. An `Expr` is a sum
of atoms with doubling; `norm` counts each atom; `ac` is proved sound once, so
Bend checks `{norm(e1) == norm(e2)}` by computation and returns the goal:

```python
A.ac([a, b, c], A.add(A.x0(), A.add(A.x1(), A.x2())),
                A.add(A.x2(), A.add(A.x1(), A.x0())), {==})
# : {(a + (b + c) : Nat) == (c + (b + a) : Nat) : Nat}
```

`x0()` to `x7()` are the atoms, in the order of the list; `add`, `dbl` and
`zero` stand for `Nat.add`, `Nat.double` and `0n`.

Atoms can be any terms and numerals ride along as atoms (`[x, y, 1n]`). A
false identity fails with the two count vectors, e.g. `[1n, 1n]` vs `[2n]`.

## Writing proofs

- State with operators: `(a + (b + c) : Nat)` is `Nat.add(a, Nat.add(b, c))`.
- A rewrite `%e : P`, with `e : {a == b}`, takes the goal `P[b/_]` to
  `P[a/_]`. Name long terms with lets (`+T = Word.to_nat(p, t)`) so each `P`
  fits on a line.
- Give every helper a one-line comment with its statement in plain math.
- A list of arbitrary elements is affine: a proof may use it once. Carry the
  second use in an accumulator, or in a separate `Nat`, instead of calling a
  second lemma on the same list.
- When the next step depends on a value the proof cannot compute (a carry, a
  comparison), take the induction hypothesis as a function of that value
  (`ih: @k: Bool -> ...`), or take one hypothesis per outcome and match.
- Keep lines within 100 columns.

## How it is verified

`./check.sh` runs:

1. **The proof gates**: `bend PROOF.bend`, `bend list/PROOF.bend` and the
   example's `PROOF.bend` print "All terms check." (about a quarter second
   each).
2. **ac tests**: true identities check; a false one is rejected.
3. **Mutation tests** (`tests/mutants.py`): 43 planted bugs in laws,
   definitions, the `ac` normalizer, the `Nat` lemmas, the proof index, the list
   and sort laws, and the example program.
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
   laws before anyone proves them. Across widths 1 to 16 the 44 word laws give
   157 properties: 153 pass and 4 give up, because their preconditions (two
   random words with the same value, a 16-bit product that fits) almost never
   hold. The 26 list laws, tested at `U32` elements, all pass, and so do the
   3 sorting conjectures. `./check.sh` runs a quicker pass (widths 1, 3 and 8):
   130 properties pass and 2 give up.

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

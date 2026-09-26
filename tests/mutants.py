#!/usr/bin/env python3
"""Mutation tests: each mutant plants one bug in a copy of the library.
The proof gates must reject every mutant; a mutant that checks means a
proof or law is weaker than it looks. A mutant whose pattern no longer
occurs is reported STALE, so the list cannot rot silently."""
import os, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BEND = os.path.expanduser("~/.bend/bin/bend")
GATES = ["PROOF.bend", "list/PROOF.bend", "examples/withdraw/PROOF.bend"]

# (name, file, old, new): old must occur in file
MUTANTS = [
    # the word laws
    ("law: adc_nat drops the carry-out", "LAWS.bend",
     "  {(Word.to_nat(n, Word.adc(n, a, b, False{}, c)) + W.scale(W.carry(n, a, b, c), "
     "W.pow2(n)) : Nat)",
     "  {(Word.to_nat(n, Word.adc(n, a, b, False{}, c)) + 0n : Nat)"),
    ("law: adc_nat forgets the carry-in", "LAWS.bend",
     "(Word.to_nat(n, b) + W.b2n(c))", "Word.to_nat(n, b)"),
    ("law: xor_comm claims xor == and", "LAWS.bend",
     "{Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}",
     "{Word.xor(n, a, b) == Word.and(n, b, a) : Word(n)}"),
    ("law: add_zero claims a + 0 == not a", "LAWS.bend",
     "{Word.add(n, a, Word.zero(n)) == a : Word(n)}",
     "{Word.add(n, a, Word.zero(n)) == Word.not(n, a) : Word(n)}"),
    ("law: De Morgan with and", "LAWS.bend",
     "== Word.or(n, Word.not(n, a), Word.not(n, b)) : Word(n)}",
     "== Word.and(n, Word.not(n, a), Word.not(n, b)) : Word(n)}"),
    ("law: not_nat without the +1", "LAWS.bend",
     "{1n+(Word.to_nat(n, w) + Word.to_nat(n, Word.not(n, w)) : Nat) == W.pow2(n) : Nat}",
     "{(Word.to_nat(n, w) + Word.to_nat(n, Word.not(n, w)) : Nat) == W.pow2(n) : Nat}"),
    ("law: to_nat_inj concludes a == not b", "LAWS.bend",
     "  {a == b : Word(n)}", "  {a == Word.not(n, b) : Word(n)}"),
    ("law: add_exact off by one", "LAWS.bend",
     "  {Word.to_nat(n, Word.add(n, a, b)) == (Word.to_nat(n, a) + Word.to_nat(n, b) : Nat) : Nat}",
     "  {Word.to_nat(n, Word.add(n, a, b)) == 1n+(Word.to_nat(n, a) + Word.to_nat(n, b) : Nat) : "
     "Nat}"),
    ("law: add_assoc with a in place of c", "LAWS.bend",
     "{Word.add(n, a, Word.add(n, b, c)) == Word.add(n, Word.add(n, a, b), c) : Word(n)}",
     "{Word.add(n, a, Word.add(n, b, c)) == Word.add(n, Word.add(n, a, b), a) : Word(n)}"),
    ("law: adc_sub drops the flip", "LAWS.bend",
     "{Word.adc(n, a, Word.not(n, b), False{}, c) == Word.adc(n, a, b, True{}, c) : Word(n)}",
     "{Word.adc(n, a, Word.not(n, b), False{}, c) == Word.adc(n, a, b, False{}, c) : Word(n)}"),
    ("law: sub_nat off by one", "LAWS.bend",
     "{Word.to_nat(n, Word.sub(n, a, b)) == d : Nat}",
     "{Word.to_nat(n, Word.sub(n, a, b)) == 1n+d : Nat}"),
    ("law: shl_put without the dropped bit", "LAWS.bend",
     "  {(Word.to_nat(n, Word.shl.put(n, c, w)) + W.scale(W.top(n, c, w), W.pow2(n)) : Nat)",
     "  {(Word.to_nat(n, Word.shl.put(n, c, w)) + 0n : Nat)"),
    ("law: shr_nat forgets the lost bit", "LAWS.bend",
     "  {(W.b2n(W.lsb(n, w)) + Nat.double(Word.to_nat(n, Word.shr(n, w))) : Nat)",
     "  {(0n + Nat.double(Word.to_nat(n, Word.shr(n, w))) : Nat)"),
    ("law: cmp_nat with swapped values", "LAWS.bend",
     "{Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}",
     "{Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, b), Word.to_nat(n, a)) : Cmp}"),
    ("law: mul_exact off by one", "LAWS.bend",
     "  {Word.to_nat(n, Word.mul(n, a, b)) == (Word.to_nat(n, a) * Word.to_nat(n, b) : Nat) : Nat}",
     "  {Word.to_nat(n, Word.mul(n, a, b)) == 1n+(Word.to_nat(n, a) * Word.to_nat(n, b) : Nat) : "
     "Nat}"),
    ("law: mul_comm claims a * b == a * a", "LAWS.bend",
     "  {Word.mul(n, a, b) == Word.mul(n, b, a) : Word(n)}",
     "  {Word.mul(n, a, b) == Word.mul(n, a, a) : Word(n)}"),
    ("law: u32_lt_nat is really <=", "LAWS.bend",
     "  {(a < b : U32) == (U32.to_nat(a) < U32.to_nat(b) : Nat) : Bool}",
     "  {(a < b : U32) == (U32.to_nat(a) <= U32.to_nat(b) : Nat) : Bool}"),
    ("law: u32_xor_self yields a", "LAWS.bend",
     "  {(a .^. a : U32) == 0 : U32}", "  {(a .^. a : U32) == a : U32}"),
    # the vocabulary
    ("def: majority wrong on (F, T)", "word.bend",
     "    case False{} True{} _:\n      c", "    case False{} True{} _:\n      False{}"),
    ("def: pow2 forgets to double", "word.bend", "Nat.double(pow2(p))", "pow2(p)"),
    ("def: top ignores the word", "word.bend",
     "        case WCon{b, t}:\n          top(p, b, t)", "        case WCon{b, t}:\n          c"),
    ("def: mulq forgets the adder's carry", "word.bend",
     "Word.add(n, acc, b)) + (lost + wrap) : Nat)", "Word.add(n, acc, b)) + lost : Nat)"),
    # the lemma libraries
    ("ac: the normalizer forgets doubling", "lib/ac.bend",
     "      +v = norm(a)\n      vadd(v, v)", "      norm(a)"),
    ("ac: vadd drops the left tail", "lib/ac.bend",
     "    case Con{a, us} Nil{}:\n      Con{a, us}", "    case Con{a, us} Nil{}:\n      Nil{}"),
    ("ac: unit puts the 1 one slot late", "lib/ac.bend",
     "      Con{1n, Nil{}}", "      Con{0n, Con{1n, Nil{}}}"),
    ("nat: add_assoc claims a + (b + c) == (a + c) + a", "lib/nat.bend",
     "  {(a + (b + c) : Nat) == ((a + b) + c : Nat) : Nat}:",
     "  {(a + (b + c) : Nat) == ((a + c) + a : Nat) : Nat}:"),
    ("nat: is_succ sends 0 to Unit", "lib/nat.bend",
     "def is_succ(n: Nat) -> Type:\n  match n:\n    case 0n:\n      Empty",
     "def is_succ(n: Nat) -> Type:\n  match n:\n    case 0n:\n      Unit"),
    ("nat: pred is the identity", "lib/nat.bend",
     "    case 1n+p:\n      p\n\n# 1 + x == 1 + y",
     "    case 1n+p:\n      1n+p\n\n# 1 + x == 1 + y"),
    ("nat: le_sub with the gap reversed", "lib/nat.bend",
     "  {y == (x + Nat.sub(y, x) : Nat) : Nat}:", "  {y == (x + Nat.sub(x, y) : Nat) : Nat}:"),
    ("nat_mul: mul_assoc claims a(bc) == (ab)a", "lib/nat_mul.bend",
     "  {(a * (b * c) : Nat) == ((a * b) * c : Nat) : Nat}:",
     "  {(a * (b * c) : Nat) == ((a * b) * a : Nat) : Nat}:"),
    # the proof index
    ("PROOF.bend forgets the U32 proofs (nothing else imports them)", "PROOF.bend",
     "import ./proofs/u32.bend as U32s\n", ""),
    # the list laws
    ("list: reverse_append keeps the order", "list/LAWS.bend",
     "    == List.append(a, A, List.reverse(a, A, ys), List.reverse(a, A, xs)) : List<a, A>}",
     "    == List.append(a, A, List.reverse(a, A, xs), List.reverse(a, A, ys)) : List<a, A>}"),
    ("list: length_take uses max", "list/LAWS.bend",
     "== Nat.min(n, List.length(a, A, xs)) : Nat}", "== Nat.max(n, List.length(a, A, xs)) : Nat}"),
    ("list: get_set reads index 0", "list/LAWS.bend",
     "{List.get(a, A, List.set(a, A, xs, n, x), n) == Some{x} : Maybe<a, A>}",
     "{List.get(a, A, List.set(a, A, xs, n, x), 0n) == Some{x} : Maybe<a, A>}"),
    ("list: get_set without its bound", "list/LAWS.bend",
     "  for h: {Nat.is_lt(n, List.length(a, A, xs)) == True{} : Bool}\n", ""),
    ("list: length_range off by one", "list/LAWS.bend",
     "{List.length(&2, Nat, List.range(n)) == n : Nat}",
     "{List.length(&2, Nat, List.range(n)) == 1n+n : Nat}"),
    ("list: append_nil claims xs ++ [] == reverse xs", "list/LAWS.bend",
     "{List.append(a, A, xs, Nil{}) == xs : List<a, A>}",
     "{List.append(a, A, xs, Nil{}) == List.reverse(a, A, xs) : List<a, A>}"),
    ("sort: merge_count forgets the accumulator", "list/LAWS.bend",
     "    == (C.count(m, acc) + (C.count(m, xs) + C.count(m, ys)) : Nat) : Nat}",
     "    == (C.count(m, xs) + C.count(m, ys) : Nat) : Nat}"),
    ("sort: sort_perm compares with another value", "list/LAWS.bend",
     "{C.count(Some{x}, C.sort(xs)) == C.count(Some{x}, xs) : Nat}",
     "{C.count(Some{x}, C.sort(xs)) == C.count(Some{0}, xs) : Nat}"),
    ("sort: counting everything counts double", "list/count.bend",
     "    case None{}:\n      1n\n", "    case None{}:\n      2n\n"),
    ("sort: the U32 sort sorts by >=", "list/count.bend",
     "  List.sort(~U32, ~U32.is_le, xs)", "  List.sort(~U32, ~U32.is_ge, xs)"),
    # the example
    ("example: a covered withdrawal adds", "examples/withdraw/main.bend",
     "      (bal - amt : U32)", "      (bal + amt : U32)"),
    ("example: the guard compares the wrong way", "examples/withdraw/main.bend",
     "  withdraw.go((amt <= bal : U32), bal, amt)", "  withdraw.go((bal <= amt : U32), bal, amt)"),
]


def check(d):
    for g in GATES:
        r = subprocess.run([BEND, g], cwd=d, capture_output=True, text=True,
                           env={**os.environ, "BEND_NO_TELEMETRY": "1"}, timeout=300)
        if "All terms check." not in r.stdout + r.stderr:
            return False
    return True


def main():
    if not check(ROOT):
        print("baseline does not check; fix it first")
        return 1
    bad = 0
    for name, f, old, new in MUTANTS:
        with tempfile.TemporaryDirectory() as t:
            d = os.path.join(t, "w")
            shutil.copytree(ROOT, d, ignore=shutil.ignore_patterns(".git", "tests", "tools"))
            src = open(os.path.join(d, f)).read()
            if old not in src:
                print(f"STALE    {name}: pattern not found in {f}")
                bad += 1
                continue
            open(os.path.join(d, f), "w").write(src.replace(old, new, 1))
            if check(d):
                print(f"SURVIVED {name}")
                bad += 1
            else:
                print(f"killed   {name}")
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants killed")
    return 1 if bad else 0


sys.exit(main())

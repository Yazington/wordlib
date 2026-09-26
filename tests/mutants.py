#!/usr/bin/env python3
"""Mutation tests: each mutant plants one bug in a copy of the library.
The checker must reject every mutant; a mutant that checks means a proof
or law is weaker than it looks."""
import os, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BEND = os.path.expanduser("~/.bend/bin/bend")
GATES = ["PROOF.bend", "examples/withdraw/PROOF.bend"]

# (name, file, old, new): old must occur in file
MUTANTS = [
    ("law: drop the carry-out term", "LAWS.bend",
     "W.scale(W.carry(n, a, b, c), W.pow2(n))", "0n"),
    ("law: forget the carry-in", "LAWS.bend",
     "Nat.add(Word.to_nat(n, b), W.b2n(c))", "Word.to_nat(n, b)"),
    ("def: majority wrong on (F, T)", "word.bend",
     "    case False{} True{} _:\n      c", "    case False{} True{} _:\n      False{}"),
    ("def: pow2 forgets to double", "word.bend",
     "Nat.double(pow2(p))", "pow2(p)"),
    ("law: xor_comm claims xor == and", "LAWS.bend",
     "{Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}",
     "{Word.xor(n, a, b) == Word.and(n, b, a) : Word(n)}"),
    ("law: add_zero claims a + 0 == not a", "LAWS.bend",
     "{Word.add(n, a, Word.zero(n)) == a : Word(n)}",
     "{Word.add(n, a, Word.zero(n)) == Word.not(n, a) : Word(n)}"),
    ("law: De Morgan with and", "LAWS.bend",
     "== Word.or(n, Word.not(n, a), Word.not(n, b)) : Word(n)}",
     "== Word.and(n, Word.not(n, a), Word.not(n, b)) : Word(n)}"),
    ("ac: normalizer forgets doubling", "ac.bend",
     "      +v = norm(a)\n      vadd(v, v)", "      norm(a)"),
    ("ac: vadd drops the left tail", "ac.bend",
     "    case Con{a, us} Nil{}:\n      Con{a, us}", "    case Con{a, us} Nil{}:\n      Nil{}"),
    ("ac: unit puts the 1 one slot late", "ac.bend",
     "      Con{1n, Nil{}}", "      Con{0n, Con{1n, Nil{}}}"),
    ("nat: add_assoc claims a+(b+c) == (a+c)+b", "nat.bend",
     "-> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}",
     "-> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, c), a) : Nat}"),
("law: not_nat without the +1", "LAWS.bend",
     "{1n+Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))) == W.pow2(n) : Nat}",
     "{Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))) == W.pow2(n) : Nat}"),
    ("law: to_nat_inj concludes a == not b", "LAWS.bend",
     "  {a == b : Word(n)}", "  {a == Word.not(n, b) : Word(n)}"),
    ("law: adc_sub drops the flip", "LAWS.bend",
     "{Word.adc(n, a, Word.not(n, b), False{}, c) == Word.adc(n, a, b, True{}, c) : Word(n)}",
     "{Word.adc(n, a, Word.not(n, b), False{}, c) == Word.adc(n, a, b, False{}, c) : Word(n)}"),
    ("law: sub_nat off by one", "LAWS.bend",
     "{Word.to_nat(n, Word.sub(n, a, b)) == d : Nat}", "{Word.to_nat(n, Word.sub(n, a, b)) == 1n+d : Nat}"),
    ("law: add_assoc with a in place of c", "LAWS.bend",
     "{Word.add(n, a, Word.add(n, b, c)) == Word.add(n, Word.add(n, a, b), c) : Word(n)}",
     "{Word.add(n, a, Word.add(n, b, c)) == Word.add(n, Word.add(n, a, b), a) : Word(n)}"),
    ("nat: disc motive sends 0 to Unit", "nat.bend",
     "    case 0n:\n      Empty\n", "    case 0n:\n      Unit\n"),
    ("nat: pred is the identity", "nat.bend",
     "    case 1n+p:\n      p\n\ndef succ_inj", "    case 1n+p:\n      1n+p\n\ndef succ_inj"),
    ("law: shl_put without the dropped bit", "LAWS.bend",
     "{Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), W.scale(W.top(n, c, w), W.pow2(n))) ==",
     "{Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), 0n) =="),
    ("law: shr_nat forgets the lost bit", "LAWS.bend",
     "{Nat.add(W.b2n(W.lsb(n, w)), Nat.double(Word.to_nat(n, Word.shr(n, w)))) == Word.to_nat(n, w) : Nat}",
     "{Nat.double(Word.to_nat(n, Word.shr(n, w))) == Word.to_nat(n, w) : Nat}"),
    ("law: cmp_nat with swapped values", "LAWS.bend",
     "{Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}",
     "{Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, b), Word.to_nat(n, a)) : Cmp}"),
    ("law: add_exact off by one", "LAWS.bend",
     "  {Word.to_nat(n, Word.add(n, a, b)) == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}",
     "  {Word.to_nat(n, Word.add(n, a, b)) == 1n+Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}"),
    ("def: top ignores the word", "word.bend",
     "        case WCon{b, t}:\n          top(p, b, t)", "        case WCon{b, t}:\n          c"),
    ("law: u32_lt_nat is really le", "LAWS.bend",
     "{U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}",
     "{U32.is_lt(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}"),
    ("law: u32_xor_self yields a", "LAWS.bend",
     "  {U32.xor(a, a) == 0 : U32}", "  {U32.xor(a, a) == a : U32}"),
    ("nat: le_sub with the gap reversed", "nat.bend",
     "-> {y == Nat.add(x, Nat.sub(y, x)) : Nat}:", "-> {y == Nat.add(x, Nat.sub(x, y)) : Nat}:"),
    ("example: covered withdraw adds", "examples/withdraw/main.bend",
     "      (bal - amt : U32)", "      (bal + amt : U32)"),
    ("example: guard compares the wrong way", "examples/withdraw/main.bend",
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
        print("baseline does not check; fix it first"); return 1
    bad = 0
    for name, f, old, new in MUTANTS:
        with tempfile.TemporaryDirectory() as t:
            d = os.path.join(t, "w")
            shutil.copytree(ROOT, d, ignore=shutil.ignore_patterns(".git", "tests", "tools"))
            src = open(os.path.join(d, f)).read()
            if old not in src:
                print(f"STALE   {name}: pattern not found in {f}"); bad += 1; continue
            open(os.path.join(d, f), "w").write(src.replace(old, new, 1))
            if check(d):
                print(f"SURVIVED {name}"); bad += 1
            else:
                print(f"killed   {name}")
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants killed")
    return 1 if bad else 0

sys.exit(main())

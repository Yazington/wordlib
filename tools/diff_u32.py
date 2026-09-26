#!/usr/bin/env python3
"""Differential test for U32: the same (a, b, k) rows through Bend's
native C build, its JS build, and the checker's evaluation of Base's
bit-level definitions, each compared with Python's mod-2^32 model.
Usage: diff_u32.py [rows] [checker_rows]"""
import os, random, subprocess, sys, tempfile

BEND = os.path.expanduser("~/.bend/bin/bend")
ENV = {**os.environ, "BEND_NO_TELEMETRY": "1"}
M = 1 << 32
OPS = ["add", "sub", "mul", "and", "or", "xor", "div", "mod", "shln", "shrn", "lt", "le"]

def model(a, b, k):
    return [(a + b) % M, (a - b) % M, (a * b) % M, a & b, a | b, a ^ b,
            0 if b == 0 else a // b, a if b == 0 else a % b,
            0 if k >= 32 else (a << k) % M, 0 if k >= 32 else a >> k,
            a < b, a <= b]

def rows(n, seed=1):
    edge = [0, 1, 2, 3, 7, 10, 255, 256, 65535, 65536, 2**31 - 1, 2**31, 2**31 + 1, M - 2, M - 1]
    r = random.Random(seed)
    out = [(a, b, k) for a in edge for b in edge for k in (0, 1, 31, 32, 33)][:n // 2]
    while len(out) < n:
        a = r.choice([r.randrange(M), r.randrange(256), M - 1 - r.randrange(256)])
        b = r.choice([r.randrange(M), r.randrange(1, 17), 0])
        out.append((a, b, r.randrange(40)))
    return out

ROW = '''def row(+a: U32, +b: U32, +k: Nat) -> String:
  U32.show((a + b : U32)) ++ " " ++ U32.show((a - b : U32)) ++ " " ++ U32.show((a * b : U32)) ++ " "
    ++ U32.show((a .&. b : U32)) ++ " " ++ U32.show((a .|. b : U32)) ++ " " ++ U32.show((a .^. b : U32)) ++ " "
    ++ U32.show((a / b : U32)) ++ " " ++ U32.show((a % b : U32)) ++ " "
    ++ U32.show(U32.shln(a, k)) ++ " " ++ U32.show(U32.shrn(a, k)) ++ " "
    ++ Bool.show((a < b : U32)) ++ " " ++ Bool.show((a <= b : U32))
'''

def native_src(rs, chunk=20):
    # long do-blocks overflow node's parser in the JS build: chunk them
    parts, calls = [], []
    for i in range(0, len(rs), chunk):
        body = "\n".join(f"    IO.print(row({a}, {b}, {k}n))" for a, b, k in rs[i:i + chunk])
        parts.append(f"def part{i // chunk}() -> IO(Unit):\n  do IO<Unit>:\n{body}\n")
        calls.append(f"    part{i // chunk}()")
    main = "def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(calls) + "\n"
    return f"import Base\n\n{ROW}\n" + "\n".join(parts) + "\n" + main

def checker_src(rs):
    parts = ' ++ "|" ++ '.join(f"row({a}, {b}, {k}n)" for a, b, k in rs)
    return f"import Base\n\n{ROW}\ndef main() -> String:\n  {parts}\n"

def parse(line):
    xs = line.split()
    return [int(x) for x in xs[:10]] + [x == "True" for x in xs[10:]]

def compare(name, rs, lines):
    bad = 0
    if len(lines) != len(rs):
        print(f"{name}: expected {len(rs)} rows, got {len(lines)}"); return len(rs)
    for (a, b, k), line in zip(rs, lines):
        got, want = parse(line), model(a, b, k)
        for op, g, w in zip(OPS, got, want):
            if g != w:
                bad += 1
                if bad <= 10: print(f"{name}: {op}({a}, {b}, k={k}) = {g}, model says {w}")
    print(f"{name}: {len(rs)} rows x {len(OPS)} ops, {bad} mismatches")
    return bad

def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, env=ENV, **kw)
    if r.returncode != 0:
        print(f"$ {' '.join(cmd)}\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
        raise SystemExit(1)
    return r.stdout

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    nc = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    rs = rows(n, int(os.environ.get("SEED", "1")))
    bad = 0
    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "diff.bend")
        open(src, "w").write(native_src(rs))
        run([BEND, src, "-o", os.path.join(d, "diff")])
        out = run([os.path.join(d, "diff")])
        bad += compare("native C", rs, out.strip().splitlines())
        run([BEND, src, "-o", os.path.join(d, "diff.js")])
        out = run(["node", os.path.join(d, "diff.js")])
        bad += compare("JS", rs, out.strip().splitlines())
        # the checker normalizes main with Base's bit-level definitions
        crs = rs[:nc // 2] + rs[-(nc - nc // 2):]
        open(src, "w").write(checker_src(crs))
        r = subprocess.run([BEND, src], capture_output=True, text=True, env=ENV, timeout=600)
        txt = r.stdout.strip().strip('"')
        bad += compare("checker (definitions)", crs, txt.split("|"))
    print("OK" if bad == 0 else "FAIL")
    return 1 if bad else 0

sys.exit(main())

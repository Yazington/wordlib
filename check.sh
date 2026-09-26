#!/bin/sh
# Runs every check: the proof gate, the ac tests (one must pass, one must
# fail), the mutation tests and a quick U32 differential test.
set -u
export BEND_NO_TELEMETRY=1
BEND=${BEND:-$HOME/.bend/bin/bend}
cd "$(dirname "$0")"
fail=0
step() { printf '%-34s' "$1"; }
ok() { echo "ok"; }
no() { echo "FAIL"; fail=1; }

step "proofs (bend PROOF.bend)"
out=$("$BEND" PROOF.bend 2>&1); echo "$out" | grep -q "All terms check." && ok || { no; echo "$out" | head -20; }

step "example: withdraw laws"
out=$("$BEND" examples/withdraw/PROOF.bend 2>&1); echo "$out" | grep -q "All terms check." && ok || { no; echo "$out" | head -20; }

step "ac: true identities check"
out=$("$BEND" tests/ac_ok.bend --check-only 2>&1); echo "$out" | grep -q "All terms check." && ok || { no; echo "$out" | head -20; }

step "ac: false identity is rejected"
out=$("$BEND" tests/ac_bad.bend --check-only 2>&1); echo "$out" | grep -q "All terms check." && no || ok

step "mutation tests"
out=$(python3 tests/mutants.py 2>&1); [ $? -eq 0 ] && echo "ok ($(echo "$out" | tail -1))" || { no; echo "$out"; }

step "U32 differential (C, JS, checker)"
out=$(python3 tools/diff_u32.py 200 8 2>&1); [ $? -eq 0 ] && ok || { no; echo "$out"; }

[ $fail -eq 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail

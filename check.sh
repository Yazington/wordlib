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

step "list laws"
out=$("$BEND" list/PROOF.bend 2>&1); echo "$out" | grep -q "All terms check." && ok || { no; echo "$out" | head -20; }

step "ac: true identities check"
out=$("$BEND" tests/ac_ok.bend --check-only 2>&1); echo "$out" | grep -q "All terms check." && ok || { no; echo "$out" | head -20; }

step "ac: false identity is rejected"
out=$("$BEND" tests/ac_bad.bend --check-only 2>&1); echo "$out" | grep -q "All terms check." && no || ok

step "mutation tests"
out=$(python3 tests/mutants.py 2>&1); [ $? -eq 0 ] && echo "ok ($(echo "$out" | tail -1))" || { no; echo "$out"; }

step "U32 differential (C, JS, checker)"
out=$(python3 tools/diff_u32.py 200 8 2>&1); [ $? -eq 0 ] && ok || { no; echo "$out"; }

step "property tests (bendcheck)"
BENDCHECK=${BENDCHECK:-../bendcheck}
if [ -f "$BENDCHECK/tools/lawcheck.py" ]; then
  out=$(python3 "$BENDCHECK/tools/lawcheck.py" LAWS.bend --widths 1,3,8 --count 100 2>&1); r1=$?
  out2=$(python3 "$BENDCHECK/tools/lawcheck.py" examples/withdraw/LAWS.bend 2>&1); r2=$?
  out3=$(python3 "$BENDCHECK/tools/lawcheck.py" list/LAWS.bend 2>&1); r3=$?
  out4=$(python3 "$BENDCHECK/tools/lawcheck.py" list/CONJECTURES.bend 2>&1); r4=$?
  if [ $r1 -eq 0 ] && [ $r2 -eq 0 ] && [ $r3 -eq 0 ] && [ $r4 -eq 0 ]; then
    echo "ok ($(echo "$out" | tail -1 | sed 's/lawcheck: //'))"
  else
    no; printf '%s\n%s\n%s\n%s\n' "$out" "$out2" "$out3" "$out4" | grep -A2 'FAILED\|build' | head -30
  fi
else
  echo "skipped (clone bendcheck next to wordlib, or set BENDCHECK)"
fi

[ $fail -eq 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail

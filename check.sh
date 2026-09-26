#!/bin/sh
# Runs every check: the proof gates, the ac tests (one must check, one must
# not), the mutation tests, a quick U32 differential test, and property tests
# of every law when bendcheck sits next to wordlib (or BENDCHECK points to it).
set -u
export BEND_NO_TELEMETRY=1
BEND=${BEND:-$HOME/.bend/bin/bend}
BENDCHECK=${BENDCHECK:-../bendcheck}
cd "$(dirname "$0")"
fail=0

step() { printf '%-36s' "$1"; }
pass() { echo "ok${1:+ ($1)}"; }
flunk() { echo "FAIL"; fail=1; printf '%s\n' "$1" | head -30; }

# gate NAME FILE: FILE must check
gate() {
  step "$1"
  out=$("$BEND" "$2" --check-only 2>&1)
  if echo "$out" | grep -q "All terms check."; then pass; else flunk "$out"; fi
}

# rejects NAME FILE: FILE must not check
rejects() {
  step "$1"
  out=$("$BEND" "$2" --check-only 2>&1)
  if echo "$out" | grep -q "All terms check."; then flunk "$2 checks"; else pass; fi
}

gate "proofs" PROOF.bend
gate "list proofs" list/PROOF.bend
gate "example: withdraw" examples/withdraw/PROOF.bend
gate "ac: true identities" tests/ac_ok.bend
rejects "ac: a false identity is rejected" tests/ac_bad.bend

step "mutation tests"
if out=$(python3 tests/mutants.py 2>&1); then pass "$(echo "$out" | tail -1)"; else flunk "$out"; fi

step "U32 differential (C, JS, checker)"
if out=$(python3 tools/diff_u32.py 200 8 2>&1); then pass; else flunk "$out"; fi

step "property tests (bendcheck)"
if [ -f "$BENDCHECK/tools/lawcheck.py" ]; then
  ok=0
  out=$(python3 "$BENDCHECK/tools/lawcheck.py" LAWS.bend --widths 1,3,8 --count 100 2>&1) || ok=1
  for f in examples/withdraw/LAWS.bend list/LAWS.bend list/CONJECTURES.bend; do
    more=$(python3 "$BENDCHECK/tools/lawcheck.py" "$f" 2>&1) || ok=1
    out="$out
$more"
  done
  passed=$(echo "$out" | grep -c '^  ok  ')
  gaveup=$(echo "$out" | grep -c '^  GAVE UP')
  if [ $ok -eq 0 ]; then
    pass "$passed passed, $gaveup gave up: precondition rarely held"
  else
    flunk "$(echo "$out" | grep -A2 'FAILED\|do not build')"
  fi
else
  echo "skipped (clone bendcheck next to wordlib, or set BENDCHECK)"
fi

[ $fail -eq 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $fail

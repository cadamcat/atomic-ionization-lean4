#!/usr/bin/env bash
# Build everything and require the main theorem and every package theorem to use only the standard axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
out=$(lake env lean Verification/Axioms.lean 2>&1)
printf '%s\n' "$out"
# Lean wraps long axiom lists over several lines: join them before checking each report.
reports=$(printf '%s' "$out" | tr '\n' ' ' | grep -oE "depends on axioms: \[[^]]*\]|does not depend on any axioms" || true)
n=$(printf '%s\n' "$reports" | grep -c . || true)
[ "$n" -eq 11 ] || { echo "verify: expected 11 axiom reports, got $n" >&2; exit 2; }
if printf '%s' "$out" | grep -q 'sorryAx'; then echo "verify: an open proof (sorryAx) remains" >&2; exit 2; fi
bad=$(printf '%s\n' "$reports" | sed -E 's/ +/ /g' | grep -vE "^depends on axioms: \[propext, Classical.choice, Quot.sound\]$|^does not depend on any axioms$" || true)
[ -z "$bad" ] || { echo "verify: a non-standard axiom appears: $bad" >&2; exit 2; }
echo "verify: OK"

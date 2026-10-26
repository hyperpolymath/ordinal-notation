#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-agda-trusted-base.sh — pin the Agda trusted base to exactly what is
# declared. The only postulates allowed are the two open order-type fidelity
# axioms in Ordinal/Buchholz/Fidelity.agda (`denotation`,
# `ordinal-upper-bound`; see Fidelity-OPEN-postulates.adoc). That file is the
# one entry for proof code in .cicd-hygiene-allow, and this check is the
# exact-count enforcement that entry requires: a third postulate block, a
# postulate anywhere else, or an escape pragma fails it.
#
# Usage: check-agda-trusted-base.sh [agda-root]   (default verification/proofs/agda)
set -euo pipefail

ROOT="${1:-verification/proofs/agda}"
ALLOWED="$ROOT/Ordinal/Buchholz/Fidelity.agda"
EXPECTED_BLOCKS=2
EXPECTED_NAMES="denotation ordinal-upper-bound"

[ -d "$ROOT" ] || { echo "check-agda-trusted-base: no Agda root at $ROOT" >&2; exit 2; }
[ -f "$ALLOWED" ] || { echo "check-agda-trusted-base: $ALLOWED is missing" >&2; exit 2; }

fail=0

# 1. No postulate outside the allowed file.
others="$(grep -rnE '^[[:space:]]*postulate([[:space:]]|$)' --include='*.agda' "$ROOT" | grep -v "^$ALLOWED:" || true)"
if [ -n "$others" ]; then
  echo "FAIL: postulate outside $ALLOWED:"; echo "$others"; fail=1
fi

# 2. Exactly the expected number of postulate blocks in the allowed file.
blocks="$(grep -cE '^[[:space:]]*postulate([[:space:]]|$)' "$ALLOWED" || true)"
if [ "$blocks" != "$EXPECTED_BLOCKS" ]; then
  echo "FAIL: $ALLOWED has $blocks postulate blocks, expected $EXPECTED_BLOCKS"; fail=1
fi

# 3. The postulated names are exactly the declared ones.
names="$(awk '
  /^[[:space:]]*postulate([[:space:]]|$)/ { inb = 1; ind = -1; next }
  inb {
    if ($0 ~ /^[[:space:]]*$/ || $0 ~ /^[[:space:]]*--/) next
    match($0, /^[[:space:]]*/); cur = RLENGTH
    if (ind < 0) ind = cur
    if (cur < ind) { inb = 0; next }
    if (cur == ind && $0 ~ /^[[:space:]]*[^[:space:]]+[[:space:]]+:/) { split($0, w, " "); print w[1] }
  }' "$ALLOWED" | LC_ALL=C sort | tr '\n' ' ' | sed 's/ $//')"
want="$(printf '%s\n' $EXPECTED_NAMES | LC_ALL=C sort | tr '\n' ' ' | sed 's/ $//')"
if [ "$names" != "$want" ]; then
  echo "FAIL: postulated names in $ALLOWED are '$names', expected '$want'"; fail=1
fi

# 4. No escape pragmas anywhere.
esc="$(grep -rnE '\{-#[[:space:]]*(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|INJECTIVE)\b|primTrustMe|trustMe' --include='*.agda' "$ROOT" || true)"
if [ -n "$esc" ]; then
  echo "FAIL: escape pragma or trustMe:"; echo "$esc"; fail=1
fi

if [ "$fail" = 0 ]; then
  echo "PASS: trusted base is exactly $EXPECTED_BLOCKS postulate blocks ($want) in $ALLOWED; no escape pragmas"
fi
exit "$fail"

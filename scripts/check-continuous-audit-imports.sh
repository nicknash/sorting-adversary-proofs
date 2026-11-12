#!/usr/bin/env bash
set -euo pipefail

expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT

find SortingAdversary/Continuous -type f -name '*.lean' -print \
  | sed '/\/Audit\.lean$/d; s/\.lean$//; s|/|.|g; s/^/import /' \
  | sort > "$expected"
grep -E '^import SortingAdversary\.Continuous\.' SortingAdversary/Continuous/Audit.lean \
  | sort > "$actual"

if ! diff -u "$expected" "$actual"; then
  echo 'Continuous/Audit.lean must import every continuous proof module exactly once.' >&2
  exit 1
fi

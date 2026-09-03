#!/usr/bin/env bash
set -euo pipefail

files=(SortingAdversary.lean)
while IFS= read -r -d '' file; do
  files+=("$file")
done < <(find SortingAdversary -name '*.lean' -print0)

# Comments may discuss these words, so inspect only source lines whose first
# non-space token is a forbidden proof escape or axiom declaration.
if grep -nE '^[[:space:]]*(sorry|admit)([[:space:]]|$)|sorryAx|^[[:space:]]*axiom[[:space:]]' \
    "${files[@]}"; then
  echo 'Trusted source contains a placeholder or project-specific axiom.' >&2
  exit 1
fi

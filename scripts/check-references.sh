#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ROOT"

while IFS= read -r pdf; do
  note="${pdf%.pdf}.md"
  [[ -f "$note" ]] || { printf 'missing reference synopsis: %s\n' "$note" >&2; exit 1; }
  expected="$(sed -n 's/^- SHA-256: `\([0-9a-f]\{64\}\)`$/\1/p' "$note")"
  actual="$(sha256sum "$pdf")"
  actual="${actual%% *}"
  [[ "$expected" == "$actual" ]] || {
    printf 'reference hash mismatch: %s\n  expected %s\n  actual   %s\n' \
      "$pdf" "$expected" "$actual" >&2
    exit 1
  }
done < <(rg --files references -g '*.pdf' | sort)

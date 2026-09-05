#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ROOT"

awk '
  /^### [A-Z0-9]+-[A-Z]+[0-9]+:/ {
    id = $2; sub(/:$/, "", id)
    if (seen[id]++) { print "duplicate salvage record: " id > "/dev/stderr"; failed = 1 }
  }
  END { exit failed }
' SALVAGE.md

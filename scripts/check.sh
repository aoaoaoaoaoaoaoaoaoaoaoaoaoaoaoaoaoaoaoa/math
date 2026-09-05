#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$HOME/.local/share/elan}"
case "${XDG_CACHE_HOME:-}" in
  /*) cache_home="$XDG_CACHE_HOME" ;;
  *) cache_home="$HOME/.cache" ;;
esac
export LAKE_CACHE_DIR="${LAKE_CACHE_DIR-$cache_home/lake}"
"$ROOT/scripts/share-lake-packages.sh" "$ROOT"

if [[ "${1:-}" == --help ]]; then
  printf '%s\n' \
    'Usage: scripts/check.sh [TARGET ...]' \
    'Proofs: m35 m44 m82 m92 source binary packing mortality frankl proofs' \
    'Release: publication (published proofs, HTML, paper)' \
    'Other: html symbolic references paper ledger all (default)' \
    'Lake options: lake build -v TARGET; lake build --no-build TARGET'
  exit 0
fi
(( $# > 0 )) || set -- all
exec lake --wfail build "$@"

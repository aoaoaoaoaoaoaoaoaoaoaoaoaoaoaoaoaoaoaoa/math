#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ROOT"

readonly SCRATCH="$(mktemp -d)"
trap 'rm -rf -- "$SCRATCH"' EXIT
export SOURCE_DATE_EPOCH=1784606400
readonly TECTONIC_BUNDLE='https://relay.fullyjustified.net/default_bundle_v33.tar'
readonly TECTONIC_VERSION='Tectonic 0.17.0'

[[ "$(tectonic --version)" == "$TECTONIC_VERSION" ]] || {
  printf 'paper reproduction requires %s\n' "$TECTONIC_VERSION" >&2
  exit 1
}

tectonic --bundle "$TECTONIC_BUNDLE" --outdir "$SCRATCH" paper/main.tex
cmp --silent "$SCRATCH/main.pdf" paper/main.pdf || {
  printf 'paper/main.pdf is not the reproducible output of paper/main.tex\n' >&2
  exit 1
}

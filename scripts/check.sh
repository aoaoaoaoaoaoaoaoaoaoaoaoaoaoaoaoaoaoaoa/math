#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
readonly ELAN_HOME="${ELAN_HOME:-$HOME/.local/share/elan}"
readonly SOURCE_DATE_EPOCH=1784606400
readonly SCRATCH="$(mktemp -d)"
trap 'rm -rf -- "$SCRATCH"' EXIT

cd -- "$ROOT"
export ELAN_HOME
export SOURCE_DATE_EPOCH

sha256sum --check ARTIFACTS.sha256

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

lake build
lake env lean AxiomAudit.lean

if rg -n '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|run_tac)\b' \
    --glob '*.lean' .; then
  printf 'forbidden proof escape found\n' >&2
  exit 1
fi

uvx --from ruff==0.15.22 ruff check tools/scour_source.py
uvx --from ruff==0.15.22 ruff format --check tools/scour_source.py
uvx --from ty==0.0.58 ty check tools/scour_source.py
uv run --script tools/scour_source.py

uvx --from html5validator==0.4.2 html5validator index.html
xmllint --html --noout index.html
while IFS= read -r href; do
  case "$href" in
    http://*|https://*|mailto:*) continue ;;
    \#*)
      id="${href#\#}"
      rg --fixed-strings --quiet "id=\"$id\"" index.html || {
        printf 'broken HTML fragment: %s\n' "$href" >&2
        exit 1
      }
      ;;
    *)
      target="${href%%#*}"
      [[ -e "$target" ]] || {
        printf 'broken local HTML link: %s\n' "$href" >&2
        exit 1
      }
      ;;
  esac
done < <(rg --only-matching 'href="[^"]+"' index.html | sed 's/^href="//; s/"$//')

tectonic --outdir "$SCRATCH" paper/main.tex
cmp --silent "$SCRATCH/main.pdf" paper/main.pdf || {
  printf 'paper/main.pdf is not the reproducible output of paper/main.tex\n' >&2
  exit 1
}

printf 'all checks passed\n'

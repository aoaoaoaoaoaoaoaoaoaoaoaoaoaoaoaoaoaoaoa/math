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

sh -n scripts/publish.sh

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
lake env lean LintAudit.lean
lake env lean AxiomAudit.lean > "$SCRATCH/axioms.txt"
if ! cmp --silent verification/axioms.txt "$SCRATCH/axioms.txt"; then
  printf 'transitive axiom set changed:\n' >&2
  diff --unified verification/axioms.txt "$SCRATCH/axioms.txt" >&2 || true
  exit 1
fi
cat "$SCRATCH/axioms.txt"

if rg -n '\b(sorry|admit|axiom|native_decide|unsafe|partial|implemented_by|run_tac|sorryAx|ofReduceBool|extern)\b|@\[nolint' \
    --glob '*.lean' .; then
  printf 'forbidden proof escape found\n' >&2
  exit 1
fi

if rg -n 'set_option[[:space:]]+(autoImplicit[[:space:]]+true|warningAsError[[:space:]]+false|linter\.[^[:space:]]+[[:space:]]+false)' \
    --glob '*.lean' .; then
  printf 'forbidden Lean strictness relaxation found\n' >&2
  exit 1
fi

uvx --from ruff==0.15.22 ruff check tools/scour_source.py
uvx --from ruff==0.15.22 ruff format --check tools/scour_source.py
uvx --from ty==0.0.58 ty check tools/scour_source.py
uv run --script tools/scour_source.py

uvx --from html5validator==0.4.2 html5validator index.html
xmllint --html --noout index.html

xpath_count() {
  xmllint --html --xpath "count($1)" index.html 2>/dev/null
}

assert_xpath_count() {
  local expected="$1"
  local path="$2"
  local actual
  actual="$(xpath_count "$path")"
  [[ "$actual" == "$expected" ]] || {
    printf 'unexpected HTML structure: count(%s) = %s, expected %s\n' \
      "$path" "$actual" "$expected" >&2
    exit 1
  }
}

check_toc_level() {
  local level="$1"
  local path="$2"
  local id
  while IFS= read -r id; do
    if [[ "$(xpath_count "$path/a[@href='#$id']")" != 1 ]]; then
      printf 'heading missing from contents level %s: %s\n' "$level" "$id" >&2
      exit 1
    fi
  done < <(rg --only-matching "<h$level id=\"[^\"]+\"" index.html | sed 's/.*id="//; s/"$//')
}

major_sections='//main[@id="article"]/article/details[contains(concat(" ", normalize-space(@class), " "), " major-section ")]'
assert_xpath_count 3 "$major_sections"
assert_xpath_count 3 "$major_sections[not(@open)]"
assert_xpath_count 3 "$major_sections/summary/h2"
assert_xpath_count 1 "($major_sections)[1]/summary/h2[@id='known-stuff' and normalize-space()='Known Stuff']"
assert_xpath_count 1 "($major_sections)[2]/summary/h2[@id='new-stuff' and normalize-space()='New Stuff']"
assert_xpath_count 1 "($major_sections)[3]/summary/h2[@id='bookkeeping' and normalize-space()='Bookkeeping']"

formulas='//div[contains(concat(" ", normalize-space(@class), " "), " formula ")]'
formula_count="$(xpath_count "$formulas")"
[[ "$formula_count" != 0 ]] || { printf 'publication contains no display mathematics\n' >&2; exit 1; }
assert_xpath_count "$formula_count" "$formulas/math[@display='block']"
assert_xpath_count 0 "$formulas[count(math) != 1 or *[not(self::math)]]"

properties='//div[contains(concat(" ", normalize-space(@class), " "), " properties ")]'
assert_xpath_count 3 "$properties/div/math[@display='block']"
assert_xpath_count 0 "$properties/div[count(math) != 1 or *[not(self::strong or self::math)]]"
assert_xpath_count 0 '//math[not(ancestor::div[contains(concat(" ", normalize-space(@class), " "), " formula ") or contains(concat(" ", normalize-space(@class), " "), " properties ")])]'
assert_xpath_count 0 '//div[contains(concat(" ", normalize-space(@class), " "), " matrix-equation ") or contains(concat(" ", normalize-space(@class), " "), " matrix ")]'

if rg --line-number -i 'MathJax|KaTeX|<script([[:space:]>])' index.html; then
  printf 'mathematical rendering runtime escaped into standalone HTML\n' >&2
  exit 1
fi

for level in 2 3 4; do
  [[ "$(xpath_count "//h$level[not(@id)]")" == 0 ]] || {
    printf 'h%s without fragment id\n' "$level" >&2
    exit 1
  }
done
check_toc_level 2 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li'
check_toc_level 3 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li/ol/li'
check_toc_level 4 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li/ol/li/ol/li'

if rg --line-number '<style([[:space:]>])|style[[:space:]]*=|rel[[:space:]]*=[[:space:]]*"stylesheet"' index.html; then
  printf 'page-local presentation escaped into index.html\n' >&2
  exit 1
fi
if rg --line-number -i 'eyebrow|section-index|class="tag([[:space:]]|")' index.html; then
  printf 'forbidden eyebrow escaped into index.html\n' >&2
  exit 1
fi
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

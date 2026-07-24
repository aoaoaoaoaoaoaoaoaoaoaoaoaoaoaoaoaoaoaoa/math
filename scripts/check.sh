#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
readonly ELAN_HOME="${ELAN_HOME:-$HOME/.local/share/elan}"
readonly MANIFEST="$ROOT/publications.json"
readonly SOURCE_DATE_EPOCH=1784606400
readonly SCRATCH="$(mktemp -d)"
trap 'rm -rf -- "$SCRATCH"' EXIT

cd -- "$ROOT"
export ELAN_HOME
export SOURCE_DATE_EPOCH

sh -n scripts/publish.sh
jq -e '
  def safe_source:
    type == "string" and
    test("^[A-Za-z0-9][A-Za-z0-9_.-]*[.]html$");
  def safe_route:
    type == "string" and
    (. == "" or (
      test("^[a-z0-9][a-z0-9_/-]*$") and
      (contains("//") | not) and
      (endswith("/") | not) and
      (split("/") | all(. != "." and . != ".." and length > 0))
    ));
  def safe_card:
    type == "string" and
    test("^[A-Za-z0-9][A-Za-z0-9_.-]*[.]png$");
  .version == 1 and
  (.publications | type == "array" and length > 0) and
  all(.publications[];
    type == "object" and
    ((keys - ["kind", "route", "social_card", "source"]) | length == 0) and
    (.kind == "index" or .kind == "collection" or .kind == "result") and
    (.source | safe_source) and
    (.route | safe_route) and
    ((has("social_card") | not) or (.social_card | safe_card)) and
    ((.kind == "index") == (.route == ""))
  ) and
  (([.publications[].source] | length) ==
    ([.publications[].source] | unique | length)) and
  (([.publications[].route] | length) ==
    ([.publications[].route] | unique | length)) and
  ([.publications[] | select(.kind == "index")] | length) == 1
' "$MANIFEST" >/dev/null

while IFS= read -r route; do
  jq -e --arg route "$route" '
    any(.publications[];
      .kind == "collection" and
      (.route as $parent | $route | startswith($parent + "/"))
    )
  ' "$MANIFEST" >/dev/null || {
    printf 'result route has no parent collection: %s\n' "$route" >&2
    exit 1
  }
done < <(jq -r '.publications[] | select(.kind == "result") | .route' "$MANIFEST")

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

assert_manifest_route() {
  local href="$1"
  local path="${href%%#*}"
  path="${path%%\?*}"
  local route="${path#/math/}"
  route="${route%/}"
  jq -e --arg route "$route" \
    'any(.publications[]; .route == $route)' "$MANIFEST" >/dev/null || {
    printf 'route absent from publications.json: %s\n' "$href" >&2
    exit 1
  }
}

check_semantic_source() {
  local publication="$1"
  uvx --from html5validator==0.4.2 html5validator "$publication"
  xmllint --html --noout "$publication"
  [[ "$(rg -o --fixed-strings '</head>' "$publication" | wc -l)" == 1 ]]
  [[ "$(rg -o '<footer>' "$publication" | wc -l)" == 1 ]]
  [[ "$(rg -o 'property="og:url"' "$publication" | wc -l)" == 0 ]]

  if rg --line-number -i 'MathJax|KaTeX|<script([[:space:]>])' "$publication"; then
    printf '%s: mathematical rendering runtime escaped into semantic HTML\n' \
      "$publication" >&2
    exit 1
  fi
  if rg --line-number \
      '<style([[:space:]>])|style[[:space:]]*=|rel[[:space:]]*=[[:space:]]*"stylesheet"' \
      "$publication"; then
    printf '%s: page-local presentation escaped into semantic HTML\n' "$publication" >&2
    exit 1
  fi
  if rg --line-number -i 'eyebrow|section-index|class="tag([[:space:]]|")' "$publication"; then
    printf '%s: forbidden eyebrow escaped into semantic HTML\n' "$publication" >&2
    exit 1
  fi

  local href
  while IFS= read -r href; do
    case "$href" in
      http://*|https://*|mailto:*) ;;
      /math/*) assert_manifest_route "$href" ;;
      \#*)
        local id="${href#\#}"
        rg --fixed-strings --quiet "id=\"$id\"" "$publication" || {
          printf '%s: broken HTML fragment: %s\n' "$publication" "$href" >&2
          exit 1
        }
        ;;
      *)
        local target="${href%%#*}"
        [[ -e "$target" ]] || {
          printf '%s: broken local HTML link: %s\n' "$publication" "$href" >&2
          exit 1
        }
        ;;
    esac
  done < <(rg --only-matching 'href="[^"]+"' "$publication" |
    sed 's/^href="//; s/"$//')
}

while IFS= read -r publication; do
  check_semantic_source "$publication"
done < <(jq -r '.publications[].source' "$MANIFEST")

xpath_count() {
  xmllint --html --xpath "count($1)" "$PUBLICATION" 2>/dev/null
}

assert_xpath_count() {
  local expected="$1"
  local path="$2"
  local actual
  actual="$(xpath_count "$path")"
  [[ "$actual" == "$expected" ]] || {
    printf '%s: unexpected HTML structure: count(%s) = %s, expected %s\n' \
      "$PUBLICATION" "$path" "$actual" "$expected" >&2
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
  done < <(rg --only-matching "<h$level id=\"[^\"]+\"" "$PUBLICATION" |
    sed 's/.*id="//; s/"$//')
}

check_publication() {
  PUBLICATION="$1"
  local expected_properties="$2"

  local major_sections='//main[@id="article"]/article/details[contains(concat(" ", normalize-space(@class), " "), " major-section ")]'
  local article='//main[@id="article"]/article'
  local headline_result="$article/div[contains(concat(' ', normalize-space(@class), ' '), ' verdict ')]"
  assert_xpath_count 1 "$headline_result"
  assert_xpath_count 1 "($article/*)[1][self::div[contains(concat(' ', normalize-space(@class), ' '), ' verdict ')]]"
  assert_xpath_count 2 "$headline_result/p"
  assert_xpath_count 3 "$major_sections"
  assert_xpath_count 3 "$major_sections[not(@open)]"
  assert_xpath_count 3 "$major_sections/summary/h2"
  assert_xpath_count 1 "($major_sections)[1]/summary/h2[@id='known-stuff' and normalize-space()='Known Stuff']"
  assert_xpath_count 1 "($major_sections)[2]/summary/h2[@id='new-stuff' and normalize-space()='New Stuff']"
  assert_xpath_count 1 "($major_sections)[3]/summary/h2[@id='bookkeeping' and normalize-space()='Bookkeeping']"

  assert_xpath_count 0 \
    "$article//table[contains(concat(' ', normalize-space(@class), ' '), ' status-table ')]"
  assert_xpath_count 0 \
    "$article//strong[contains(concat(' ', normalize-space(@class), ' '), ' new-result ')]"

  local formulas='//div[contains(concat(" ", normalize-space(@class), " "), " formula ")]'
  local formula_count
  formula_count="$(xpath_count "$formulas")"
  [[ "$formula_count" != 0 ]] || {
    printf '%s: publication contains no display mathematics\n' "$PUBLICATION" >&2
    exit 1
  }
  assert_xpath_count "$formula_count" "$formulas/math[@display='block']"
  assert_xpath_count 0 "$formulas[count(math) != 1 or *[not(self::math)]]"

  local properties='//div[contains(concat(" ", normalize-space(@class), " "), " properties ")]'
  assert_xpath_count "$expected_properties" "$properties/div/math[@display='block']"
  assert_xpath_count 0 "$properties/div[count(math) != 1 or *[not(self::strong or self::math)]]"
  assert_xpath_count 0 '//math[not(ancestor::div[contains(concat(" ", normalize-space(@class), " "), " formula ") or contains(concat(" ", normalize-space(@class), " "), " properties ")])]'
  assert_xpath_count 0 '//div[contains(concat(" ", normalize-space(@class), " "), " matrix-equation ") or contains(concat(" ", normalize-space(@class), " "), " matrix ")]'

  local level
  for level in 2 3 4; do
    [[ "$(xpath_count "//h$level[not(@id)]")" == 0 ]] || {
      printf '%s: h%s without fragment id\n' "$PUBLICATION" "$level" >&2
      exit 1
    }
  done
  check_toc_level 2 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li'
  check_toc_level 3 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li/ol/li'
  check_toc_level 4 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li/ol/li/ol/li'

}

check_collection() {
  PUBLICATION="$1"
  local route="$2"
  local article='//main[@id="article"]/article'
  local collection_results
  collection_results="$(jq --arg prefix "$route/" \
    '[.publications[] | select(.kind == "result" and (.route | startswith($prefix)))] | length' \
    "$MANIFEST")"

  assert_xpath_count 1 '//h1[normalize-space()="Matrix Mortality"]'
  assert_xpath_count 0 \
    "$article/div[contains(concat(' ', normalize-space(@class), ' '), ' verdict ')]"
  assert_xpath_count 0 \
    "$article/details[contains(concat(' ', normalize-space(@class), ' '), ' major-section ')]"
  assert_xpath_count 1 \
    "($article/*)[1][self::section/h2[@id='techniques' and normalize-space()='Techniques']]"
  assert_xpath_count "$collection_results" \
    "($article/section[h2[@id='techniques']])[1]/ul[contains(concat(' ', normalize-space(@class), ' '), ' artifact-list ')]/li/a"
  assert_xpath_count 1 \
    "$article/section[h2[@id='definition']]//div[contains(concat(' ', normalize-space(@class), ' '), ' definition ')]"
  assert_xpath_count 1 \
    "$article/section[h2[@id='frontier']]//table[contains(concat(' ', normalize-space(@class), ' '), ' status-table ')]"
  local table_stars="$article//table[contains(concat(' ', normalize-space(@class), ' '), ' status-table ')]//strong[contains(concat(' ', normalize-space(@class), ' '), ' new-result ') and normalize-space()='U★']"
  assert_xpath_count 6 "$table_stars"
  assert_xpath_count 6 "$table_stars/parent::a"
  assert_xpath_count 4 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/m3_5/#result']"
  assert_xpath_count 1 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/m4_4/#result']"
  assert_xpath_count 1 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/binary_compilers/#mortality-ten']"

  local formulas='//div[contains(concat(" ", normalize-space(@class), " "), " formula ")]'
  local formula_count
  formula_count="$(xpath_count "$formulas")"
  [[ "$formula_count" != 0 ]]
  assert_xpath_count "$formula_count" "$formulas/math[@display='block']"
  assert_xpath_count 0 "$formulas[count(math) != 1 or *[not(self::math)]]"
  assert_xpath_count 0 \
    '//math[not(ancestor::div[contains(concat(" ", normalize-space(@class), " "), " formula ")])]'

  local level
  for level in 2 3 4; do
    [[ "$(xpath_count "//h$level[not(@id)]")" == 0 ]] || {
      printf '%s: h%s without fragment id\n' "$PUBLICATION" "$level" >&2
      exit 1
    }
  done
  check_toc_level 2 \
    '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li'

  while IFS= read -r child_route; do
    rg --quiet --fixed-strings "href=\"/math/$child_route/\"" "$PUBLICATION"
  done < <(jq -r --arg prefix "$route/" \
    '.publications[] | select(.kind == "result" and (.route | startswith($prefix))) | .route' \
    "$MANIFEST")
}

check_collection matrix_mortality.html matrix_mortality
check_publication m3_5.html 3
check_publication m4_4.html 0
check_publication binary_compilers.html 0

PUBLICATION=math.html
assert_xpath_count 1 '//h1[normalize-space()="Mathematics"]'
collection_count="$(jq '[.publications[] | select(.kind == "collection")] | length' "$MANIFEST")"
assert_xpath_count "$collection_count" \
  '//ul[contains(concat(" ", normalize-space(@class), " "), " artifact-list ")]/li/a'
while IFS= read -r route; do
  rg --quiet --fixed-strings "href=\"/math/$route/\"" math.html
done < <(jq -r '.publications[] | select(.kind == "collection") | .route' "$MANIFEST")

diff --unified \
  <(jq -r '.publications[] | select(.kind != "index") | .source' "$MANIFEST" | sort) \
  <(printf '%s\n' binary_compilers.html matrix_mortality.html m3_5.html m4_4.html | sort)

tectonic --outdir "$SCRATCH" paper/main.tex
cmp --silent "$SCRATCH/main.pdf" paper/main.pdf || {
  printf 'paper/main.pdf is not the reproducible output of paper/main.tex\n' >&2
  exit 1
}

printf 'all checks passed\n'

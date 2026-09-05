#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ROOT"

readonly MANIFEST="$ROOT/publications.json"

sh -n scripts/publish.sh
uvx --from ruff==0.15.22 ruff check scripts/render_publication_graph.py
uvx --from ruff==0.15.22 ruff format --check scripts/render_publication_graph.py
uvx --from ty==0.0.58 ty check scripts/render_publication_graph.py
jq -e '
  def safe_source:
    type == "string" and
    test("^[A-Za-z0-9][A-Za-z0-9_.-]*[.]html$");
  def safe_graph_source:
    type == "string" and
    test("^[A-Za-z0-9][A-Za-z0-9_.-]*[.]json$");
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
  . as $manifest |
  .version == 3 and
  ((keys - ["graphs", "publications", "version"]) | length == 0) and
  (.graphs | type == "array") and
  all(.graphs[];
    type == "object" and
    (keys == ["collection", "source"]) and
    (.collection | safe_route) and
    (.collection | length > 0) and
    (.source | safe_graph_source)
  ) and
  (([.graphs[].source] | length) ==
    ([.graphs[].source] | unique | length)) and
  (([.graphs[].collection] | length) ==
    ([.graphs[].collection] | unique | length)) and
  (.publications | type == "array" and length > 0) and
  all(.publications[];
    type == "object" and
    ((keys - ["kind", "route", "social_card", "source"]) | length == 0) and
    (.kind == "index" or .kind == "collection" or .kind == "reference" or
      .kind == "module" or .kind == "result") and
    (.source | safe_source) and
    (.route | safe_route) and
    ((has("social_card") | not) or (.social_card | safe_card)) and
    ((.kind == "index") == (.route == ""))
  ) and
  (([.publications[].source] | length) ==
    ([.publications[].source] | unique | length)) and
  (([.publications[].route] | length) ==
    ([.publications[].route] | unique | length)) and
  ([.publications[] | select(.kind == "index")] | length) == 1 and
  all(
    $manifest.publications[] | select(.kind != "index");
    . as $child |
    any(
      $manifest.publications[];
      .route == ($child.route | split("/") | .[0:-1] | join("/")) and
      (
        ($child.kind == "collection" and .kind == "index") or
        (($child.kind == "reference" or $child.kind == "module" or
          $child.kind == "result") and
          .kind == "collection")
      )
    )
  ) and
  all(
    $manifest.graphs[];
    . as $graph |
    any(
      $manifest.publications[];
      .kind == "collection" and .route == $graph.collection
    )
  )
' "$MANIFEST" >/dev/null

while IFS= read -r graph_source; do
  [[ -s "$graph_source" ]]
  jq -e . "$graph_source" >/dev/null
done < <(jq -r '.graphs[].source' "$MANIFEST")

uv run --script scripts/render_publication_graph.py --check

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
  if [[ "$(xmllint --html --xpath 'count(/html/body/footer/div)' "$publication" 2>/dev/null)" != 1 ]]; then
    printf '%s: publication footer must own one div for the site importer\n' "$publication" >&2
    exit 1
  fi
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

  local duplicate_ids
  duplicate_ids="$(rg --only-matching 'id="[^"]+"' "$publication" |
    sed 's/^id="//; s/"$//' | sort | uniq -d)"
  [[ -z "$duplicate_ids" ]] || {
    printf '%s: duplicate fragment identifiers:\n%s\n' \
      "$publication" "$duplicate_ids" >&2
    exit 1
  }

  local level headings linked
  for level in 2 3 4; do
    headings="$(xmllint --html --xpath "count(//h$level)" "$publication" 2>/dev/null)"
    linked="$(xmllint --html --xpath \
      "count(//h$level[@id][count(a)=1][a[contains(concat(' ', normalize-space(@class), ' '), ' fragment-link ')][@href=concat('#', ../@id)][@aria-label='Link to this section'][normalize-space()='#']][*[last()][self::a]])" \
      "$publication" 2>/dev/null)"
    [[ "$headings" == "$linked" ]] || {
      printf '%s: h%s headings do not own exact terminal fragment links\n' \
        "$publication" "$level" >&2
      exit 1
    }
  done

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
  local profile="${3:-result}"

  local major_sections='//main[@id="article"]/article/details[contains(concat(" ", normalize-space(@class), " "), " major-section ")]'
  local article='//main[@id="article"]/article'
  local abstract='//div[contains(concat(" ", normalize-space(@class), " "), " shell ")]/section[contains(concat(" ", normalize-space(@class), " "), " abstract ")]'
  assert_xpath_count 1 "$abstract[@aria-label='Abstract' and string-length(normalize-space(.)) > 0]"
  assert_xpath_count 1 '(//div[contains(concat(" ", normalize-space(@class), " "), " shell ")]/*)[1][self::section[contains(concat(" ", normalize-space(@class), " "), " abstract ")]]'
  assert_xpath_count 0 '//head/meta[@name="description" or @property="og:description"]'
  assert_xpath_count 0 '//p[contains(concat(" ", normalize-space(@class), " "), " module-meta ")]'
  if [[ "$profile" != collection ]]; then
    assert_xpath_count 1 \
      "$article/nav[contains(concat(' ', normalize-space(@class), ' '), ' module-context ')][@aria-label='Module relations']"
  fi
  assert_xpath_count 3 "$major_sections"
  assert_xpath_count 3 "$major_sections[not(@open)]"
  assert_xpath_count 3 "$major_sections/summary/h2"
  assert_xpath_count 1 "($major_sections)[1]/summary/h2[@id='known-stuff' and normalize-space(text()[1])='Known Stuff']"
  assert_xpath_count 1 "($major_sections)[2]/summary/h2[@id='new-stuff' and normalize-space(text()[1])='New Stuff']"
  assert_xpath_count 1 "($major_sections)[3]/summary/h2[@id='bookkeeping' and normalize-space(text()[1])='Bookkeeping']"

  local fragment_subsections fragment_section_count
  fragment_subsections="$major_sections//*[self::h3 or self::h4][@id][not(parent::summary)]"
  fragment_section_count="$(xpath_count "$fragment_subsections")"
  assert_xpath_count "$fragment_section_count" \
    "$fragment_subsections[parent::section[contains(concat(' ', normalize-space(@class), ' '), ' fragment-section ')]]"
  assert_xpath_count 0 \
    "$major_sections//*[self::h3 or self::h4][@id][parent::summary[not(parent::details)]]"

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
  # Display formulas own a block wrapper; native inline MathML belongs in prose.
  assert_xpath_count 0 '//math[@display="block"][not(ancestor::div[contains(concat(" ", normalize-space(@class), " "), " formula ") or contains(concat(" ", normalize-space(@class), " "), " properties ")])]'
  assert_xpath_count 0 '//div[contains(concat(" ", normalize-space(@class), " "), " matrix-equation ") or contains(concat(" ", normalize-space(@class), " "), " matrix ")]'

  check_toc_level 2 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li'
  check_toc_level 3 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li/ol/li'
  check_toc_level 4 '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li/ol/li/ol/li'

}

check_collection() {
  PUBLICATION="$1"
  local route="$2"
  local article='//main[@id="article"]/article'
  local collection_references graph_source graph_nodes graph_views
  collection_references="$(jq --arg prefix "$route/" \
    '[.publications[] | select(.kind == "reference" and (.route | startswith($prefix)))] | length' \
    "$MANIFEST")"
  graph_source="$(jq -r --arg collection "$route" \
    '.graphs[] | select(.collection == $collection) | .source' "$MANIFEST")"
  [[ -n "$graph_source" ]]
  graph_nodes="$(jq '.nodes | length' "$graph_source")"
  graph_views="$(jq '.views | length' "$graph_source")"

  assert_xpath_count 1 '//h1[normalize-space()="Matrix Mortality"]'
  assert_xpath_count 0 \
    '//section[contains(concat(" ", normalize-space(@class), " "), " abstract ")]'
  assert_xpath_count 0 \
    "$article/details[contains(concat(' ', normalize-space(@class), ' '), ' major-section ')]"
  assert_xpath_count 1 \
    "($article/*)[1][self::section/h2[@id='definition']]"
  assert_xpath_count 1 "$article/section/h2[@id='reference']"
  assert_xpath_count "$collection_references" \
    "($article/section[h2[@id='reference']])[1]/ul[contains(concat(' ', normalize-space(@class), ' '), ' artifact-list ')]/li/a"
  assert_xpath_count 1 \
    "$article/section/h2[@id='modules']"
  assert_xpath_count "$graph_nodes" \
    "$article/section[h2[@id='modules']]//li[contains(concat(' ', normalize-space(@class), ' '), ' module-node ')][@data-node-id]"
  assert_xpath_count "$graph_views" \
    "$article/section[h2[@id='modules']]//section[contains(concat(' ', normalize-space(@class), ' '), ' module-layer ')]"
  assert_xpath_count 0 "$article/section[h2[@id='techniques' or @id='dependencies']]"
  assert_xpath_count 1 \
    "$article/section[h2[@id='definition']]//div[contains(concat(' ', normalize-space(@class), ' '), ' definition ')]"
  assert_xpath_count 1 \
    "$article/section[h2[@id='frontier']]//table[contains(concat(' ', normalize-space(@class), ' '), ' status-table ')]"
  local table_stars="$article//table[contains(concat(' ', normalize-space(@class), ' '), ' status-table ')]//strong[contains(concat(' ', normalize-space(@class), ' '), ' new-result ') and normalize-space()='U★']"
  assert_xpath_count 9 "$table_stars"
  assert_xpath_count 9 "$table_stars/parent::a"
  assert_xpath_count 5 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/m3_5/#result']"
  assert_xpath_count 1 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/m4_4/#result']"
  assert_xpath_count 1 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/binary_compilers/#mortality-ten']"
  assert_xpath_count 1 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/m9_2/#result']"
  assert_xpath_count 1 \
    "$table_stars/parent::a[@href='/math/matrix_mortality/m8_2/#result']"

  local formulas='//div[contains(concat(" ", normalize-space(@class), " "), " formula ")]'
  local formula_count
  formula_count="$(xpath_count "$formulas")"
  [[ "$formula_count" != 0 ]]
  assert_xpath_count "$formula_count" "$formulas/math[@display='block']"
  assert_xpath_count 0 "$formulas[count(math) != 1 or *[not(self::math)]]"
  assert_xpath_count 0 \
    '//math[@display="block"][not(ancestor::div[contains(concat(" ", normalize-space(@class), " "), " formula ")])]'

  check_toc_level 2 \
    '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li'

  while IFS= read -r child_route; do
    rg --quiet --fixed-strings "href=\"/math/$child_route/" "$PUBLICATION"
  done < <(jq -r --arg prefix "$route/" \
    '.publications[] | select((.kind == "reference" or .kind == "module" or .kind == "result") and (.route | startswith($prefix))) | .route' \
    "$MANIFEST")
}

check_reference() {
  PUBLICATION="$1"
  local article='//main[@id="article"]/article'
  local entries="$article//dl[contains(concat(' ', normalize-space(@class), ' '), ' glossary ')]/div[contains(concat(' ', normalize-space(@class), ' '), ' glossary-entry ')]"
  local entry_count
  entry_count="$(xpath_count "$entries")"

  [[ "$entry_count" -ge 60 ]] || {
    printf '%s: glossary is too narrow for its declared audience (%s entries)\n' \
      "$PUBLICATION" "$entry_count" >&2
    exit 1
  }
  assert_xpath_count 1 '//h1[normalize-space()="Matrix Mortality Glossary"]'
  assert_xpath_count 0 \
    '//section[contains(concat(" ", normalize-space(@class), " "), " abstract ")]'
  assert_xpath_count 0 \
    "$article/details[contains(concat(' ', normalize-space(@class), ' '), ' major-section ')]"
  assert_xpath_count "$entry_count" "$entries/dt[@id][dfn][count(a)=1]"
  assert_xpath_count "$entry_count" \
    "$entries/dt/a[contains(concat(' ', normalize-space(@class), ' '), ' fragment-link ')][@href=concat('#', ../@id)][@aria-label='Link to this term'][normalize-space()='#']"
  assert_xpath_count "$entry_count" "$entries/dd[p[1][string-length(normalize-space(.)) > 0]]"
  assert_xpath_count "$entry_count" \
    "$article//nav[contains(concat(' ', normalize-space(@class), ' '), ' glossary-index ')]/ol/li/a"

  local id
  while IFS= read -r id; do
    assert_xpath_count 1 \
      "$article//nav[contains(concat(' ', normalize-space(@class), ' '), ' glossary-index ')]/ol/li/a[@href='#$id']"
  done < <(rg --only-matching '<dt id="[^"]+"' "$PUBLICATION" |
    sed 's/.*id="//; s/"$//')

  check_toc_level 2 \
    '//nav[contains(concat(" ", normalize-space(@class), " "), " contents ")]/ol/li'
}

check_collection matrix_mortality.html matrix_mortality
check_reference matrix_mortality_glossary.html
check_publication frankl.html 0 collection
check_publication m3_5.html 3
check_publication m4_4.html 0
check_publication binary_compilers.html 0
check_publication m9_2.html 0
check_publication m8_2.html 0
check_publication m3_2_return_guard.html 0
check_publication paired_scalar_series.html 0
check_publication interface_compression.html 0
check_publication shortcut_collatz_incidence.html 0

PUBLICATION=math.html
assert_xpath_count 1 '//h1[normalize-space()="Mathematics"]'
collection_count="$(jq '[.publications[] | select(.kind == "collection")] | length' "$MANIFEST")"
assert_xpath_count "$collection_count" \
  '//ul[contains(concat(" ", normalize-space(@class), " "), " artifact-list ")]/li/a'
while IFS= read -r route; do
  rg --quiet --fixed-strings "href=\"/math/$route/\"" math.html
done < <(jq -r '.publications[] | select(.kind == "collection") | .route' "$MANIFEST")

diff --unified \
  <(jq -r '.publications[].source' "$MANIFEST" | sort) \
  <(rg --files -g '*.html' | sort)

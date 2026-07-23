#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
site=${ETERNALIST_SITE_SOURCE:-"$root/../eternalist.moe"}
manifest="$root/publications.json"

fail() {
    printf '%s\n' "$1" >&2
    exit 1
}

require_release_head() {
    repo=$1
    name=$2

    test -z "$(git -C "$repo" status --porcelain)" || fail "$name worktree is not clean"
    test "$(git -C "$repo" branch --show-current)" = main || fail "$name is not on main"
}

require_upstream_head() {
    repo=$1
    name=$2

    git -C "$repo" rev-parse '@{upstream}' >/dev/null 2>&1 || \
        fail "$name has no upstream branch"
    test "$(git -C "$repo" rev-parse HEAD)" = "$(git -C "$repo" rev-parse '@{upstream}')" || \
        fail "$name HEAD differs from its upstream"
}

test -x "$site/scripts/check" || fail "Eternalist checkout not found at $site"
test -x "$site/scripts/deploy" || fail "Eternalist deployment contract not found at $site"
require_release_head "$root" math
require_release_head "$site" eternalist

git -C "$site" fetch --quiet
require_upstream_head "$site" eternalist

"$root/scripts/check.sh"
ETERNALIST_MATH_SOURCE="$root" "$site/scripts/check"

git -C "$root" push
require_upstream_head "$root" math

revision=$(git -C "$root" rev-parse HEAD)
invalidation=$(ETERNALIST_MATH_SOURCE="$root" "$site/scripts/deploy" --wait)
out=$(ETERNALIST_MATH_SOURCE="$root" "$site/scripts/build")
live=$(mktemp -d)
trap 'rm -rf "$live"' EXIT HUP INT TERM
jq -c '.publications[]' "$manifest" |
    while IFS= read -r entry; do
        source=$(printf '%s\n' "$entry" | jq -r '.source')
        route=$(printf '%s\n' "$entry" | jq -r '.route')
        if test -n "$route"; then
            path="math/$route/index.html"
            url="https://eternalist.moe/math/$route/"
        else
            path='math/index.html'
            url='https://eternalist.moe/math/'
        fi
        curl --fail --location --silent --show-error \
            "$url?revision=$revision" \
            --output "$live/$source"
        cmp --silent "$out/$path" "$live/$source" || \
            fail "live publication differs from the release build: /$path"
    done

printf 'published math %s via CloudFront invalidation %s\n' "$revision" "$invalidation"

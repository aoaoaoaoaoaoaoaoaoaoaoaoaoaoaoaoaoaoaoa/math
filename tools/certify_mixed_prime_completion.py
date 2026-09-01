#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Certify the finite completion of the five mixed-prime rewrite rules."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections.abc import Iterator
from dataclasses import asdict, dataclass


@dataclass(frozen=True, slots=True)
class Rule:
    """One equal-length lexicographically decreasing rewrite rule."""

    name: str
    lhs: str
    rhs: str


@dataclass(frozen=True, slots=True)
class CompletionSummary:
    """Compact output of the exact completion audit."""

    rules: int
    unique_lhs: int
    lhs_inclusions: int
    critical_overlaps: int
    distinct_critical_pairs: int
    old_pairs: int
    new_pairs: int
    step_histogram: dict[str, int]
    minimum_critical_length: int
    maximum_critical_length: int
    fork_length: int
    fork_left_steps: int
    fork_right_steps: int
    fork_normal_form_sha256: str
    odd_family_periodic_bound: int
    certificate_sha256: str
    status: str


@dataclass(frozen=True, slots=True)
class ForkSummary:
    """Normal-form replay of the first quotient fork."""

    length: int
    left_steps: int
    right_steps: int
    normal_form_sha256: str


BASE_RULES = (
    Rule(
        "r27",
        "TTDDDDDDTTDDTDTDTDDTTDDTDTT",
        "DTTTTTTTTTTDDTDDTDDDDDDDDDD",
    ),
    Rule(
        "r29",
        "TTDDDDDDTTDDTDTDTDDTTDDTTDDTT",
        "DTTTTTTTTTTDDTDDTDDDDDDDDDTDD",
    ),
    Rule(
        "r30a",
        "TTDDDDDDDDTTTTDTDTDDTDDTDDTDTT",
        "DTTTTTTDTTDTTTDDTDDTDDDDDDDDDD",
    ),
    Rule(
        "r30b",
        "TTDDDDDDDDDDTTTDDDTTTTDDTDDDTT",
        "DTTTTTTDDTDTTDDTTDDTDDDDDDDDDD",
    ),
    Rule(
        "r30c",
        "TTDDDDDDDDDTDTTDTTTTDDTDDTDDDT",
        "DTTTTTTDDTTTDDDTDTDTDDDDDDDDDD",
    ),
)

ODD_FAMILY_LEFT_HEAD = "DTTTTTTTTTTDDTDDTDDDDDDDDDT"
ODD_FAMILY_RIGHT_HEAD = "TTDDDDDDTTDDTDTDTDDTTDDTT"

type Trace = tuple[tuple[int, int], ...]


def orient(left: str, right: str) -> tuple[str, str]:
    """Orient one balanced relation by strict lexicographic descent."""
    assert len(left) == len(right) and left != right
    return max(left, right), min(left, right)


def affine_signature(word: str) -> tuple[int, int, int]:
    """Return the exact upper-triangular integer action signature."""
    slope_numerator, offset, denominator = 1, 0, 1
    for letter in word:
        match letter:
            case "D":
                slope_numerator *= 2
                offset *= 3
                denominator *= 3
            case "T":
                offset = 5 * (slope_numerator + offset)
                slope_numerator *= 3
                denominator *= 5
            case _:
                raise AssertionError("raw words use only D and T")
    return slope_numerator, offset, denominator


def proper_overlaps(left: str, right: str) -> Iterator[int]:
    """Yield every nonempty proper suffix-prefix overlap width."""
    for width in range(1, min(len(left), len(right))):
        if left[-width:] == right[:width]:
            yield width


def occurrences(word: str, pattern: str) -> Iterator[int]:
    """Yield all overlapping occurrences of ``pattern`` in ``word``."""
    for position in range(len(word) - len(pattern) + 1):
        if word.startswith(pattern, position):
            yield position


def normalize(word: str, rules: tuple[Rule, ...]) -> tuple[str, Trace]:
    """Normalize by the deterministic leftmost-then-lexicographic strategy."""
    trace: list[tuple[int, int]] = []
    while True:
        redexes = [
            (position, rule.lhs, index, rule.rhs)
            for index, rule in enumerate(rules)
            for position in occurrences(word, rule.lhs)
        ]
        if not redexes:
            return word, tuple(trace)
        position, lhs, index, rhs = min(redexes)
        successor = word[:position] + rhs + word[position + len(lhs) :]
        assert len(successor) == len(word) and successor < word
        word = successor
        trace.append((index, position))


def construct_rules() -> tuple[Rule, ...]:
    """Adjoin every first critical branch pair to the five base rules."""
    rules = list(BASE_RULES)
    seen = {(rule.lhs, rule.rhs) for rule in rules}
    for left in BASE_RULES:
        for right in BASE_RULES:
            for width in proper_overlaps(left.lhs, right.lhs):
                left_branch = left.rhs + right.lhs[width:]
                right_branch = left.lhs[:-width] + right.rhs
                lhs, rhs = orient(left_branch, right_branch)
                assert (lhs, rhs) not in seen
                seen.add((lhs, rhs))
                rules.append(Rule(f"{left.name}>{right.name}@{width}", lhs, rhs))
    assert len(rules) == 50
    return tuple(rules)


def certify_odd_family_avoidance(rules: tuple[Rule, ...]) -> int:
    """Check the finite boundary basis proving odd-family irreducibility."""
    bound = max(len(rule.lhs) for rule in rules)
    assert all(rule.lhs.startswith("TTDD") for rule in rules)
    assert "TTDD" not in "DT" * bound
    for depth in range(1, bound + 1):
        left = ODD_FAMILY_LEFT_HEAD + "DT" * depth + "DD"
        right = ODD_FAMILY_RIGHT_HEAD + "DT" * depth + "DDTT"
        assert left != right
        assert normalize(left, rules) == (left, ())
        assert normalize(right, rules) == (right, ())
    return bound


def certify_fork(rules: tuple[Rule, ...]) -> ForkSummary:
    """Replay the length-312 fork through the completed normalizer."""
    cassaigne_right = BASE_RULES[0].lhs
    cassaigne_left = BASE_RULES[0].rhs
    middle = cassaigne_right[1:-1]
    x = cassaigne_right[:-1]
    z = cassaigne_left + middle
    root = z + x
    y = x + root
    left = y + z + x + y + x
    right = x + z + y + x + y
    left_normal, left_trace = normalize(left, rules)
    right_normal, right_trace = normalize(right, rules)
    assert (len(x), len(y), len(z), len(left)) == (26, 104, 52, 312)
    assert left != right and left_normal == right_normal
    return ForkSummary(
        length=len(left),
        left_steps=len(left_trace),
        right_steps=len(right_trace),
        normal_form_sha256=hashlib.sha256(left_normal.encode()).hexdigest(),
    )


def certify() -> tuple[dict[str, object], CompletionSummary]:
    """Build and check the canonical finite-convergence certificate."""
    rules = construct_rules()
    assert len({(rule.lhs, rule.rhs) for rule in rules}) == 50
    assert len({rule.lhs for rule in rules}) == 50
    for rule in rules:
        assert len(rule.lhs) == len(rule.rhs) and rule.lhs > rule.rhs
        assert affine_signature(rule.lhs) == affine_signature(rule.rhs)
        assert normalize(rule.rhs, rules) == (rule.rhs, ())

    inclusions = [
        (outer_index, inner_index, position)
        for outer_index, outer in enumerate(rules)
        for inner_index, inner in enumerate(rules)
        for position in occurrences(outer.lhs, inner.lhs)
        if outer_index != inner_index or position != 0
    ]
    assert not inclusions

    rule_pairs = {(rule.lhs, rule.rhs) for rule in rules}
    pair_keys: set[tuple[str, str]] = set()
    critical_pairs: list[dict[str, object]] = []
    critical_lengths: list[int] = []
    old_pairs = 0
    new_pairs = 0
    step_histogram: dict[tuple[int, int], int] = {}
    for left_index, left in enumerate(rules):
        for right_index, right in enumerate(rules):
            for width in proper_overlaps(left.lhs, right.lhs):
                source = left.lhs + right.lhs[width:]
                left_branch = left.rhs + right.lhs[width:]
                right_branch = left.lhs[:-width] + right.rhs
                assert affine_signature(source) == affine_signature(left_branch)
                assert affine_signature(source) == affine_signature(right_branch)
                pair = orient(left_branch, right_branch)
                assert pair not in pair_keys
                pair_keys.add(pair)
                left_normal, left_trace = normalize(left_branch, rules)
                right_normal, right_trace = normalize(right_branch, rules)
                assert left_normal == right_normal
                steps = (len(left_trace), len(right_trace))
                step_histogram[steps] = step_histogram.get(steps, 0) + 1
                if pair in rule_pairs:
                    old_pairs += 1
                    assert sorted(steps) == [0, 1]
                else:
                    new_pairs += 1
                    assert sorted(steps) == [0, 2]
                critical_pairs.append(
                    {
                        "left_rule": left_index,
                        "right_rule": right_index,
                        "overlap": width,
                        "source": source,
                        "left_branch": left_branch,
                        "right_branch": right_branch,
                        "left_trace": left_trace,
                        "right_trace": right_trace,
                        "normal_form": left_normal,
                    }
                )
                critical_lengths.append(len(source))

    assert len(critical_pairs) == len(pair_keys) == 450
    assert old_pairs == 45 and new_pairs == 405
    fork = certify_fork(rules)
    odd_bound = certify_odd_family_avoidance(rules)
    payload: dict[str, object] = {
        "alphabet": ["D", "T"],
        "order": "equal-length lexicographic, D<T",
        "rules": [asdict(rule) for rule in rules],
        "critical_pairs": critical_pairs,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CompletionSummary(
        rules=len(rules),
        unique_lhs=len({rule.lhs for rule in rules}),
        lhs_inclusions=len(inclusions),
        critical_overlaps=len(critical_pairs),
        distinct_critical_pairs=len(pair_keys),
        old_pairs=old_pairs,
        new_pairs=new_pairs,
        step_histogram={
            f"{left},{right}": count
            for (left, right), count in sorted(step_histogram.items())
        },
        minimum_critical_length=min(critical_lengths),
        maximum_critical_length=max(critical_lengths),
        fork_length=fork.length,
        fork_left_steps=fork.left_steps,
        fork_right_steps=fork.right_steps,
        fork_normal_form_sha256=fork.normal_form_sha256,
        odd_family_periodic_bound=odd_bound,
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="finite convergent presentation certified",
    )
    return payload, summary


def main() -> None:
    """Print either the compact summary or the canonical full certificate."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    arguments = parser.parse_args()
    payload, summary = certify()
    output: object = payload if arguments.full else asdict(summary)
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()

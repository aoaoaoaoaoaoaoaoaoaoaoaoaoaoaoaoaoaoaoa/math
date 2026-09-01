#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Certify every Parikh-balanced cut in two mixed-prime rewrite generations."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import asdict, dataclass

from certify_mixed_prime_completion import (
    affine_signature,
    construct_rules,
    normalize,
    orient,
    proper_overlaps,
)


@dataclass(frozen=True, slots=True)
class CutRow:
    """All proper balanced cuts of one oriented equal-Parikh relation."""

    name: str
    generation: int
    lhs: str
    rhs: str
    prefix_cuts: tuple[int, ...]
    suffix_cuts: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class CutSummary:
    """Compact output of the exact contextual-cut audit."""

    completed_rules: int
    base_rules: int
    first_critical_rules: int
    second_critical_pairs: int
    first_length_histogram: dict[str, int]
    first_extra_cut_histogram: dict[str, int]
    second_length_histogram: dict[str, int]
    second_cut_histogram: dict[str, int]
    first_internal_bound: int
    second_internal_bound: int
    certificate_sha256: str
    status: str


def balanced_cuts(left: str, right: str) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Return all proper prefix and suffix cuts with equal dilation count."""
    assert len(left) == len(right)
    length = len(left)
    prefixes = tuple(
        cut
        for cut in range(1, length)
        if left[:cut].count("D") == right[:cut].count("D")
    )
    suffixes = tuple(
        cut
        for cut in range(1, length)
        if left[-cut:].count("D") == right[-cut:].count("D")
    )
    assert suffixes == tuple(length - cut for cut in reversed(prefixes))
    for cut in prefixes:
        assert left[cut - 1] != right[cut - 1]
        assert left[cut] != right[cut]
    return prefixes, suffixes


def histogram(values: list[int]) -> dict[str, int]:
    """Encode an integer histogram with deterministic string keys."""
    return {str(value): count for value, count in sorted(Counter(values).items())}


def certify() -> tuple[dict[str, object], CutSummary]:
    """Construct and check the two-generation contextual-cut certificate."""
    rules = construct_rules()
    assert len(rules) == 50

    first_rows: list[CutRow] = []
    first_extra_patterns: Counter[tuple[int, int, int]] = Counter()
    for index, rule in enumerate(rules):
        assert affine_signature(rule.lhs) == affine_signature(rule.rhs)
        prefixes, suffixes = balanced_cuts(rule.lhs, rule.rhs)
        if index < 5:
            assert prefixes == (3,)
        else:
            assert len(prefixes) == 2 and prefixes[0] == 3
            extra = prefixes[1]
            assert 28 <= extra <= 32
            first_extra_patterns[(len(rule.lhs), extra, len(rule.lhs) - extra)] += 1
        first_rows.append(
            CutRow(
                name=rule.name,
                generation=1,
                lhs=rule.lhs,
                rhs=rule.rhs,
                prefix_cuts=prefixes,
                suffix_cuts=suffixes,
            )
        )

    rule_pairs = {(rule.lhs, rule.rhs) for rule in rules}
    second_rows: list[CutRow] = []
    seen_pairs: set[tuple[str, str]] = set()
    second_cut_patterns: Counter[tuple[int, int, int]] = Counter()
    for left_index, left_rule in enumerate(rules):
        for right_index, right_rule in enumerate(rules):
            for overlap in proper_overlaps(left_rule.lhs, right_rule.lhs):
                left_branch = left_rule.rhs + right_rule.lhs[overlap:]
                right_branch = left_rule.lhs[:-overlap] + right_rule.rhs
                lhs, rhs = orient(left_branch, right_branch)
                if (lhs, rhs) in rule_pairs:
                    continue
                assert (lhs, rhs) not in seen_pairs
                seen_pairs.add((lhs, rhs))
                left_normal, left_trace = normalize(left_branch, rules)
                right_normal, right_trace = normalize(right_branch, rules)
                assert left_normal == right_normal
                assert sorted((len(left_trace), len(right_trace))) == [0, 2]
                assert affine_signature(lhs) == affine_signature(rhs)
                prefixes, suffixes = balanced_cuts(lhs, rhs)
                assert len(prefixes) == 3 and prefixes[0] == 3
                first_extra, second_extra = prefixes[1:]
                assert 28 <= first_extra <= 32
                assert 53 <= second_extra <= 61
                second_cut_patterns[(3, first_extra, second_extra)] += 1
                second_rows.append(
                    CutRow(
                        name=f"g2:{left_index}>{right_index}@{overlap}",
                        generation=2,
                        lhs=lhs,
                        rhs=rhs,
                        prefix_cuts=prefixes,
                        suffix_cuts=suffixes,
                    )
                )

    assert len(first_rows) == 50
    assert len(first_extra_patterns) == 15
    assert sum(first_extra_patterns.values()) == 45
    assert len(second_rows) == len(seen_pairs) == 405
    assert len(second_cut_patterns) == 25
    assert sum(second_cut_patterns.values()) == 405

    rows = [asdict(row) for row in (*first_rows, *second_rows)]
    payload: dict[str, object] = {
        "alphabet": ["D", "T"],
        "balance": "equal dilation count",
        "local_gate": "letters differ immediately before and after every proper balanced cut",
        "rows": rows,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CutSummary(
        completed_rules=len(first_rows),
        base_rules=5,
        first_critical_rules=45,
        second_critical_pairs=len(second_rows),
        first_length_histogram=histogram([len(row.lhs) for row in first_rows]),
        first_extra_cut_histogram={
            f"{length},{cut},{length - cut}": count
            for (length, cut, _), count in sorted(first_extra_patterns.items())
        },
        second_length_histogram=histogram([len(row.lhs) for row in second_rows]),
        second_cut_histogram={
            f"{first},{second},{third}": count
            for (first, second, third), count in sorted(second_cut_patterns.items())
        },
        first_internal_bound=max(2 * len(row.lhs) - 5 for row in first_rows),
        second_internal_bound=max(2 * len(row.lhs) - 5 for row in second_rows),
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="two-generation contextual Parikh cuts certified",
    )
    assert summary.first_internal_bound == 113
    assert summary.second_internal_bound == 171
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

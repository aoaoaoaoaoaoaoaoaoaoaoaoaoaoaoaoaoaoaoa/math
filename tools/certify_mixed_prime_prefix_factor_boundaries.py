#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Reject the 11 surviving prefix-cloak pumps by local factor-boundary signatures."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import asdict, dataclass

from certify_mixed_prime_prefix_pump_suffixes import (
    FINITE_GEOMETRY_FAMILY,
    PARIKH_DEAD,
    maximum_feasible_suffix,
    periodic_suffix_delta,
    stabilization_power,
)
from certify_mixed_prime_pump_families import PUMP_SEEDS, PumpSeed, pumped_pair

BIGRAM_DEAD = frozenset({"l31-01", "l31-02", "l31-04", "l32-06", "l32-07", "l32-15"})
TRIGRAM_DEAD = frozenset({"l31-06", "l32-02", "l32-05", "l32-08", "l32-13"})


@dataclass(frozen=True, slots=True)
class FamilyRejection:
    """Complete factor-signature catalogue for one pump family."""

    family: str
    factor_length: int
    stabilization_power: int
    head_signatures: tuple[tuple[int, ...], ...]
    signature_l1_norms: tuple[int, ...]
    universal_boundary_signatures: int
    finite_replay_power: int


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact result of the all-family prefix-cloak boundary rejection."""

    input_families: int
    bigram_eliminations: int
    trigram_eliminations: int
    surviving_families: int
    bigram_boundary_signatures: int
    trigram_boundary_signatures: int
    certificate_sha256: str
    status: str


def binary_words(length: int) -> tuple[str, ...]:
    """All `D/T` words of one length in canonical order."""
    return tuple("".join(bits) for bits in itertools.product("DT", repeat=length))


def factor_patterns(length: int) -> tuple[str, ...]:
    """Canonical coordinate order for length-`r` factor-count vectors."""
    return binary_words(length)


def factor_signature(word: str, length: int) -> tuple[int, ...]:
    """Count every contiguous length-`r` factor in canonical coordinate order."""
    patterns = factor_patterns(length)
    return tuple(
        sum(
            word[index : index + length] == pattern
            for index in range(len(word) - length + 1)
        )
        for pattern in patterns
    )


def subtract_signatures(
    left: tuple[int, ...], right: tuple[int, ...]
) -> tuple[int, ...]:
    """Coordinatewise integer signature difference."""
    assert len(left) == len(right)
    return tuple(
        left_value - right_value for left_value, right_value in zip(left, right)
    )


def head_signature_delta(left: str, right: str, length: int) -> tuple[int, ...]:
    """Factor-count discrepancy between two equal-length cloak heads."""
    assert len(left) == len(right)
    return subtract_signatures(
        factor_signature(left, length), factor_signature(right, length)
    )


def boundary_representatives(length: int) -> tuple[str, ...]:
    """One word for every boundary type relevant to length-`r` crossing factors."""
    radius = length - 1
    short = tuple(
        word
        for word_length in range(1, 2 * radius)
        for word in binary_words(word_length)
    )
    long = tuple(
        left + right for left in binary_words(radius) for right in binary_words(radius)
    )
    representatives = short + long
    assert len(representatives) == len(set(representatives))
    return representatives


def universal_boundary_deltas(length: int) -> frozenset[tuple[int, ...]]:
    """Every factor discrepancy possible for `yzx` versus `xzy`."""
    representatives = boundary_representatives(length)
    deltas = {
        head_signature_delta(y + z + x, x + z + y, length)
        for x in representatives
        for y in representatives
        for z in representatives
    }
    maximum_l1 = 4 * (length - 1)
    assert all(sum(abs(value) for value in delta) <= maximum_l1 for delta in deltas)
    return frozenset(deltas)


def periodic_prefix(pump: str, length: int) -> str:
    """Prefix of one infinite two-letter pump word."""
    assert length >= 0 and len(pump) == 2
    return (pump * ((length + 1) // 2))[:length]


def stable_long_head_pair(seed: PumpSeed, residue: int) -> tuple[str, str]:
    """Cloak heads after removing a pump-tail suffix with `residue=2k-q`."""
    base_length = len(seed.left)
    left_tail_length = base_length - seed.left_cut
    right_tail_length = base_length - seed.right_cut
    left_pump_length = residue + left_tail_length
    right_pump_length = residue + right_tail_length
    assert left_pump_length >= 0 and right_pump_length >= 0
    left = seed.left[: seed.left_cut] + periodic_prefix(seed.pump, left_pump_length)
    right = seed.right[: seed.right_cut] + periodic_prefix(seed.pump, right_pump_length)
    assert len(left) == len(right)
    return left, right


def complete_head_catalog(seed: PumpSeed, length: int) -> frozenset[tuple[int, ...]]:
    """Symbolically enumerate every feasible balanced-suffix cloak-head signature."""
    base_length = len(seed.left)
    left_tail = seed.left[seed.left_cut :]
    right_tail = seed.right[seed.right_cut :]
    maximum_tail = max(len(left_tail), len(right_tail))
    threshold = stabilization_power(seed)
    catalog: set[tuple[int, ...]] = set()

    # Exact finite preperiod before all feasible suffixes are pump-tail confined.
    for power in range(threshold):
        left, right = pumped_pair(seed, power)
        for suffix_length in range(1, maximum_feasible_suffix(base_length, power) + 1):
            if left[-suffix_length:].count("D") != right[-suffix_length:].count("D"):
                continue
            catalog.add(
                head_signature_delta(
                    left[:-suffix_length], right[:-suffix_length], length
                )
            )

    # Fixed short suffixes persist as the common pump grows. Once the pump exceeds the factor
    # radius, one added pump block contributes the same internal factors on both sides.
    for suffix_length in range(1, maximum_tail):
        if periodic_suffix_delta(seed, left_tail, right_tail, suffix_length) != 0:
            continue
        left, right = pumped_pair(seed, threshold)
        delta = head_signature_delta(
            left[:-suffix_length], right[:-suffix_length], length
        )
        catalog.add(delta)
        for power in range(threshold + 1, threshold + 4):
            later_left, later_right = pumped_pair(seed, power)
            assert (
                head_signature_delta(
                    later_left[:-suffix_length], later_right[:-suffix_length], length
                )
                == delta
            )

    # Longer suffixes remove both fixed tails. Their heads depend only on t=2k-q. For each
    # balanced parity, finitely many short periodic remnants precede one stable local signature.
    for parity in (0, 1):
        representative = maximum_tail
        if representative % 2 != parity:
            representative += 1
        if periodic_suffix_delta(seed, left_tail, right_tail, representative) != 0:
            continue
        minimum_residue = -min(len(left_tail), len(right_tail))
        while minimum_residue % 2 != parity:
            minimum_residue += 1
        stable_residue = max(
            minimum_residue,
            length - 1 - len(left_tail),
            length - 1 - len(right_tail),
        )
        while stable_residue % 2 != parity:
            stable_residue += 1
        for residue in range(minimum_residue, stable_residue + 1, 2):
            left, right = stable_long_head_pair(seed, residue)
            catalog.add(head_signature_delta(left, right, length))
        stable_left, stable_right = stable_long_head_pair(seed, stable_residue)
        stable_delta = head_signature_delta(stable_left, stable_right, length)
        for residue in range(stable_residue + 2, stable_residue + 10, 2):
            later_left, later_right = stable_long_head_pair(seed, residue)
            assert head_signature_delta(later_left, later_right, length) == stable_delta

    # A broad finite replay catches any defect in the cell decomposition; it is not the all-depth
    # argument, which is the finite-preperiod plus local-periodic decomposition above.
    replay_power = 50
    replay_catalog: set[tuple[int, ...]] = set()
    for power in range(replay_power + 1):
        left, right = pumped_pair(seed, power)
        for suffix_length in range(1, maximum_feasible_suffix(base_length, power) + 1):
            if left[-suffix_length:].count("D") == right[-suffix_length:].count("D"):
                replay_catalog.add(
                    head_signature_delta(
                        left[:-suffix_length], right[:-suffix_length], length
                    )
                )
    assert replay_catalog <= catalog
    assert catalog
    return frozenset(catalog)


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Reject every post-Parikh prefix-cloak pump family."""
    by_identifier = {seed.identifier: seed for seed in PUMP_SEEDS}
    previous_dead = PARIKH_DEAD | {FINITE_GEOMETRY_FAMILY}
    input_families = by_identifier.keys() - previous_dead
    assert input_families == BIGRAM_DEAD | TRIGRAM_DEAD
    assert len(input_families) == 11

    universal = {length: universal_boundary_deltas(length) for length in (2, 3)}
    assert len(universal[2]) == 21
    assert len(universal[3]) == 1_203
    rows: list[FamilyRejection] = []
    for identifier in sorted(input_families):
        factor_length = 2 if identifier in BIGRAM_DEAD else 3
        seed = by_identifier[identifier]
        catalog = complete_head_catalog(seed, factor_length)
        assert catalog.isdisjoint(universal[factor_length])
        rows.append(
            FamilyRejection(
                family=identifier,
                factor_length=factor_length,
                stabilization_power=stabilization_power(seed),
                head_signatures=tuple(sorted(catalog)),
                signature_l1_norms=tuple(
                    sorted(sum(abs(value) for value in delta) for delta in catalog)
                ),
                universal_boundary_signatures=len(universal[factor_length]),
                finite_replay_power=50,
            )
        )

    payload: dict[str, object] = {
        "formal_head_equation": "head(L_k)=yzx and head(R_k)=xzy",
        "boundary_principle": (
            "internal length-r factors cancel; the discrepancy depends only on nonempty "
            "block boundary types and has l1 norm at most 4(r-1)"
        ),
        "boundary_catalogues": {
            "2": len(universal[2]),
            "3": len(universal[3]),
        },
        "family_rejections": [asdict(row) for row in rows],
        "surviving_families": [],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CertificateSummary(
        input_families=len(input_families),
        bigram_eliminations=len(BIGRAM_DEAD),
        trigram_eliminations=len(TRIGRAM_DEAD),
        surviving_families=0,
        bigram_boundary_signatures=len(universal[2]),
        trigram_boundary_signatures=len(universal[3]),
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="all 23 pumped prefix-cloak schemas are globally impossible",
    )
    return payload, summary


def main() -> None:
    """Print the compact summary or canonical full certificate."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    arguments = parser.parse_args()
    payload, summary = certify()
    output: object = payload if arguments.full else asdict(summary)
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()

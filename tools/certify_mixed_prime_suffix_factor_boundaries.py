#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Reject all 23 pump schemas as suffix-cloaked forks by trigram boundaries."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass

from certify_mixed_prime_prefix_factor_boundaries import (
    boundary_representatives,
    head_signature_delta,
)
from certify_mixed_prime_pump_families import PUMP_SEEDS, pumped_pair

FACTOR_LENGTH = 3
ADDRESS_CONTEXTS = ("", "DT", "TD")


@dataclass(frozen=True, slots=True)
class FamilyRejection:
    """Complete preperiod/stable trigram catalogue for one suffix cloak."""

    family: str
    preperiod_signatures: tuple[tuple[int, ...], ...]
    stable_signatures: tuple[tuple[int, ...], ...]
    maximum_signature_l1: int


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact result of the suffix-cloak pump-family extinction."""

    pump_families: int
    address_boundary_contexts: int
    universal_fork_signatures: int
    eliminated_families: int
    surviving_families: int
    certificate_sha256: str
    status: str


def universal_fork_deltas() -> frozenset[tuple[int, ...]]:
    """Every trigram discrepancy possible for `yzxyx` versus `xzyxy`."""
    representatives = boundary_representatives(FACTOR_LENGTH)
    return frozenset(
        head_signature_delta(
            y + z + x + y + x,
            x + z + y + x + y,
            FACTOR_LENGTH,
        )
        for x in representatives
        for y in representatives
        for z in representatives
    )


def contextual_signatures(power_left: str, power_right: str) -> set[tuple[int, ...]]:
    """All trigram discrepancies after an empty or aligned-address prefix."""
    return {
        head_signature_delta(
            context + power_left,
            context + power_right,
            FACTOR_LENGTH,
        )
        for context in ADDRESS_CONTEXTS
    }


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Certify the finite preperiod and one stable pump cell for every family."""
    universal = universal_fork_deltas()
    assert len(universal) == 1_243
    rows: list[FamilyRejection] = []
    for seed in PUMP_SEEDS:
        base_left, base_right = pumped_pair(seed, 0)
        one_left, one_right = pumped_pair(seed, 1)
        preperiod = contextual_signatures(base_left, base_right)
        stable = contextual_signatures(one_left, one_right)
        assert preperiod.isdisjoint(universal)
        assert stable.isdisjoint(universal)

        # Trigrams see two letters across a boundary. From one full pump onward, appending one
        # further two-letter period adds the same internal factors and preserves both junctions.
        for power in range(2, 9):
            later_left, later_right = pumped_pair(seed, power)
            assert contextual_signatures(later_left, later_right) == stable

        all_signatures = preperiod | stable
        rows.append(
            FamilyRejection(
                family=seed.identifier,
                preperiod_signatures=tuple(sorted(preperiod)),
                stable_signatures=tuple(sorted(stable)),
                maximum_signature_l1=max(
                    sum(abs(value) for value in signature)
                    for signature in all_signatures
                ),
            )
        )

    assert len(rows) == len(PUMP_SEEDS) == 23
    payload: dict[str, object] = {
        "physical_equation": "yzxyx=W*L_k and xzyxy=W*R_k",
        "factor_length": FACTOR_LENGTH,
        "address_contexts": list(ADDRESS_CONTEXTS),
        "address_context_reason": (
            "trigram crossing depends only on last two letters; every nonempty aligned "
            "address ends in DT or TD"
        ),
        "pump_stability": (
            "k=0 is the preperiod; for k>=1 one more two-letter pump preserves the "
            "trigram discrepancy"
        ),
        "universal_fork_signatures": len(universal),
        "family_rejections": [asdict(row) for row in rows],
        "surviving_families": [],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CertificateSummary(
        pump_families=len(PUMP_SEEDS),
        address_boundary_contexts=len(ADDRESS_CONTEXTS),
        universal_fork_signatures=len(universal),
        eliminated_families=len(rows),
        surviving_families=0,
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="all 23 pumped suffix-cloak schemas are globally impossible",
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

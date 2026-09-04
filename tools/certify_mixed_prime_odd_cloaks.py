#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Reject the infinite odd kernel family in both one-sided cloak orientations."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass

from certify_mixed_prime_suffix_factor_boundaries import (
    contextual_signatures,
    universal_fork_deltas,
)

ODD_LEFT_HEAD = "D" + "T" * 10 + "D" * 2 + "T" + "D" * 2 + "T" + "D" * 8
ODD_RIGHT_HEAD = (
    "T" * 2
    + "D" * 6
    + "T" * 2
    + "D" * 2
    + "TDTDT"
    + "D" * 2
    + "T" * 2
    + "D" * 2
    + "T" * 2
)
ODD_LEFT_TAIL = "DTDD"
ODD_RIGHT_TAIL = "DDTT"
ORIENTATIONS = ("forward", "reverse")


@dataclass(frozen=True, slots=True)
class OrientationRejection:
    """Complete trigram cells for one orientation of the odd relation."""

    orientation: str
    depth_zero_signatures: tuple[tuple[int, ...], ...]
    stable_positive_depth_signatures: tuple[tuple[int, ...], ...]


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact result of the odd-family one-sided-cloak extinction."""

    relation_family: str
    prefix_orientations_eliminated: int
    suffix_orientations_eliminated: int
    universal_fork_signatures: int
    suffix_cells_checked: int
    certificate_sha256: str
    status: str


def odd_pair(depth: int) -> tuple[str, str]:
    """Return the exact factorized odd-family relation at one pump depth."""
    pump = "DT" * depth
    return (
        ODD_LEFT_HEAD + pump + ODD_LEFT_TAIL,
        ODD_RIGHT_HEAD + pump + ODD_RIGHT_TAIL,
    )


def oriented_pair(depth: int, orientation: str) -> tuple[str, str]:
    """Orient the relation as the flat and nested physical fork words."""
    left, right = odd_pair(depth)
    match orientation:
        case "forward":
            return left, right
        case "reverse":
            return right, left
        case unreachable:
            raise AssertionError(unreachable)


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Certify both orientations by one preperiod and one stable trigram cell."""
    assert len(ODD_LEFT_HEAD) == len(ODD_RIGHT_HEAD) == 25
    for depth in range(9):
        left, right = odd_pair(depth)
        assert len(left) == len(right) == 29 + 2 * depth
        assert left.count("D") == right.count("D") == 16 + depth
        assert left.count("T") == right.count("T") == 13 + depth

    universal = universal_fork_deltas()
    assert len(universal) == 1_243
    rows: list[OrientationRejection] = []
    for orientation in ORIENTATIONS:
        depth_zero = contextual_signatures(*oriented_pair(0, orientation))
        stable = contextual_signatures(*oriented_pair(1, orientation))
        assert depth_zero.isdisjoint(universal)
        assert stable.isdisjoint(universal)

        # A trigram sees at most two letters across the pump/tail junction. Once one full `DT`
        # period is present, adding another contributes equal internal factors on both sides and
        # leaves every junction unchanged. Equality at depth zero is an extra collapse here.
        assert depth_zero == stable
        for depth in range(2, 9):
            assert contextual_signatures(*oriented_pair(depth, orientation)) == stable

        rows.append(
            OrientationRejection(
                orientation=orientation,
                depth_zero_signatures=tuple(sorted(depth_zero)),
                stable_positive_depth_signatures=tuple(sorted(stable)),
            )
        )

    payload: dict[str, object] = {
        "relation_family": "kernelOddFamilyLeft/kernelOddFamilyRight",
        "factorization": {
            "left": "oddFamilyLeftHead*(DT)^k*DTDD",
            "right": "oddFamilyRightHead*(DT)^k*DDTT",
        },
        "prefix_rejection": (
            "Lean: the unique positive proper Parikh-balanced suffix has length |L_k|-3, "
            "contradicting the physical gate 2(address_depth+suffix_length)<|L_k|"
        ),
        "suffix_equation": "yzxyx=W*L_k and xzyxy=W*R_k",
        "suffix_locality": (
            "the aligned address contributes only epsilon/DT/TD; depth zero and one stable "
            "positive-depth trigram cell exhaust every pump depth"
        ),
        "universal_fork_signatures": len(universal),
        "orientation_rejections": [asdict(row) for row in rows],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CertificateSummary(
        relation_family="odd mixed-prime kernel",
        prefix_orientations_eliminated=len(ORIENTATIONS),
        suffix_orientations_eliminated=len(rows),
        universal_fork_signatures=len(universal),
        suffix_cells_checked=sum(
            len(row.depth_zero_signatures) + len(row.stable_positive_depth_signatures)
            for row in rows
        ),
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="odd kernel family is impossible in both one-sided cloak orientations",
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

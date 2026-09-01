#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Certify 23 two-seed pump schemas in the mixed-prime affine kernel."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import asdict, dataclass

from certify_mixed_prime_completion import affine_signature, construct_rules


@dataclass(frozen=True, slots=True)
class PumpSeed:
    """One boundary-reduced relation and its side-specific two-letter pump cuts."""

    identifier: str
    left: str
    right: str
    pump: str
    left_cut: int
    right_cut: int


@dataclass(frozen=True, slots=True)
class PumpSummary:
    """Compact output of the exact pump-family audit."""

    families: int
    base_length_histogram: dict[str, int]
    pump_length: int
    seed_depths_required: tuple[int, int]
    completed_rules: int
    maximum_lhs_length: int
    maximum_pump_power_checked: int
    finite_occurrence_checks: int
    pump_signatures: dict[str, tuple[int, int, int]]
    certificate_sha256: str
    status: str


PUMP_SEEDS = (
    PumpSeed(
        "l31-01",
        "DTTTTTTDTTTTDTDDDTTTDDTDDDDDDDD",
        "TTDDDDDDDTDTDTTDTTDTDDTDTTDTTDT",
        "TD",
        30,
        29,
    ),
    PumpSeed(
        "l31-02",
        "DTTTTTTTTDDTDTDTDDTDDTTDDDDDDDD",
        "TTDDDDDDTDDTDTTDTDTDDTTDTTTDDDT",
        "DT",
        29,
        28,
    ),
    PumpSeed(
        "l31-03",
        "DTTTTTTTTTTDDTDDTDDDDDDDDDTDTDD",
        "TTDDDDDDTTDDTDTDTDDTTDDTTDTDDTT",
        "DT",
        25,
        25,
    ),
    PumpSeed(
        "l31-04",
        "DTTTTTTTTTTDDTDDTDTDTDDDDDDDDDD",
        "TTDDDDDDTDTTTDTDDTTDDTTDDTTDDDT",
        "DT",
        29,
        28,
    ),
    PumpSeed(
        "l31-05",
        "DTTTTTTDDTTTDTTDDTDDTDDDDDDDDDD",
        "TTDDDDDDDDDTTDTTDTTDDTTDDDDTDTT",
        "TD",
        30,
        28,
    ),
    PumpSeed(
        "l31-06",
        "DTTTTTTDDTDDDDTDDDTDDTDDDDDDDDT",
        "TTDDDDDDDDDDDDTDTDTTDDTTDTTDTDD",
        "DT",
        28,
        27,
    ),
    PumpSeed(
        "l31-07",
        "DTTTTTTDDTDDDDTTTDDDDDDDDDDDTDD",
        "TTDDDDDDDDDDDTDDTDTDDTTDTDDTDTT",
        "TD",
        28,
        28,
    ),
    PumpSeed(
        "l32-01",
        "DTTTTTTDDTDDDDTDDDTDDTDDDTDDDTDD",
        "TTDDDDDDDDDDDDTDTDTTDTDDTTDDTDTT",
        "TD",
        29,
        29,
    ),
    PumpSeed(
        "l32-02",
        "DTTTTTTDDTDDDDTDDTTDTDDDDDDDDDDT",
        "TTDDDDDDDDDDDDTDTTTDTDDDTTTTDTDD",
        "DT",
        29,
        28,
    ),
    PumpSeed(
        "l32-03",
        "DTTTTTTDDTDDTTTTDDTDDTDDDDDDDDDD",
        "TTDDDDDDDDDDTDTTDDTTDTDDTTDDTDTT",
        "TD",
        31,
        29,
    ),
    PumpSeed(
        "l32-04",
        "DTTTTTTDDTDTTDDTTDDTDDDDDDDDDTDD",
        "TTDDDDDDDDDDTTTDDDTTTTDDTDDTDDTT",
        "DT",
        28,
        26,
    ),
    PumpSeed(
        "l32-05",
        "DTTTTTTDDTTTDDDTDTDTDDDDDDDDDTDD",
        "TTDDDDDDDDDTDTTDTTTTDDTDDTDDTDDT",
        "DT",
        28,
        27,
    ),
    PumpSeed(
        "l32-06",
        "DTTTTTTDDTTTTTDDDDDDDDTDDDDDDDDT",
        "TTDDDDDDDDDTTTDTTDDDTTTDTDDTDTDD",
        "DT",
        29,
        26,
    ),
    PumpSeed(
        "l32-07",
        "DTTTTTTDDTTTTTDDDDDDTDDTDDDDDDDD",
        "TTDDDDDDDDDTTTTDDDTDDTDTDTTDDTDT",
        "TD",
        31,
        30,
    ),
    PumpSeed(
        "l32-08",
        "DTTTTTTDDTTTTTDDDTTDDDDTDDDDDDDD",
        "TTDDDDDDDDDTTTTDDTTDDDDTDTTTDTDT",
        "TD",
        31,
        30,
    ),
    PumpSeed(
        "l32-09",
        "DTTTTTTDTTDTTTDDTDDTDDDDDDDDDTDD",
        "TTDDDDDDDDTTTTDTDTDDTDDTDDTTDDTT",
        "DT",
        28,
        28,
    ),
    PumpSeed(
        "l32-10",
        "DTTTTTTTTDDTDTDTDDTDDDDTDTDDDTDD",
        "TTDDDDDDTDDTDTTDTDDTTDTTDTTDDDTT",
        "DT",
        28,
        28,
    ),
    PumpSeed(
        "l32-11",
        "DTTTTTTTTDDTDTDTDDTDDDDTDTDTDTDD",
        "TTDDDDDDTDDTDTTDTDDTTDTTTDDDTTTT",
        "DT",
        22,
        26,
    ),
    PumpSeed(
        "l32-12",
        "DTTTTTTTTDDTDTDTDDTDDDTDDDDDDDTT",
        "TTDDDDDDTDDTDTTDDTTTTDTTDDTTDTDD",
        "DT",
        28,
        28,
    ),
    PumpSeed(
        "l32-13",
        "DTTTTTTTTDDTDTDTDTDDDDTTDDDDDDDD",
        "TTDDDDDDDTTTDTDTTTDDDTDDDTTTDDDT",
        "DT",
        30,
        29,
    ),
    PumpSeed(
        "l32-14",
        "DTTTTTTTTDTTDTTTDTDDDDDDDDDTDTDD",
        "TTDDDDDDTDTDTTDTDTDTDTTTDDDTDTTT",
        "TD",
        27,
        28,
    ),
    PumpSeed(
        "l32-15",
        "DTTTTTTTTDTTDTTTDTDDDDTTDDDDDDDD",
        "TTDDDDDDTDTDTTDTDTDTTDTDTTTTDDDT",
        "DT",
        30,
        29,
    ),
    PumpSeed(
        "l32-16",
        "DTTTTTTTTTTDDTDDTTDDDDDDDDDDDTDD",
        "TTDDDDDTDDDTDDTDDTDTTDDTTTDDTDTT",
        "TD",
        29,
        29,
    ),
)


def pumped_pair(seed: PumpSeed, exponent: int) -> tuple[str, str]:
    """Insert ``seed.pump^exponent`` at the two certified cuts."""
    block = seed.pump * exponent
    return (
        seed.left[: seed.left_cut] + block + seed.left[seed.left_cut :],
        seed.right[: seed.right_cut] + block + seed.right[seed.right_cut :],
    )


def certify_pump_radix() -> dict[str, object]:
    """Check the common-diagonal power formulas for the two pump macros."""
    signatures = {pump: affine_signature(pump) for pump in ("DT", "TD")}
    assert signatures == {"DT": (6, 10, 15), "TD": (6, 15, 15)}
    for pump, (_, pump_offset, _) in signatures.items():
        for exponent in range(65):
            scale = 6**exponent
            denominator = 15**exponent
            offset = pump_offset * (denominator - scale) // 9
            assert affine_signature(pump * exponent) == (scale, offset, denominator)
            if exponent > 0:
                assert (denominator - scale) % 9 == 0
                assert offset % 5 == 0 and offset % 25 != 0
    return {
        "append_recurrence": "u(wS)=15*u(w)+b(S)*6^|w|",
        "fixed_length_code": "u=5*3^(n-1)*sum(d_i*2^(i-1)*5^(n-i)), d_i in {2,3}",
        "left_decoder": "successive reduction modulo 2",
        "right_decoder": "successive reduction modulo 5",
        "power_offset": "b*(15^k-6^k)/9",
        "signatures": signatures,
    }


def certify() -> tuple[dict[str, object], PumpSummary]:
    """Check the two action seeds and the finite irreducibility boundary basis."""
    rules = construct_rules()
    maximum_lhs_length = max(len(rule.lhs) for rule in rules)
    assert len(rules) == 50
    assert maximum_lhs_length == 59

    rows: list[dict[str, object]] = []
    occurrence_checks = 0
    maximum_pump_power = 0
    for index, seed in enumerate(PUMP_SEEDS, start=1):
        base_length = len(seed.left)
        assert base_length == len(seed.right) and base_length in (31, 32)
        assert len(seed.pump) == 2
        assert 0 < seed.left_cut < len(seed.left)
        assert 0 < seed.right_cut < len(seed.right)
        assert seed.left[0] != seed.right[0]
        assert seed.left[-1] != seed.right[-1]
        assert seed.left.count("D") == seed.right.count("D")

        base_left, base_right = pumped_pair(seed, 0)
        one_left, one_right = pumped_pair(seed, 1)
        alternate_pump = "TD" if seed.pump == "DT" else "DT"
        alternate_seed = PumpSeed(
            seed.identifier,
            seed.left,
            seed.right,
            alternate_pump,
            seed.left_cut,
            seed.right_cut,
        )
        alternate_left, alternate_right = pumped_pair(alternate_seed, 1)
        alternate_left_signature = affine_signature(alternate_left)
        alternate_right_signature = affine_signature(alternate_right)
        assert alternate_left_signature[::2] == alternate_right_signature[::2]
        alternate_discrepancy = (
            alternate_left_signature[1] - alternate_right_signature[1]
        )
        alternate_reader = alternate_discrepancy == 0
        assert affine_signature(base_left) == affine_signature(base_right)
        assert affine_signature(one_left) == affine_signature(one_right)
        assert (one_left, one_right) not in {
            (seed.pump + seed.left, seed.pump + seed.right),
            (seed.left + seed.pump, seed.right + seed.pump),
        }

        for word, cut in ((seed.left, seed.left_cut), (seed.right, seed.right_cut)):
            head, tail = word[:cut], word[cut:]
            for rule in rules:
                # An occurrence crossing both pump boundaries has `2k < |lhs|`. An occurrence
                # meeting at most one boundary stabilizes once the pump is longer than `lhs`.
                # Thus this finite interval contains every possible local redex window.
                saturation = (len(rule.lhs) + 1) // 2 + 1
                maximum_pump_power = max(maximum_pump_power, saturation)
                for exponent in range(saturation + 1):
                    occurrence_checks += 1
                    candidate = head + seed.pump * exponent + tail
                    assert rule.lhs not in candidate

        rows.append(
            {
                "family": index,
                "identifier": seed.identifier,
                "left": seed.left,
                "right": seed.right,
                "pump": seed.pump,
                "alternate_pump": alternate_pump,
                "alternate_pump_reader": alternate_reader,
                "alternate_offset_discrepancy": alternate_discrepancy,
                "left_cut": seed.left_cut,
                "right_cut": seed.right_cut,
                "base_signature": affine_signature(base_left),
                "one_pump_signature": affine_signature(one_left),
            }
        )

    assert len(PUMP_SEEDS) == 23
    assert len({seed.identifier for seed in PUMP_SEEDS}) == 23
    assert len({pumped_pair(seed, 0) for seed in PUMP_SEEDS}) == 23
    assert len({pumped_pair(seed, 1) for seed in PUMP_SEEDS}) == 23
    assert sum(bool(row["alternate_pump_reader"]) for row in rows) == 0
    assert maximum_pump_power == 31

    radix = certify_pump_radix()
    length_histogram = {
        str(length): count
        for length, count in sorted(
            Counter(len(seed.left) for seed in PUMP_SEEDS).items()
        )
    }
    assert length_histogram == {"31": 7, "32": 16}

    payload: dict[str, object] = {
        "families": rows,
        "length": "base_length+2k",
        "macro_radix": radix,
        "seed_depths_required": [0, 1],
        "propagation": "two-dimensional Cayley-Hamilton",
        "irreducibility_window": "two-boundary or stabilized one-boundary periodic-factor windows",
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = PumpSummary(
        families=len(rows),
        base_length_histogram=length_histogram,
        pump_length=2,
        seed_depths_required=(0, 1),
        completed_rules=len(rules),
        maximum_lhs_length=maximum_lhs_length,
        maximum_pump_power_checked=maximum_pump_power,
        finite_occurrence_checks=occurrence_checks,
        pump_signatures={pump: affine_signature(pump) for pump in ("DT", "TD")},
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="23 infinite affine-kernel pump schemas certified and 50-rule irreducible",
    )
    return payload, summary


def main() -> None:
    """Print either the compact summary or the canonical full certificate."""
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--full", action="store_true")
    mode.add_argument("--seed-manifest", action="store_true")
    arguments = parser.parse_args()
    if arguments.seed_manifest:
        print("identifier\tleft\tright\tpump\tleft_cut\tright_cut")
        for seed in PUMP_SEEDS:
            print(
                seed.identifier,
                seed.left,
                seed.right,
                seed.pump,
                seed.left_cut,
                seed.right_cut,
                sep="\t",
            )
        return
    payload, summary = certify()
    output: object = payload if arguments.full else asdict(summary)
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()

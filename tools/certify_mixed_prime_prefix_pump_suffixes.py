#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Certify the uniform balanced-suffix collapse of 12 prefix-cloak pump families."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass

from certify_mixed_prime_prefix_cloaks import solve_geometry
from certify_mixed_prime_pump_families import PUMP_SEEDS, PumpSeed, pumped_pair

PARIKH_DEAD = frozenset(
    {
        "l31-03",
        "l31-05",
        "l31-07",
        "l32-01",
        "l32-03",
        "l32-04",
        "l32-09",
        "l32-10",
        "l32-11",
        "l32-14",
        "l32-16",
    }
)
FINITE_GEOMETRY_FAMILY = "l32-12"


@dataclass(frozen=True, slots=True)
class UniformParikhRejection:
    """Exact eventually periodic certificate for one uniformly dead pump family."""

    family: str
    base_length: int
    pump: str
    left_tail: str
    right_tail: str
    stabilization_power: int
    finite_powers_checked: int
    finite_suffixes_checked: int
    preperiod_balanced_suffixes: int
    short_suffix_deltas: tuple[tuple[int, int], ...]
    periodic_delta_even: int
    periodic_delta_odd: int


@dataclass(frozen=True, slots=True)
class FiniteGeometryRejection:
    """Finite physical-factor census before periodic Parikh extinction."""

    family: str
    stabilization_power: int
    finite_powers_checked: int
    branch_orientations: int
    geometries: int
    survivors: int


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact result of the global suffix-Parikh pump-family cut."""

    pump_families: int
    uniform_parikh_eliminations: int
    finite_geometry_eliminations: int
    surviving_families: int
    finite_geometries: int
    certificate_sha256: str
    status: str


def maximum_feasible_suffix(base_length: int, power: int) -> int:
    """Largest `q` satisfying the formal gate `2q < base_length+2*power`."""
    return (base_length + 2 * power - 1) // 2


def stabilization_power(seed: PumpSeed) -> int:
    """First power where every feasible suffix stays inside both pump-plus-tail words."""
    base_length = len(seed.left)
    minimum_tail = min(
        base_length - seed.left_cut,
        base_length - seed.right_cut,
    )
    power = 0
    while maximum_feasible_suffix(base_length, power) > 2 * power + minimum_tail:
        power += 1
    # The left side grows by one and the right side by two thereafter, so this is permanent.
    assert maximum_feasible_suffix(base_length, power + 1) <= (
        2 * (power + 1) + minimum_tail
    )
    return power


def periodic_suffix_d_count(pump: str, tail: str, suffix_length: int) -> int:
    """Count `D` in a suffix confined to `pump^k + tail`, independently of `k`."""
    if suffix_length <= len(tail):
        return tail[-suffix_length:].count("D")
    pump_length = suffix_length - len(tail)
    assert len(pump) == 2 and pump.count("D") == 1
    return tail.count("D") + pump_length // 2 + (pump_length % 2) * int(pump[-1] == "D")


def periodic_suffix_delta(
    seed: PumpSeed,
    left_tail: str,
    right_tail: str,
    suffix_length: int,
) -> int:
    """Parikh difference of the two eventually periodic suffixes."""
    return periodic_suffix_d_count(
        seed.pump, left_tail, suffix_length
    ) - periodic_suffix_d_count(seed.pump, right_tail, suffix_length)


def certify_uniform_parikh(
    seed: PumpSeed, *, preperiod_must_be_dead: bool = True
) -> UniformParikhRejection:
    """Prove eventual Parikh extinction, optionally requiring a dead preperiod."""
    base_length = len(seed.left)
    assert len(seed.right) == base_length
    left_tail = seed.left[seed.left_cut :]
    right_tail = seed.right[seed.right_cut :]
    threshold = stabilization_power(seed)

    finite_suffixes_checked = 0
    preperiod_balanced_suffixes = 0
    for power in range(threshold):
        left, right = pumped_pair(seed, power)
        for suffix_length in range(1, maximum_feasible_suffix(base_length, power) + 1):
            finite_suffixes_checked += 1
            balanced = left[-suffix_length:].count("D") == right[-suffix_length:].count(
                "D"
            )
            preperiod_balanced_suffixes += int(balanced)
            if preperiod_must_be_dead:
                assert not balanced

    maximum_tail = max(len(left_tail), len(right_tail))
    short_deltas = tuple(
        (
            suffix_length,
            periodic_suffix_delta(seed, left_tail, right_tail, suffix_length),
        )
        for suffix_length in range(1, maximum_tail)
    )
    assert all(delta != 0 for _, delta in short_deltas)

    parity_deltas: dict[int, int] = {}
    for parity in (0, 1):
        representative = maximum_tail
        if representative % 2 != parity:
            representative += 1
        delta = periodic_suffix_delta(seed, left_tail, right_tail, representative)
        # Beyond both fixed tails, the exact floor formula is two-periodic in `q`.
        for suffix_length in range(representative, representative + 12, 2):
            assert (
                periodic_suffix_delta(seed, left_tail, right_tail, suffix_length)
                == delta
            )
        assert delta != 0
        parity_deltas[parity] = delta

    return UniformParikhRejection(
        family=seed.identifier,
        base_length=base_length,
        pump=seed.pump,
        left_tail=left_tail,
        right_tail=right_tail,
        stabilization_power=threshold,
        finite_powers_checked=threshold,
        finite_suffixes_checked=finite_suffixes_checked,
        preperiod_balanced_suffixes=preperiod_balanced_suffixes,
        short_suffix_deltas=short_deltas,
        periodic_delta_even=parity_deltas[0],
        periodic_delta_odd=parity_deltas[1],
    )


def certify_finite_geometry(seed: PumpSeed) -> FiniteGeometryRejection:
    """Reject the finite physical residue before this family's Parikh gate stabilizes."""
    base_length = len(seed.left)
    threshold = stabilization_power(seed)
    assert seed.identifier == FINITE_GEOMETRY_FAMILY
    assert threshold == 11
    geometries = 0
    survivors = 0
    for power in range(threshold):
        seed_left, seed_right = pumped_pair(seed, power)
        cloak_length = len(seed_left)
        feasible_balanced = [
            suffix_length
            for suffix_length in range(
                1, maximum_feasible_suffix(base_length, power) + 1
            )
            if seed_left[-suffix_length:].count("D")
            == seed_right[-suffix_length:].count("D")
        ]
        assert feasible_balanced == [2 * power + 5]
        for cloak_left, cloak_right in (
            (seed_left, seed_right),
            (seed_right, seed_left),
        ):
            for suffix_length in feasible_balanced:
                for address_depth in range(cloak_length):
                    if 2 * (address_depth + suffix_length) >= cloak_length:
                        continue
                    data_length = 2 * address_depth + suffix_length
                    z_length = cloak_length - 2 * address_depth - 2 * suffix_length
                    assert z_length > 0
                    for x_length in range(1, data_length):
                        y_length = data_length - x_length
                        geometries += 1
                        witness, _ = solve_geometry(
                            cloak_left,
                            cloak_right,
                            address_depth,
                            x_length,
                            y_length,
                            z_length,
                        )
                        survivors += int(witness is not None)
    assert geometries == 2_288
    assert survivors == 0
    return FiniteGeometryRejection(
        family=seed.identifier,
        stabilization_power=threshold,
        finite_powers_checked=threshold,
        branch_orientations=2,
        geometries=geometries,
        survivors=survivors,
    )


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Certify 11 uniform Parikh deaths and the one finite-geometry residue."""
    by_identifier = {seed.identifier: seed for seed in PUMP_SEEDS}
    assert len(by_identifier) == len(PUMP_SEEDS) == 23
    assert PARIKH_DEAD <= by_identifier.keys()
    parikh_rows = [
        certify_uniform_parikh(by_identifier[identifier])
        for identifier in sorted(PARIKH_DEAD)
    ]

    finite_seed = by_identifier[FINITE_GEOMETRY_FAMILY]
    finite_row = certify_finite_geometry(finite_seed)
    # At and beyond power 11, the same exact periodic calculation kills every feasible suffix.
    eventual_finite_row = certify_uniform_parikh(
        finite_seed, preperiod_must_be_dead=False
    )
    assert eventual_finite_row.stabilization_power == finite_row.stabilization_power

    dead = PARIKH_DEAD | {FINITE_GEOMETRY_FAMILY}
    surviving = sorted(by_identifier.keys() - dead)
    assert len(surviving) == 11
    payload: dict[str, object] = {
        "formal_gate": {
            "balanced_suffix": "count_D(suffix_q(L_k))=count_D(suffix_q(R_k))",
            "size": "2*(address_depth+q)<base_length+2k",
        },
        "uniform_parikh_rejections": [asdict(row) for row in parikh_rows],
        "finite_geometry_rejection": asdict(finite_row),
        "finite_family_eventual_parikh_rejection": asdict(eventual_finite_row),
        "surviving_families": surviving,
        "periodic_argument": (
            "after stabilization every feasible suffix lies in pump^k+tail; "
            "the exact D-count is tail_D+floor(r/2)+odd(r)*last_D"
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CertificateSummary(
        pump_families=len(PUMP_SEEDS),
        uniform_parikh_eliminations=len(parikh_rows),
        finite_geometry_eliminations=1,
        surviving_families=len(surviving),
        finite_geometries=finite_row.geometries,
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="12 prefix-cloak pump families eliminated globally; 11 remain",
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

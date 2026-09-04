#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Reject every base mixed-prime pump cloak as a physical prefix-cloaked fork."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import asdict, dataclass

from certify_mixed_prime_completion import affine_signature
from certify_mixed_prime_pump_families import PUMP_SEEDS, pumped_pair


class ParityDsu:
    """Union-find for equations `value(left) xor value(right) = parity`."""

    def __init__(self, cardinality: int) -> None:
        self.parent = list(range(cardinality))
        self.rank = [0] * cardinality
        self.parity = [0] * cardinality

    def find(self, node: int) -> tuple[int, int]:
        """Return the root and the parity from `node` to that root."""
        parent = self.parent[node]
        if parent == node:
            return node, 0
        root, upper_parity = self.find(parent)
        self.parity[node] ^= upper_parity
        self.parent[node] = root
        return root, self.parity[node]

    def unite(self, left: int, right: int, parity: int) -> bool:
        """Add one parity equation, returning false exactly on contradiction."""
        left_root, left_parity = self.find(left)
        right_root, right_parity = self.find(right)
        if left_root == right_root:
            return left_parity ^ right_parity == parity
        if self.rank[left_root] < self.rank[right_root]:
            left_root, right_root = right_root, left_root
            left_parity, right_parity = right_parity, left_parity
        self.parent[right_root] = left_root
        self.parity[right_root] = left_parity ^ right_parity ^ parity
        if self.rank[left_root] == self.rank[right_root]:
            self.rank[left_root] += 1
        return True


@dataclass(frozen=True, slots=True)
class RejectedGeometry:
    """One length geometry and the first inconsistent target binding."""

    family: str
    branch_orientation: str
    cloak_length: int
    address_depth: int
    x_length: int
    y_length: int
    z_length: int
    conflict_position: int
    conflict_branch: str


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact result of the complete base-prefix-cloak census."""

    families: int
    branch_orientations: int
    base_length_histogram: dict[str, int]
    maximum_feasible_address_depth: int
    geometries: int
    survivors: int
    certificate_sha256: str
    status: str


@dataclass(frozen=True, slots=True)
class ForkLayout:
    """Variable-letter indices in `YZXYX` and `XZYXY`."""

    left: tuple[int, ...]
    right: tuple[int, ...]
    variable_count: int

    @staticmethod
    def construct(x_length: int, y_length: int, z_length: int) -> ForkLayout:
        x = tuple(range(x_length))
        y = tuple(range(x_length, x_length + y_length))
        z = tuple(range(x_length + y_length, x_length + y_length + z_length))
        return ForkLayout(
            left=y + z + x + y + x,
            right=x + z + y + x + y,
            variable_count=x_length + y_length + z_length,
        )


@dataclass(frozen=True, slots=True)
class ForkWitness:
    """A satisfying assignment, retained only to make any failed rejection explicit."""

    address: str
    x: str
    y: str
    z: str


def _letter(value: int) -> str:
    return "T" if value else "D"


def solve_geometry(
    cloak_left: str,
    cloak_right: str,
    address_depth: int,
    x_length: int,
    y_length: int,
    z_length: int,
) -> tuple[ForkWitness | None, tuple[int, str] | None]:
    """Solve one factorization exactly as a finite system of parity equations."""
    layout = ForkLayout.construct(x_length, y_length, z_length)
    cloak_length = len(cloak_left)
    assert len(cloak_right) == cloak_length
    assert len(layout.left) == cloak_length + 2 * address_depth

    address_start = cloak_length
    first_address_variable = layout.variable_count
    constant = first_address_variable + address_depth
    dsu = ParityDsu(constant + 1)

    def bind(variable: int, position: int, cloak: str) -> bool:
        if position < address_start:
            target = constant
            parity = int(cloak[position] == "T")
        else:
            address_position = position - address_start
            target = first_address_variable + address_position // 2
            parity = address_position % 2
        return dsu.unite(variable, target, parity)

    for position, (left_variable, right_variable) in enumerate(
        zip(layout.left, layout.right, strict=True)
    ):
        if not bind(left_variable, position, cloak_left):
            return None, (position, "left")
        if not bind(right_variable, position, cloak_right):
            return None, (position, "right")

    constant_root, constant_parity = dsu.find(constant)

    def value(variable: int) -> int:
        root, parity = dsu.find(variable)
        root_value = constant_parity if root == constant_root else 0
        return root_value ^ parity

    variables = [_letter(value(variable)) for variable in range(layout.variable_count)]
    address = "".join(
        "TD" if value(first_address_variable + index) else "DT"
        for index in range(address_depth)
    )
    x = "".join(variables[:x_length])
    y = "".join(variables[x_length : x_length + y_length])
    z = "".join(variables[x_length + y_length :])
    witness = ForkWitness(address=address, x=x, y=y, z=z)
    assert y + z + x + y + x == cloak_left + address
    assert x + z + y + x + y == cloak_right + address
    return witness, None


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Enumerate exactly every geometry admitted by the formal strict size bound."""
    rows: list[RejectedGeometry] = []
    survivors: list[dict[str, object]] = []
    maximum_depth = 0
    for seed in PUMP_SEEDS:
        seed_left, seed_right = pumped_pair(seed, 0)
        cloak_length = len(seed_left)
        assert len(seed_right) == cloak_length
        assert seed_left != seed_right
        assert affine_signature(seed_left) == affine_signature(seed_right)
        for branch_orientation, (cloak_left, cloak_right) in (
            ("seed", (seed_left, seed_right)),
            ("swapped", (seed_right, seed_left)),
        ):
            for address_depth in range(cloak_length):
                for x_length in range(1, cloak_length):
                    for y_length in range(1, cloak_length):
                        data_length = x_length + y_length
                        if not 2 * address_depth < data_length < cloak_length:
                            continue
                        z_length = (
                            cloak_length
                            + 2 * address_depth
                            - 2 * x_length
                            - 2 * y_length
                        )
                        if z_length <= 0:
                            continue
                        maximum_depth = max(maximum_depth, address_depth)
                        witness, conflict = solve_geometry(
                            cloak_left,
                            cloak_right,
                            address_depth,
                            x_length,
                            y_length,
                            z_length,
                        )
                        if witness is not None:
                            survivors.append(
                                {
                                    "family": seed.identifier,
                                    "branch_orientation": branch_orientation,
                                    "address_depth": address_depth,
                                    "witness": asdict(witness),
                                }
                            )
                            continue
                        assert conflict is not None
                        conflict_position, conflict_branch = conflict
                        rows.append(
                            RejectedGeometry(
                                family=seed.identifier,
                                branch_orientation=branch_orientation,
                                cloak_length=cloak_length,
                                address_depth=address_depth,
                                x_length=x_length,
                                y_length=y_length,
                                z_length=z_length,
                                conflict_position=conflict_position,
                                conflict_branch=conflict_branch,
                            )
                        )

    assert len(PUMP_SEEDS) == 23
    assert maximum_depth == 14
    assert len(rows) == 77_280
    assert not survivors
    payload: dict[str, object] = {
        "scope": "23 base prefix cloaks in both branch orientations",
        "formal_size_gate": "2*address_depth < x_length+y_length < cloak_length",
        "physical_length": "2*x_length+2*y_length+z_length=cloak_length+2*address_depth",
        "letter_system": "D=0, T=1; each address macro is (bit,bit xor 1)",
        "rows": [asdict(row) for row in rows],
        "survivors": survivors,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    histogram = {
        str(length): count
        for length, count in sorted(
            Counter(len(seed.left) for seed in PUMP_SEEDS).items()
        )
    }
    assert histogram == {"31": 7, "32": 16}
    summary = CertificateSummary(
        families=len(PUMP_SEEDS),
        branch_orientations=2,
        base_length_histogram=histogram,
        maximum_feasible_address_depth=maximum_depth,
        geometries=len(rows),
        survivors=len(survivors),
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="all 23 base prefix cloaks rejected as physical reduced forks",
    )
    return payload, summary


def main() -> None:
    """Print the compact summary or the canonical full certificate."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    arguments = parser.parse_args()
    payload, summary = certify()
    output: object = payload if arguments.full else asdict(summary)
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()

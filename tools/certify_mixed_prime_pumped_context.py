#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Reject the finite family-six cut-27 contextual-fork residue exactly."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass

LEFT_BASE = "DTTTTTTDDTDDDDTDDDTDDTDDDDDDDDT"
RIGHT_BASE = "TTDDDDDDDDDDDDTDTDTTDDTTDTTDTDD"
PUMP = "DT"
LEFT_CUT = 28
RIGHT_CUT = 27


@dataclass(frozen=True, slots=True)
class RejectedGeometry:
    """One assignment-complete length geometry and its first forced letter conflict."""

    power: int
    orientation: str
    x_length: int
    y_length: int
    z_length: int
    prefix_length: int
    suffix_length: int
    conflict_position: int
    conflict_kind: str


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact finite-residue certificate result."""

    maximum_power: int
    orientations: int
    geometries: int
    survivors: int
    certificate_sha256: str
    status: str


class LetterDsu:
    """Equality closure for variable letters with optional `D` or `T` bindings."""

    def __init__(self, cardinality: int) -> None:
        self.parent = list(range(cardinality))
        self.rank = [0] * cardinality
        self.value: list[str | None] = [None] * cardinality

    def find(self, element: int) -> int:
        root = element
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[element] != element:
            successor = self.parent[element]
            self.parent[element] = root
            element = successor
        return root

    def merge(self, left: int, right: int) -> bool:
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return True
        if self.rank[left_root] < self.rank[right_root]:
            left_root, right_root = right_root, left_root
        left_value = self.value[left_root]
        right_value = self.value[right_root]
        if (
            left_value is not None
            and right_value is not None
            and left_value != right_value
        ):
            return False
        self.parent[right_root] = left_root
        self.value[left_root] = left_value if left_value is not None else right_value
        if self.rank[left_root] == self.rank[right_root]:
            self.rank[left_root] += 1
        return True

    def bind(self, element: int, value: str) -> bool:
        root = self.find(element)
        existing = self.value[root]
        if existing is not None:
            return existing == value
        self.value[root] = value
        return True


@dataclass(frozen=True, slots=True)
class ForkLayout:
    """Variable-letter positions in `YZXYX` and `XZYXY`."""

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

    def first_conflict(
        self,
        relation_left: str,
        relation_right: str,
        prefix_length: int,
    ) -> tuple[int, str] | None:
        dsu = LetterDsu(self.variable_count)
        relation_end = prefix_length + len(relation_left)
        for position, (left, right) in enumerate(
            zip(self.left, self.right, strict=True)
        ):
            if position < prefix_length or relation_end <= position:
                if not dsu.merge(left, right):
                    return position, "context equality"
                continue
            relation_position = position - prefix_length
            if not dsu.bind(left, relation_left[relation_position]):
                return position, "left relation binding"
            if not dsu.bind(right, relation_right[relation_position]):
                return position, "right relation binding"
        return None


def pumped_words(power: int) -> tuple[str, str]:
    """Construct family six at pump power `power`."""
    left = LEFT_BASE[:LEFT_CUT] + PUMP * power + LEFT_BASE[LEFT_CUT:]
    right = RIGHT_BASE[:RIGHT_CUT] + PUMP * power + RIGHT_BASE[RIGHT_CUT:]
    assert len(left) == len(right) == 31 + 2 * power
    return left, right


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Enumerate every geometry allowed by the formal cut-27 residue."""
    assert len(LEFT_BASE) == len(RIGHT_BASE) == 31
    rows: list[RejectedGeometry] = []
    survivors: list[tuple[int, str, int]] = []
    for power in range(12):
        left, right = pumped_words(power)
        suffix_length = 2 * power + 1
        for orientation, (x_length, y_length) in (
            ("forward", (2 * power + 3, 2 * power + 2)),
            ("reverse", (2 * power + 2, 2 * power + 3)),
        ):
            for prefix_length in range(min(x_length, y_length)):
                z_length = prefix_length + 22 - 4 * power
                if z_length <= 0:
                    continue
                layout = ForkLayout.construct(x_length, y_length, z_length)
                total_length = len(layout.left)
                assert total_length == prefix_length + len(left) + suffix_length
                conflict = layout.first_conflict(left, right, prefix_length)
                if conflict is None:
                    survivors.append((power, orientation, prefix_length))
                    continue
                conflict_position, conflict_kind = conflict
                rows.append(
                    RejectedGeometry(
                        power=power,
                        orientation=orientation,
                        x_length=x_length,
                        y_length=y_length,
                        z_length=z_length,
                        prefix_length=prefix_length,
                        suffix_length=suffix_length,
                        conflict_position=conflict_position,
                        conflict_kind=conflict_kind,
                    )
                )
    assert len(rows) == 156
    assert not survivors
    payload: dict[str, object] = {
        "family": "sixth length-31 pump schema",
        "left_base": LEFT_BASE,
        "right_base": RIGHT_BASE,
        "pump": PUMP,
        "left_cut": LEFT_CUT,
        "right_cut": RIGHT_CUT,
        "residue": {
            "power": "0 <= k <= 11",
            "suffix_length": "2k+1",
            "tail_lengths": "{2k+3,2k+2}",
            "prefix_internal": "p < min(|X|,|Y|)",
            "toggle_length": "p+22-4k > 0",
        },
        "rows": [asdict(row) for row in rows],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CertificateSummary(
        maximum_power=11,
        orientations=2,
        geometries=len(rows),
        survivors=len(survivors),
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="family-six cut-27 literal residue rejected",
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

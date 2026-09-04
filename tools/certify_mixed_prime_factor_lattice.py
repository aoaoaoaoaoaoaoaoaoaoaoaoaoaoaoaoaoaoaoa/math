#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Certify saturation of short factor-count lattices by each mixed-prime rule."""

from __future__ import annotations

import hashlib
import itertools
import json
from dataclasses import asdict, dataclass

# PEP 723 supplies SymPy at script runtime; standalone ty does not load that environment.
import sympy as sp  # ty: ignore[unresolved-import]
from sympy.matrices.normalforms import (  # ty: ignore[unresolved-import]
    hermite_normal_form,
)

# Direct script execution makes the sibling tools directory the import root. The LSP cannot
# model that runtime path, so this one module-resolution exception is irreducible.
from certify_mixed_prime_completion import (  # ty: ignore[unresolved-import, unused-ignore-comment]
    BASE_RULES,
    Rule,
)

ALPHABET = "DT"
MINIMUM_WIDTH = 2
MAXIMUM_WIDTH = 6
RANK_PRIMES = (2, 3, 5, 7)
EXPECTED_CERTIFICATE_SHA256 = (
    "ee43620eb3cd33ef4558a89e0e8c593fb98b4beee5334983e76898f6792e0b47"
)

type Vector = tuple[int, ...]


@dataclass(frozen=True, slots=True)
class SaturationCell:
    """Exact result for one base relation and one factor width."""

    rule: str
    width: int
    contexts: int
    distinct_moves: int
    augmentation_rank: int
    hermite_determinant: int
    row_sha256: str


def words_upto(radius: int) -> tuple[str, ...]:
    """Enumerate every binary word of length at most ``radius``."""
    return tuple(
        "".join(letters)
        for length in range(radius + 1)
        for letters in itertools.product(ALPHABET, repeat=length)
    )


def factor_counts(word: str, width: int) -> Vector:
    """Count overlapping width-``width`` factors in binary lexical order."""
    counts = [0] * (1 << width)
    for start in range(len(word) - width + 1):
        index = 0
        for letter in word[start : start + width]:
            index = (index << 1) | int(letter == "T")
        counts[index] += 1
    return tuple(counts)


def contextual_move(rule: Rule, prefix: str, suffix: str, width: int) -> Vector:
    """Return Φ_r(P·lhs·Q) − Φ_r(P·rhs·Q)."""
    left = factor_counts(prefix + rule.lhs + suffix, width)
    right = factor_counts(prefix + rule.rhs + suffix, width)
    return tuple(a - b for a, b in zip(left, right, strict=True))


def modular_rank(rows: tuple[Vector, ...], prime: int) -> int:
    """Compute exact row rank over one prime field."""
    basis: dict[int, list[int]] = {}
    for row in rows:
        vector = [entry % prime for entry in row]
        for pivot, basis_row in sorted(basis.items()):
            if vector[pivot] == 0:
                continue
            scale = vector[pivot]
            vector = [
                (entry - scale * basis_entry) % prime
                for entry, basis_entry in zip(vector, basis_row, strict=True)
            ]
        pivot = next((index for index, entry in enumerate(vector) if entry), None)
        if pivot is None:
            continue
        inverse = pow(vector[pivot], -1, prime)
        basis[pivot] = [(entry * inverse) % prime for entry in vector]
    return len(basis)


def row_digest(rows: tuple[Vector, ...]) -> str:
    """Hash a canonical serialization of the complete contextual move set."""
    payload = json.dumps(rows, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()


def certify_cell(rule: Rule, width: int) -> SaturationCell:
    """Prove one projected contextual lattice is the full integer lattice."""
    contexts = words_upto(width - 1)
    moves = tuple(
        sorted(
            {
                contextual_move(rule, prefix, suffix, width)
                for prefix in contexts
                for suffix in contexts
            }
        )
    )
    assert all(sum(move) == 0 for move in moves)

    # Deleting the final coordinate identifies the augmentation lattice
    # {v : Σv=0} with ℤ^(2^r−1).
    projected = tuple(move[:-1] for move in moves)
    rank = (1 << width) - 1
    columns = sp.Matrix(
        [[move[coordinate] for move in projected] for coordinate in range(rank)]
    )
    hermite = hermite_normal_form(columns)
    assert hermite.shape == (rank, rank)
    assert hermite == sp.eye(rank)
    determinant = abs(int(hermite.det()))
    assert determinant == 1
    assert all(modular_rank(projected, prime) == rank for prime in RANK_PRIMES)

    return SaturationCell(
        rule=rule.name,
        width=width,
        contexts=len(contexts),
        distinct_moves=len(moves),
        augmentation_rank=rank,
        hermite_determinant=determinant,
        row_sha256=row_digest(moves),
    )


def main() -> None:
    """Replay every finite lattice certificate and print its canonical digest."""
    assert all(
        len(rule.lhs) == len(rule.rhs)
        and rule.lhs.count("D") == rule.rhs.count("D")
        and rule.lhs.count("T") == rule.rhs.count("T")
        for rule in BASE_RULES
    )
    cells = tuple(
        certify_cell(rule, width)
        for rule in BASE_RULES
        for width in range(MINIMUM_WIDTH, MAXIMUM_WIDTH + 1)
    )
    payload = json.dumps(
        [asdict(cell) for cell in cells],
        sort_keys=True,
        separators=(",", ":"),
    )
    digest = hashlib.sha256(payload.encode()).hexdigest()
    assert digest == EXPECTED_CERTIFICATE_SHA256
    print(
        json.dumps(
            {"cells": [asdict(cell) for cell in cells], "sha256": digest}, indent=2
        )
    )


if __name__ == "__main__":
    main()

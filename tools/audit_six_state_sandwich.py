#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Audit exact sandwich saturation in the canonical six-state mortality families."""

from __future__ import annotations

from collections import deque
from itertools import permutations

# PEP 723 installs SymPy only in the script runtime; standalone ty cannot discover that
# ephemeral environment. The audit explicitly permits this single module-resolution exception.
import sympy as sp  # ty: ignore[unresolved-import]

MODULUS = 1_000_003
BLOCK_DIMENSION = 3
PACKED_DIMENSION = 6

type Matrix3 = tuple[tuple[int, int, int], tuple[int, int, int], tuple[int, int, int]]
type Matrix6 = tuple[tuple[int, ...], ...]


def ternary_code(bits: str) -> int:
    value = 0
    for bit in bits:
        value = 3 * value + (2 if bit == "1" else 1)
    return value


def paired_determinants() -> tuple[sp.Expr, sp.Expr]:
    ρ, lower_value, lower_scale = sp.symbols("rho V B")
    marker_value = (5 * ρ - 1) / 2
    upper_b_value = (15 * ρ + 1) / 2

    raw_b = sp.Matrix(
        [
            [1, 0, 0, 0, 0, 0],
            [0, 0, 0, 1, 0, 0],
            [0, 0, 0, 0, 1, 0],
            [25, 27, 0, 0, 0, 0],
            [upper_b_value, 0, 9 * ρ, 0, 0, 0],
            [1, 3, 0, 0, 0, 0],
        ]
    )
    raw_c = sp.Matrix(
        [
            [1, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 1],
            [0, 0, 0, 0, 1, 0],
            [lower_value, lower_scale, 0, 0, 0, 0],
            [2, 0, 3, 0, 0, 0],
            [1, 3, 0, 0, 0, 0],
        ]
    )
    a0 = raw_b.T
    a1 = raw_c.T
    column = sp.Matrix([marker_value, -1, 3 * ρ, 0, 0, 0])
    row = sp.Matrix([[1, 0, 0, 0, 0, 0]])

    reachable = sp.Matrix.hstack(
        column,
        a0 * column,
        a1 * column,
        a0**2 * column,
        a1 * a0 * column,
        a0**3 * column,
    )
    observable = sp.Matrix.vstack(
        row,
        row * a0,
        row * a1,
        row * a0**2,
        row * a0 * a1,
        row * a0**3,
    )

    reachable_factor = (
        sp.Rational(81, 2)
        * ρ**2
        * (ρ - 3) ** 2
        * (17 * lower_scale - 18 * lower_value + 18 * ρ - 33)
    )
    observable_factor = (
        18
        * (15 * ρ + 1)
        * (
            45 * lower_value * ρ**2
            - 372 * lower_value * ρ
            - 25 * lower_value
            - 1125 * ρ**2
            + 3300 * ρ
            + 1825
        )
    )

    reachable_det = sp.factor(reachable.det())
    observable_det = sp.factor(observable.det())
    assert sp.factor(reachable_det - reachable_factor) == 0
    assert sp.factor(observable_det - observable_factor) == 0
    return reachable_det, observable_det


def matrix_mul(left: Matrix6, right: Matrix6) -> Matrix6:
    return tuple(
        tuple(
            sum(left[i][k] * right[k][j] for k in range(PACKED_DIMENSION)) % MODULUS
            for j in range(PACKED_DIMENSION)
        )
        for i in range(PACKED_DIMENSION)
    )


def identity6() -> Matrix6:
    return tuple(
        tuple(1 if i == j else 0 for j in range(PACKED_DIMENSION))
        for i in range(PACKED_DIMENSION)
    )


class ModularBasis:
    def __init__(self) -> None:
        self.rows: dict[int, list[int]] = {}

    def add(self, matrix: Matrix6) -> bool:
        vector = [entry % MODULUS for row in matrix for entry in row]
        for pivot in sorted(self.rows):
            if vector[pivot]:
                scale = vector[pivot]
                basis_row = self.rows[pivot]
                vector = [
                    (entry - scale * basis_entry) % MODULUS
                    for entry, basis_entry in zip(vector, basis_row, strict=True)
                ]
        pivot = next((index for index, entry in enumerate(vector) if entry), None)
        if pivot is None:
            return False
        inverse = pow(vector[pivot], -1, MODULUS)
        vector = [(entry * inverse) % MODULUS for entry in vector]
        for old_pivot, basis_row in tuple(self.rows.items()):
            if basis_row[pivot]:
                scale = basis_row[pivot]
                self.rows[old_pivot] = [
                    (entry - scale * basis_entry) % MODULUS
                    for entry, basis_entry in zip(basis_row, vector, strict=True)
                ]
        self.rows[pivot] = vector
        return True

    def __len__(self) -> int:
        return len(self.rows)


ZERO3: Matrix3 = ((0, 0, 0), (0, 0, 0), (0, 0, 0))
IDENTITY3: Matrix3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def block(rows: tuple[tuple[Matrix3, Matrix3], tuple[Matrix3, Matrix3]]) -> Matrix6:
    return tuple(
        tuple(
            entry % MODULUS
            for block_matrix in block_row
            for entry in block_matrix[local_row]
        )
        for block_row in rows
        for local_row in range(BLOCK_DIMENSION)
    )


def benchmark_source() -> tuple[tuple[str, Matrix3], ...]:
    beta = 3
    b = "1" + "0" * beta + "1"
    marker = "1" + "0" * beta

    def payload(upper: str, lower: str) -> Matrix3:
        return (
            (1, 0, 0),
            (ternary_code(lower), 3 ** len(lower), 0),
            (ternary_code(upper), 0, 3 ** len(upper)),
        )

    return (
        ("P", ((ternary_code(marker), -1, 3 ** len(marker)), (0, 0, 0), (0, 0, 0))),
        ("Rb", payload(b, "110")),
        ("Rc", payload("1", "1" + b + b + "10")),
        ("Db", payload(b, "0")),
        ("Dc", payload("1", "0")),
    )


def chhn_packing(assignment: tuple[tuple[str, Matrix3], ...]) -> tuple[Matrix6, ...]:
    u, x11, x12, x21, x22 = (matrix for _, matrix in assignment)
    return (
        block(((ZERO3, u), (IDENTITY3, ZERO3))),
        block(((x11, x12), (ZERO3, ZERO3))),
        block(((x21, x22), (ZERO3, ZERO3))),
    )


def algebra_dimension(generators: tuple[Matrix6, ...]) -> int:
    basis = ModularBasis()
    queue = deque([identity6()])
    while queue:
        matrix = queue.popleft()
        if not basis.add(matrix):
            continue
        queue.extend(matrix_mul(matrix, generator) for generator in generators)
    return len(basis)


def main() -> None:
    reachable_det, observable_det = paired_determinants()
    print("paired reachable determinant:", reachable_det)
    print("paired observable determinant:", observable_det)

    dimensions: dict[int, int] = {}
    for assignment in permutations(benchmark_source()):
        dimension = algebra_dimension(chhn_packing(assignment))
        dimensions[dimension] = dimensions.get(dimension, 0) + 1
    assert dimensions == {PACKED_DIMENSION**2: 120}
    print("CHHN benchmark algebra dimensions:", dimensions)


if __name__ == "__main__":
    main()

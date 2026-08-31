#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Verify all six exact M₉(2) consecutive-moment Hankel certificates."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations

# PEP 723 installs SymPy only in the script runtime; standalone ty cannot discover that
# ephemeral environment. The audit explicitly permits this single module-resolution exception.
import sympy as sp  # ty: ignore[unresolved-import]


@dataclass(frozen=True, slots=True)
class Certificate:
    rows: tuple[int, ...]
    columns: tuple[int, ...]
    determinant: sp.Expr


a, b, c = sp.symbols("a b c", nonzero=True)
toggle = sp.Matrix([[1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0]])
separator = sp.Matrix([67, 0, 81, -1]) * sp.Matrix([[1, 0, 0, 0]])
data_b = sp.Matrix([[1, 25, 203, 1], [0, 0, 0, 0], [0, 0, 243, 0], [0, 27, 0, 3]])
data_c = sp.Matrix(
    [
        [1, 1_508_677, 2, 1],
        [0, 0, 0, 0],
        [0, 0, 3, 0],
        [0, 1_594_323, 0, 3],
    ]
)
roles = {"T": toggle, "b": data_b, "c": data_c}

certificates = {
    "Tbc": Certificate(
        (0, 1, 2, 3, 4, 6, 7, 8, 11, 14),
        (1, 2, 3, 4, 5, 7, 8, 9, 10, 11),
        539_434_878_888_077_814_219_552 * a * c**7,
    ),
    "Tcb": Certificate(
        (0, 1, 2, 3, 4, 6, 7, 10, 11, 12),
        (0, 1, 2, 3, 4, 5, 7, 9, 10, 11),
        246_112_452_864 * a * b * c**6,
    ),
    "bTc": Certificate(
        (0, 1, 2, 3, 4, 5, 7, 8, 11, 14),
        (1, 2, 3, 4, 6, 7, 8, 9, 10, 11),
        -4_543_214_987_860_848 * b**2 * c**6,
    ),
    "bcT": Certificate(
        (0, 1, 2, 3, 6, 7, 9, 10, 11, 14),
        (0, 2, 3, 4, 5, 7, 8, 9, 11, 12),
        -531_441 * b * c**5,
    ),
    "cTb": Certificate(
        (0, 1, 2, 3, 4, 5, 6, 10, 11, 15),
        (1, 2, 3, 5, 6, 7, 8, 9, 10, 11),
        -464_904_586_800 * b**2 * c**7,
    ),
    "cbT": Certificate(
        (1, 2, 3, 4, 5, 6, 7, 9, 11, 15),
        (1, 2, 3, 4, 5, 6, 7, 8, 10, 11),
        -5_481 * b**2 * c**6,
    ),
}


def block_hankel(order: str) -> sp.Matrix:
    scales = (a, b, c)
    moments = [scale * roles[name] for scale, name in zip(scales, order, strict=True)]
    moments.extend((separator,) * 4)
    return sp.Matrix.vstack(
        *(
            sp.Matrix.hstack(*(moments[left + right] for right in range(4)))
            for left in range(4)
        )
    )


def main() -> None:
    expected_orders = {"".join(order) for order in permutations("Tbc")}
    assert certificates.keys() == expected_orders
    for order, certificate in certificates.items():
        minor = block_hankel(order).extract(certificate.rows, certificate.columns)
        determinant = sp.factor(minor.det(method="domain-ge"))
        if determinant != certificate.determinant:
            raise ValueError(
                f"{order}: expected {certificate.determinant}, obtained {determinant}"
            )
        print(f"{order}: det = {determinant}")


if __name__ == "__main__":
    main()

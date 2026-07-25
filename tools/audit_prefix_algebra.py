#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Verify the exact determinant certificate for the ten-state prefix pair."""

from __future__ import annotations

from functools import reduce
from operator import matmul

# PEP 723 installs SymPy only in the script runtime; standalone ty cannot discover that
# ephemeral environment. The audit explicitly permits this single module-resolution exception.
import sympy as sp  # ty: ignore[unresolved-import]


ρ, x, κ = sp.symbols("rho x kappa", positive=True)
m = (5 * ρ - 1) / 2


def column(*terms: tuple[int, sp.Expr | int]) -> sp.Matrix:
    result = sp.zeros(10, 1)
    for index, coefficient in terms:
        result[index] = coefficient
    return result


def matrix(columns: dict[int, sp.Matrix]) -> sp.Matrix:
    result = sp.zeros(10)
    for index, value in columns.items():
        result[:, index] = value
    return result


B0 = matrix(
    {
        0: column((0, m), (6, 1), (7, 25 + x), (8, 2), (9, 1)),
        1: column((0, -1), (7, κ), (9, 3)),
        2: column((0, 3 * ρ), (8, 3)),
        6: column((3, 1)),
        7: column((4, 1)),
        8: column((5, 1)),
    }
)
B1 = matrix(
    {
        0: column((6, 1), (7, 25), (8, (15 * ρ + 1) / 2), (9, 1)),
        1: column((7, 27), (9, 3)),
        2: column((8, 9 * ρ)),
        3: column((0, 1)),
        4: column((1, 1)),
        5: column((2, 1)),
        6: column((3, 1)),
        8: column((5, 1)),
        9: column((4, 1)),
    }
)

u = column(
    (0, m**2),
    (3, 1),
    (4, 25 + x),
    (5, 2),
    (6, m),
    (7, m * (25 + x)),
    (8, 2 * m),
    (9, m),
)
v = sp.Matrix([[m, -1, 3 * ρ, 0, 0, 0, 0, 0, 0, 0]])

assert sp.simplify(B0**3 - u * v) == sp.zeros(10)

reachable = sp.Matrix.hstack(*(B1**j * u for j in range(10)))
reachable_det = sp.factor(reachable.det())

prefixes = ("", "1", "10", "11", "101", "110", "1011", "1101", "10110", "11010")


def product(word: str) -> sp.Matrix:
    return reduce(matmul, (B1 if bit == "1" else B0 for bit in word), sp.eye(10))


observable = sp.Matrix.vstack(*(v * product(prefix) for prefix in prefixes))
observable_det = sp.factor(observable.det())

P = (
    158203125 * ρ**11
    - 158203125 * ρ**10
    + 59062500 * ρ**9
    - 8812500 * ρ**8
    - 39071250 * ρ**7
    + 30457250 * ρ**6
    - 9526500 * ρ**5
    + 4428948 * ρ**4
    - 664283 * ρ**3
    + 40587 * ρ**2
    - 1032 * ρ
    + 8
)
Q = (
    46875 * ρ**6
    - 56250 * ρ**5
    + 28125 * ρ**4
    - 18000 * ρ**3 * x
    - 457500 * ρ**3
    + 10800 * ρ**2 * x
    + 271125 * ρ**2
    - 2160 * ρ * x
    - 54090 * ρ
    + 512 * x**3
    + 39168 * x**2
    + 998928 * x
    + 8493267
)
claimed_reachable_det = (
    sp.Rational(3**10, 2**22)
    * ρ
    * x
    * (3 * ρ - 1) ** 3
    * (5 * ρ - 3) ** 2
    * (5 * ρ - 1)
    * (25 * ρ**2 + 3) ** 2
    * P
    * Q
)
claimed_observable_det = 3**9 * ρ**6 * (ρ - 3) ** 3

assert sp.factor(reachable_det - claimed_reachable_det) == 0
assert sp.factor(observable_det - claimed_observable_det) == 0
assert κ not in observable_det.free_symbols

print("B0^3 = u v^T: yes")
print("det(R) factorization: yes")
print("det(O) =", observable_det)
print("body lower scale cancels from det(O): yes")

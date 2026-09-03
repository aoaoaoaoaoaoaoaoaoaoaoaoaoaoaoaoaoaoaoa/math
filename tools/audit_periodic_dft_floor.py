#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Certify Fourier-support rank floors for the two periodic-return screens."""

from __future__ import annotations

from functools import cache
from itertools import product

# PEP 723 installs SymPy only in the script runtime; standalone ty cannot discover that
# ephemeral environment. The audit explicitly permits this single module-resolution exception.
import sympy as sp  # ty: ignore[unresolved-import]

z = sp.symbols("z")


def divisors(period: int) -> tuple[int, ...]:
    return tuple(divisor for divisor in range(1, period + 1) if period % divisor == 0)


@cache
def evaluation_rows(period: int, support: tuple[int, ...], order: int) -> sp.Matrix:
    coefficients = sp.symbols(f"x0:{len(support)}")
    polynomial = sum(
        coefficient * z**slot for coefficient, slot in zip(coefficients, support)
    )
    cyclotomic = sp.cyclotomic_poly(order, z)
    remainder = sp.Poly(sp.rem(polynomial, cyclotomic, z), z)
    return sp.Matrix(
        [
            [
                sp.expand(remainder.coeff_monomial(z**degree)).coeff(coefficient)
                for coefficient in coefficients
            ]
            for degree in range(sp.degree(cyclotomic, z))
        ]
    )


@cache
def exact_zero_masks(period: int, support: tuple[int, ...]) -> tuple[int, ...]:
    orders = divisors(period)
    width = len(support)
    rows = {order: evaluation_rows(period, support, order) for order in orders}
    masks: list[int] = []
    for mask in range(1 << len(orders)):
        constraints = [
            rows[order] for index, order in enumerate(orders) if mask >> index & 1
        ]
        matrix = sp.Matrix.vstack(*constraints) if constraints else sp.zeros(0, width)
        rank = matrix.rank()
        if rank == width:
            continue
        # Over infinite Q, a common all-nonzero kernel vector exists exactly when the kernel is
        # not contained in any coordinate hyperplane. The same finite-union argument enforces
        # every orbit declared nonzero.
        if any(
            matrix.col_join(sp.eye(width)[slot, :]).rank() == rank
            for slot in range(width)
        ):
            continue
        if any(
            not (mask >> index & 1)
            and sp.Matrix.vstack(matrix, rows[order]).rank() == rank
            for index, order in enumerate(orders)
        ):
            continue
        masks.append(mask)
    return tuple(masks)


def floor(family: str, period: int) -> int:
    role_count = 4 if family == "paired" else 5
    orders = divisors(period)
    weights = tuple(int(sp.totient(order)) for order in orders)
    best = 10**9
    for assignment in product(range(role_count), repeat=period):
        if assignment[0] != 0 or len(set(assignment)) != role_count:
            continue
        supports = tuple(
            tuple(slot for slot, role in enumerate(assignment) if role == target)
            for target in range(role_count)
        )
        for masks in product(
            *(exact_zero_masks(period, support) for support in supports)
        ):
            total = 0
            for index, weight in enumerate(weights):
                nonzero = tuple(not (mask >> index & 1) for mask in masks)
                if family == "paired":
                    toggle, data_b, data_c, separator = nonzero
                    ordinary = toggle or data_b or data_c
                    rank = (
                        0
                        if not any(nonzero)
                        else 1
                        if separator and not ordinary
                        else 3
                        if toggle and separator
                        else 2
                    )
                else:
                    *ordinary_roles, terminal = nonzero
                    rank = (
                        0
                        if not any(nonzero)
                        else 2
                        if terminal and any(ordinary_roles)
                        else 1
                    )
                total += weight * rank
            best = min(best, total)
    return best


def audit_rank_strata() -> None:
    t, b, c, p, q = sp.symbols("t b c p q")
    toggle = sp.Matrix([[1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0]])
    data_b = sp.Matrix([[1, 25, 203, 1], [0, 0, 0, 0], [0, 0, 243, 0], [0, 27, 0, 3]])
    data_c = sp.Matrix(
        [[1, 1_508_677, 2, 1], [0, 0, 0, 0], [0, 0, 3, 0], [0, 1_594_323, 0, 3]]
    )
    separator = sp.Matrix([67, 0, 81, -1]) * sp.Matrix([[1, q, q, q]])
    matrix = t * toggle + b * data_b + c * data_c + p * separator
    assert sp.factor(matrix.extract([1, 2, 3], [0, 1, 3]).det()) == 81 * p * t * (
        27 * b + 1_594_323 * c + t
    )
    assert sp.factor(matrix.extract([1, 2, 3], [0, 2, 3]).det()) == p * t * (
        243 * b + 3 * c + t
    )
    ordinary_forms = sp.Matrix(
        [[25, 1_508_677, 1, 1], [203, 2, 203, 2], [9, 531_441, 1, 1], [81, 1, 81, 1]]
    )
    assert ordinary_forms.det() == -28_091_232


audit_rank_strata()
paired = tuple(floor("paired", period) for period in range(4, 9))
neary = tuple(floor("neary", period) for period in range(5, 9))
assert paired == (12, 14, 12, 19, 12)
assert neary == (10, 9, 13, 10)
print("paired m=4..8:", *paired)
print("M3(5) m=5..8:", *neary)

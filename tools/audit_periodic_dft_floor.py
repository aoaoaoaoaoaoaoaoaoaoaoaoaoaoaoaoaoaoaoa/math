#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Certify Fourier-support rank floors for periodic return and radix screens."""

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


def radix_code(
    bits: tuple[bool, ...], radix: sp.Symbol, zero: sp.Symbol, one: sp.Symbol
) -> sp.Expr:
    """Evaluate a bit word with symbolic radix and digits."""
    return sp.expand(
        sum(
            (one if bit else zero) * radix ** (len(bits) - slot - 1)
            for slot, bit in enumerate(bits)
        )
    )


def audit_radix_rank_strata() -> None:
    """Check the uniform minors used for every injective radix-digit code."""
    a, d0, d1, q = sp.symbols("a d0 d1 q")
    t, b, c, p = sp.symbols("t b c p")
    upper_b_bits = (True, False, False, False, True)
    lower_b_bits = (True, True, False)
    lower_c_bits = (True,) + 2 * upper_b_bits + (True, False)
    marker_bits = (True, False, False, False)
    upper_b = radix_code(upper_b_bits, a, d0, d1)
    lower_b = radix_code(lower_b_bits, a, d0, d1)
    lower_c = radix_code(lower_c_bits, a, d0, d1)
    marker = radix_code(marker_bits, a, d0, d1)

    toggle = sp.Matrix([[1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0]])
    data_b = sp.Matrix(
        [[1, lower_b, upper_b, d0], [0, 0, 0, 0], [0, 0, a**5, 0], [0, a**3, 0, a]]
    )
    data_c = sp.Matrix(
        [[1, lower_c, d1, d0], [0, 0, 0, 0], [0, 0, a, 0], [0, a**13, 0, a]]
    )
    separator = sp.Matrix([marker, 0, a**4, -1]) * sp.Matrix([[1, q, q, q]])
    matrix = t * toggle + b * data_b + c * data_c + p * separator

    left_form = a**13 * c + a**3 * b + t
    right_form = a**5 * b + a * c + t
    assert sp.factor(matrix.extract([1, 2, 3], [0, 1, 3]).det()) == (
        a**4 * p * t * left_form
    )
    assert sp.factor(matrix.extract([1, 2, 3], [0, 2, 3]).det()) == (p * t * right_form)
    solution = sp.solve([left_form, right_form], [b, c], dict=True)[0]
    first_denominator = a**6 - a**5 + a**4 - a**3 + a**2 - a + 1
    second_denominator = sum(a**power for power in range(7))
    positive_factor = (
        a**13 + a**11 - a**10 + 2 * a**9 + a**7 - a**6 + a**5 + 2 * a**3 - a**2 + a - 1
    )
    constrained_tail = sp.factor(
        matrix.extract([0, 1, 2], [1, 2, 3]).det().subs(solution)
    )
    assert (
        sp.factor(
            constrained_tail * first_denominator * second_denominator
            + a * p * q * t**2 * (d0 - d1) * positive_factor
        )
        == 0
    )
    # These decompositions make every remaining radix factor positive at integer a >= 2.
    assert (
        sp.expand(
            a**10 * (a**3 - 1)
            + a**11
            + 2 * a**9
            + a**6 * (a - 1)
            + a**5
            + a**2 * (2 * a - 1)
            + (a - 1)
        )
        == positive_factor
    )
    assert sp.expand(a**5 * (a - 1) + a**3 * (a - 1) + a * (a - 1) + 1) == (
        first_denominator
    )

    # The remaining paired rank-two strata need only these elementary certificates.
    no_separator_system = sp.Matrix([[1, a**5, a], [1, a**3, a**13], [1, 1, 1]])
    positive_system_factor = sum(
        coefficient * a**power
        for power, coefficient in enumerate(
            (1, 1, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 2, 1, 1)
        )
    )
    assert sp.factor(no_separator_system.det()) == (
        a * (a - 1) ** 2 * (a + 1) * positive_system_factor
    )
    data_separator = b * data_b + c * data_c + p * separator
    assert sp.factor(data_separator.extract([2, 3], [0, 2]).det()) == (
        a * p * (a**4 * b + c)
    )
    assert sp.factor(data_separator.extract([2, 3], [0, 3]).det()) == (
        a**5 * p * (b + c)
    )

    rule_b, rule_c, erase_b, erase_c, terminal = sp.symbols(
        "rule_b rule_c erase_b erase_c terminal"
    )
    ordinary_forms = sp.Matrix(
        [
            [lower_b, lower_c, d0, d0],
            [upper_b, d1, upper_b, d1],
            [a**3, a**13, a, a],
            [a**5, a, a**5, a],
        ]
    )
    empty_collision_code = radix_code((False, False, False, True), a, d0, d1)
    assert sp.factor(ordinary_forms.det()) == (
        a**5
        * (a - 1)
        * (a + 1) ** 2
        * (d0 - d1)
        * (a**2 + a + 1)
        * empty_collision_code
        * (a**4 - a**3 + a**2 - a + 1)
    )
    ordinary = ordinary_forms * sp.Matrix([rule_b, rule_c, erase_b, erase_c])
    neary = sp.Matrix(
        [
            [
                rule_b + rule_c + erase_b + erase_c + marker * terminal,
                ordinary[0],
                ordinary[1],
            ],
            [-terminal, ordinary[2], 0],
            [a**4 * terminal, 0, ordinary[3]],
        ]
    )
    assert sp.expand(neary.extract([0, 1], [0, 2]).det() - terminal * ordinary[1]) == 0
    assert (
        sp.expand(neary.extract([0, 2], [0, 1]).det() + a**4 * terminal * ordinary[0])
        == 0
    )
    assert (
        sp.expand(neary.extract([1, 2], [0, 1]).det() + a**4 * terminal * ordinary[2])
        == 0
    )
    assert sp.expand(neary.extract([1, 2], [0, 2]).det() + terminal * ordinary[3]) == 0


audit_rank_strata()
audit_radix_rank_strata()
paired = tuple(floor("paired", period) for period in range(4, 9))
neary = tuple(floor("neary", period) for period in range(5, 9))
assert paired == (12, 14, 12, 19, 12)
assert neary == (10, 9, 13, 10)
print("paired m=4..8:", *paired)
print("M3(5) m=5..8:", *neary)
print("radix paired m=4..8:", *paired)
print("radix M3(5) m=5..8:", *neary)

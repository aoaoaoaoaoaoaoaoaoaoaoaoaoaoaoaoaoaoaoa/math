#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Reconstruct the asymmetric eight-state chart, independently of the discovery emitter.

The rational identities are uniform on the regular parameter locus. Raw-word enumeration
is a bounded semantic cross-check, not the proof of the unrestricted-word converse.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

# PEP 723 owns SymPy's runtime environment. Standalone ty cannot resolve that environment;
# the bounded audit permits this module-resolution exception, as for the nine-state checker.
import sympy as sp  # ty: ignore[unresolved-import]


def zero(matrix: sp.Matrix) -> None:
    assert all(sp.cancel(entry) == 0 for entry in matrix)


@dataclass(frozen=True)
class Chart:
    transition: sp.Matrix
    input: sp.Matrix
    output: sp.Matrix
    roles: tuple[sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix]
    hankel: sp.Matrix


def realize(rho: sp.Expr, q: sp.Expr, scale: sp.Expr) -> Chart:
    """Use two length-three chains, one static state, and one geometric state."""
    code = (scale + 48 - q * (scale - 27)) / 3
    toggle = sp.Matrix([[1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0]])
    data_b = sp.Matrix(
        [
            [1, 25, (15 * rho + 1) / 2, 1],
            [0, 0, 0, 0],
            [0, 0, 9 * rho, 0],
            [0, 27, 0, 3],
        ]
    )
    data_c = sp.Matrix([[1, code, 2, 1], [0, 0, 0, 0], [0, 0, 3, 0], [0, scale, 0, 3]])
    column = sp.Matrix([(5 * rho - 1) / 2, 0, 3 * rho, -1])
    row = sp.Matrix([[1, 16 + 9 * q, q, q]])
    t = 2 * q + 1
    h = 6 / (t * (3 * rho - 1))
    xi = 3 * rho + 1 + rho * h
    delta = scale * ((t - 2) * rho - t) + 26 * t + 72
    gamma = scale * (t * (27 * rho**3 - 1) + 18 * rho**2 + 6 * rho) / delta
    separator = h * column * row
    f0 = gamma * toggle - xi**2 * separator
    f1 = data_b - xi * separator
    f2 = data_c - separator

    kappa = sp.Matrix([scale - 3 * code, 3, 0, -scale])
    z = sp.Matrix([(3 * rho - 1) / 6, 0, rho, -sp.Rational(1, 3)])
    ell = sp.Matrix([[1, 0, (q - 2) / 3, (q - 1) / 3]])
    reader = sp.Matrix(
        [
            [
                1 - xi,
                0,
                ((15 * rho + 1) / 2 - 2 + (3 * rho - xi) * (q - 2)) / 3,
                (1 - xi) * (q - 1) / 3,
            ]
        ]
    )
    omega = kappa - 3 * scale * z
    for identity in (
        data_c * kappa,
        row * kappa,
        data_c * z - column,
        ell * data_c - row,
        h * row * z - sp.ones(1),
        ell * data_b * kappa,
        ell * data_b * z - xi * row * z,
        f2 * kappa,
        f2 * z,
        ell * f2,
        reader * column,
        reader * f2 - ell * f1,
        (f0 * omega)[1:2, :],
        (ell * f0 - reader * f1) * omega,
        (f0 * kappa)[1:2, :] + sp.ones(1) * gamma * scale,
    ):
        zero(identity)

    # The explicit factorization removes rank tests and basis selection from the emitter.
    section = sp.eye(4)[:, [0, 2]]
    inverse = sp.Matrix(
        [[0, 0, -q / 3, (3 * rho - t) / 6], [0, 0, sp.Rational(1, 3), rho]]
    )
    q2 = sp.Matrix(
        [
            [1, 16 + 9 * q + scale * (3 * rho - t) / 6, 0, (3 * rho - 1) / 2],
            [0, rho * scale, 1, 3 * rho],
        ]
    )
    l0, l1, l2 = (f * section for f in (f0, f1, f2))
    q1 = (inverse * (f1 - l1 * q2)).applyfunc(sp.cancel)
    residual = (f0 - l0 * q2 - l1 * q1).applyfunc(sp.cancel)
    static_column = (-3 / gamma * residual * z).applyfunc(sp.cancel)
    static_row = sp.Matrix([[0, 0, 0, gamma]])
    q0 = (inverse * (residual - static_column * static_row)).applyfunc(sp.cancel)
    zero(inverse * l2 - sp.eye(2))
    zero(l2 * q2 - f2)
    zero(l1 * q2 + l2 * q1 - f1)
    zero(l0 * q2 + l1 * q1 + l2 * q0 + static_column * static_row - f0)

    transition = sp.zeros(8)
    for index in range(4):
        transition[index + 2, index] = 1
    transition[7, 7] = 1 / xi
    input_matrix = sp.Matrix.vstack(q2, q1, q0, static_row, xi**2 * h * row)
    output = sp.Matrix.hstack(l0, l1, l2, static_column, column)
    roles = (gamma * toggle, data_b, data_c, separator)
    for wait in range(4):
        expected = roles[wait] if wait < 3 else separator / xi
        zero(output * transition**wait * input_matrix - expected)
    zero(transition**4 - transition**3 / xi)
    # The recurrence proves every later moment, not merely the four checked values.
    hankel = sp.BlockMatrix(
        [[f0, f1, f2], [f1, f2, sp.zeros(4)], [f2, sp.zeros(4), sp.zeros(4)]]
    ).as_explicit()
    return Chart(transition, input_matrix, output, roles, hankel)


def ternary_code(word: str) -> int:
    code = 0
    for bit in word:
        code = 3 * code + int(bit) + 1
    return code


def tag_encode(width: int, body: str) -> str:
    assert width >= 3 and body.startswith("bcb") and set(body) <= {"b", "c"}
    return "".join("1" + "0" * width + "1" if letter == "b" else "1" for letter in body)


def source_chart(width: int, body: str) -> Chart:
    word = tag_encode(width, body)
    q = -1 - sp.Rational(ternary_code(word), 3 ** len(word) - 1)
    scale = sp.Integer(3) ** (len(word) + 3)
    assert (scale + 48 - q * (scale - 27)) / 3 == ternary_code("1" + word + "10")
    assert -2 < q < -sp.Rational(3, 2)
    assert -1 < 16 + 9 * q < -sp.Rational(1, 2)
    return realize(sp.Integer(3) ** width, q, scale)


def integerize(matrix: sp.Matrix) -> sp.Matrix:
    return matrix * sp.ilcm(*(entry.q for entry in matrix))


def raw_word_check(width: int, body: str, depth: int) -> int:
    word = tag_encode(width, body)
    rho = 3**width
    scale = 3 ** (len(word) + 3)
    lower_code = ternary_code("1" + word + "10")
    denominator = 3 ** len(word) - 1
    numerator = -denominator - ternary_code(word)
    stack = [(0, ((5 * rho - 1) // 2, 0, 3 * rho, -1))]
    count = 0
    while stack:
        length, (v0, v1, v2, v3) = stack.pop()
        coefficient = (
            denominator * v0
            + (16 * denominator + 9 * numerator) * v1
            + numerator * (v2 + v3)
        )
        assert (coefficient == 0) == (v0 == 0 and v1 == 0)
        count += 1
        if length < depth:
            stack.extend(
                [
                    (length + 1, (v0, v3, v2, v1)),
                    (
                        length + 1,
                        (
                            v0 + 25 * v1 + (15 * rho + 1) // 2 * v2 + v3,
                            0,
                            9 * rho * v2,
                            27 * v1 + 3 * v3,
                        ),
                    ),
                    (
                        length + 1,
                        (
                            v0 + lower_code * v1 + 2 * v2 + v3,
                            0,
                            3 * v2,
                            scale * v1 + 3 * v3,
                        ),
                    ),
                ]
            )
    return count


def main() -> None:
    realize(*sp.symbols("rho q K"))
    print(
        "Uniform Schur identities, explicit chart, four moments, and tail recurrence: passed"
    )
    benchmark = source_chart(3, "bcbc")
    transition = integerize(benchmark.transition)
    cut = integerize(benchmark.input * benchmark.output)
    witness = "CAAACAACCACAACACCAACACAAAC"
    value = sp.eye(8)
    for letter in witness:
        value *= transition if letter == "A" else cut
    assert value == sp.zeros(8)
    assert (benchmark.hankel.rank(), transition.rank(), cut.rank()) == (7, 5, 4)
    print("Integer eight-state witness and ranks 7/5/4: passed")
    for width, suffix in product((3, 4, 10), ("", "b", "cc", "bcbb")):
        chart = source_chart(width, "bcb" + suffix)
        assert chart.hankel.rank() == 7
    print("Twelve additional exact source charts: passed")
    counts = [raw_word_check(3, body, 11) for body in ("bcb", "bcbc", "bcbb")]
    assert counts == [265720] * 3
    print(
        f"Bounded phase check: {sum(counts)} raw products, lengths zero through eleven"
    )


if __name__ == "__main__":
    main()

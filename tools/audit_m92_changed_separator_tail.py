#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Verify the symbolic rank-nine changed-separator transfer construction."""

from __future__ import annotations

# PEP 723 installs SymPy only in the script runtime; standalone ty cannot discover that
# ephemeral environment. The audit explicitly permits this single module-resolution exception.
import sympy as sp  # ty: ignore[unresolved-import]


r, lower_code, lower_scale = sp.symbols("r V K", nonzero=True)


def zero_matrix(rows: int, columns: int) -> sp.Matrix:
    return sp.zeros(rows, columns)


def entrywise_zero(matrix: sp.Matrix) -> bool:
    return all(sp.cancel(entry) == 0 for entry in matrix)


def construction_parameters() -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    denominator = (
        9 * lower_scale**2 * r**2
        + 2 * lower_scale**2 * r
        - lower_scale**2
        - 18 * lower_scale * lower_code * r**2
        + 2 * lower_scale * lower_code
        - 9 * lower_scale * r**2
        - 6 * lower_scale * r
        - 47 * lower_scale
        + 48 * lower_code
        + 96
    )
    affine_weight = 2 * lower_scale * (lower_scale - 3) / denominator
    tail_weight = 2 * lower_scale * (lower_scale - 3 * lower_code) / denominator
    tail_eigenvalue = (
        lower_scale * (3 * r - 1) * (lower_scale - 2 * lower_code - 1) / denominator
    )
    ratio = (lower_scale - 3 * lower_code) / (lower_scale - 3)
    return denominator, affine_weight, tail_weight, tail_eigenvalue, ratio


def benchmark_roles() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix]:
    denominator, affine_weight, tail_weight, tail_eigenvalue, _ = (
        construction_parameters()
    )
    del denominator
    marker = (5 * r - 1) / 2
    upper_b = (15 * r + 1) / 2
    toggle = sp.Matrix([[1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0]])
    data_b = sp.Matrix(
        [
            [1, 25, upper_b, 1],
            [0, 0, 0, 0],
            [0, 0, 9 * r, 0],
            [0, 27, 0, 3],
        ]
    )
    data_c = sp.Matrix(
        [
            [1, lower_code, 2, 1],
            [0, 0, 0, 0],
            [0, 0, 3, 0],
            [0, lower_scale, 0, 3],
        ]
    )
    column = sp.Matrix([marker, 0, 3 * r, -1])
    row = sp.Matrix([[affine_weight, tail_weight, tail_weight, tail_weight]])
    assert sp.cancel(row[0, 1] / row[0, 0] - construction_parameters()[4]) == 0
    assert tail_eigenvalue != 0
    return toggle, data_b, data_c, column, row


def nilpotent_chain_realization() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    toggle, data_b, data_c, column, row = benchmark_roles()
    _, _, _, tail_eigenvalue, _ = construction_parameters()
    residual = (
        sp.simplify(toggle - column * row / tail_eigenvalue**3),
        sp.simplify(data_b - column * row / tail_eigenvalue**2),
        sp.simplify(data_c - column * row / tail_eigenvalue),
    )
    residual_zero, residual_one, residual_two = residual

    last_columns = residual_two[:, [0, 1]]
    last_pivot = last_columns.extract([0, 3], [0, 1])
    expected_last_pivot = (
        -2
        * lower_scale
        * r
        * (lower_scale + 3 * lower_code - 6)
        / ((3 * r - 1) * (lower_scale - 2 * lower_code - 1))
    )
    assert sp.cancel(last_pivot.det() - expected_last_pivot) == 0
    first_rows = sp.simplify(
        last_pivot.inv() * residual_two.extract([0, 3], [0, 1, 2, 3])
    )
    assert entrywise_zero(last_columns * first_rows - residual_two)

    middle_columns = residual_one[:, [0, 1]]
    first_remainder = sp.simplify(residual_one - middle_columns * first_rows)
    middle_rows = sp.simplify(
        last_pivot.inv() * first_remainder.extract([0, 3], [0, 1, 2, 3])
    )
    rank_one_remainder = sp.simplify(first_remainder - last_columns * middle_rows)
    expected_remainder_entry = (
        216
        * (lower_scale - lower_code - 2)
        / (lower_scale * (lower_scale + 3 * lower_code - 6))
    )
    expected_remainder = zero_matrix(4, 4)
    expected_remainder[2, 3] = expected_remainder_entry
    assert entrywise_zero(rank_one_remainder - expected_remainder)

    singleton_column = sp.Matrix([0, 0, 1, 0])
    singleton_row = sp.Matrix([list(rank_one_remainder.row(2))])
    initial_rows = sp.Matrix.vstack(first_rows, singleton_row)
    final_columns = sp.Matrix.hstack(last_columns, singleton_column)
    row_pivot_columns = [0, 1, 3]
    column_pivot_rows = [0, 2, 3]
    assert (
        sp.cancel(initial_rows[:, row_pivot_columns].det() - expected_remainder_entry)
        == 0
    )
    expected_column_pivot = (
        2
        * lower_scale
        * r
        * (lower_scale + 3 * lower_code - 6)
        / ((3 * r - 1) * (lower_scale - 2 * lower_code - 1))
    )
    assert (
        sp.cancel(final_columns[column_pivot_rows, :].det() - expected_column_pivot)
        == 0
    )

    zero_remainder = sp.simplify(residual_zero - middle_columns * middle_rows)
    initial_columns = sp.simplify(
        zero_remainder[:, row_pivot_columns] * initial_rows[:, row_pivot_columns].inv()
    )
    last_remainder = sp.simplify(zero_remainder - initial_columns * initial_rows)
    final_rows = sp.simplify(
        final_columns[column_pivot_rows, :].inv() * last_remainder[column_pivot_rows, :]
    )
    assert entrywise_zero(last_remainder - final_columns * final_rows)

    transition = zero_matrix(9, 9)
    for start, length in ((0, 3), (3, 3), (6, 2)):
        for offset in range(length - 1):
            transition[start + offset + 1, start + offset] = 1
    transition[8, 8] = tail_eigenvalue

    input_matrix = zero_matrix(9, 4)
    output_matrix = zero_matrix(4, 9)
    for chain, start in enumerate((0, 3)):
        input_matrix[start, :] = first_rows[chain, :]
        input_matrix[start + 1, :] = middle_rows[chain, :]
        input_matrix[start + 2, :] = final_rows[chain, :]
        output_matrix[:, start] = initial_columns[:, chain]
        output_matrix[:, start + 1] = middle_columns[:, chain]
        output_matrix[:, start + 2] = last_columns[:, chain]
    input_matrix[6, :] = singleton_row
    input_matrix[7, :] = final_rows[2, :]
    output_matrix[:, 6] = initial_columns[:, 2]
    output_matrix[:, 7] = singleton_column
    input_matrix[8, :] = row / tail_eigenvalue**3
    output_matrix[:, 8] = column
    return transition, input_matrix, output_matrix


def verify_exact_benchmark(
    transition: sp.Matrix, input_matrix: sp.Matrix, output_matrix: sp.Matrix
) -> None:
    substitution = {r: 27, lower_code: 1_508_677, lower_scale: 1_594_323}
    transition = transition.subs(substitution)
    input_matrix = input_matrix.subs(substitution)
    output_matrix = output_matrix.subs(substitution)
    assert transition.rank() == 6
    assert (transition**2).rank() == 3
    assert (transition**3).rank() == 1
    assert input_matrix.rank() == 4
    assert output_matrix.rank() == 4

    _, _, _, tail_eigenvalue, ratio = construction_parameters()
    expected_ratio = sp.Rational(-18_793, 10_220)
    expected_eigenvalue = sp.Rational(5_386_449_780, 437_615_386_817)
    assert sp.factor(ratio.subs(substitution)) == expected_ratio
    assert sp.factor(tail_eigenvalue.subs(substitution)) == expected_eigenvalue

    moments = [
        output_matrix * transition**exponent * input_matrix for exponent in range(7)
    ]
    hankel = sp.Matrix.vstack(
        *(
            sp.Matrix.hstack(*(moments[left + right] for right in range(4)))
            for left in range(4)
        )
    )
    assert hankel.rank() == 9
    print(f"benchmark ratio = {expected_ratio}")
    print(f"benchmark tail eigenvalue = {expected_eigenvalue}")
    print("benchmark transfer Hankel rank = 9")


def main() -> None:
    transition, input_matrix, output_matrix = nilpotent_chain_realization()
    print("symbolic 3+3+2+1 chain realization verified")
    verify_exact_benchmark(transition, input_matrix, output_matrix)


if __name__ == "__main__":
    main()

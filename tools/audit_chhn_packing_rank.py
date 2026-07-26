#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["sympy==1.14.0"]
# ///

"""Reconstruct every finite Hankel certificate in the literal CHHN packing."""

from __future__ import annotations

from itertools import permutations

# PEP 723 installs SymPy only in the script runtime; standalone ty cannot discover that
# ephemeral environment. The audit explicitly permits this single module-resolution exception.
import sympy as sp  # ty: ignore[unresolved-import]


t, z, rho = sp.symbols("t z rho")
marker_value = (5 * t - 3) / 6
upper_b_value = (5 * t + 1) / 2


def payload(
    upper_value: sp.Expr | int,
    lower_value: sp.Expr | int,
    upper_scale: sp.Expr | int,
    lower_scale: sp.Expr | int,
) -> sp.Matrix:
    return sp.Matrix(
        [
            [1, lower_value, upper_value],
            [0, lower_scale, 0],
            [0, 0, upper_scale],
        ]
    )


row3 = sp.Matrix([[1, 0, 0]])
column3 = sp.Matrix([marker_value, -1, t])
separator = column3 * row3
roles = {
    "Rc": payload(2, rho, 3, z),
    "Rb": payload(upper_b_value, 25, 3 * t, 27),
    "Dc": payload(2, 1, 3, 3),
    "Db": payload(upper_b_value, 1, 3 * t, 3),
}

zero3 = sp.zeros(3)
identity3 = sp.eye(3)
empty: tuple[int, ...] = ()
shift, left, right = range(3)


def pack(source: tuple[sp.Matrix, ...]) -> tuple[sp.Matrix, ...]:
    root, left_leading, left_trailing, right_leading, right_trailing = source
    return (
        sp.BlockMatrix([[zero3, root], [identity3, zero3]]).as_explicit(),
        sp.BlockMatrix([[left_leading, left_trailing], [zero3, zero3]]).as_explicit(),
        sp.BlockMatrix([[right_leading, right_trailing], [zero3, zero3]]).as_explicit(),
    )


def product(generators: tuple[sp.Matrix, ...], word: tuple[int, ...]) -> sp.Matrix:
    result = sp.eye(6)
    for letter in word:
        result *= generators[letter]
    return result


row6 = sp.Matrix([[1, 0, 0, 0, 0, 0]])
column6 = sp.Matrix.vstack(column3, sp.zeros(3, 1))


def observable(
    generators: tuple[sp.Matrix, ...], words: tuple[tuple[int, ...], ...]
) -> sp.Matrix:
    return sp.Matrix.vstack(*(row6 * product(generators, word) for word in words))


def reachable(
    generators: tuple[sp.Matrix, ...], words: tuple[tuple[int, ...], ...]
) -> sp.Matrix:
    return sp.Matrix.hstack(*(product(generators, word) * column6 for word in words))


def pair_row_det(first: sp.Matrix, second: sp.Matrix) -> sp.Expr:
    return sp.factor(sp.Matrix.vstack(row3, row3 * first, row3 * second).det())


def triple_row_det(first: sp.Matrix, second: sp.Matrix, third: sp.Matrix) -> sp.Expr:
    return sp.factor(sp.Matrix.vstack(row3 * first, row3 * second, row3 * third).det())


def composite_row_det(root: sp.Matrix, leading: sp.Matrix) -> sp.Expr:
    return sp.factor(sp.Matrix.vstack(row3, row3 * root, row3 * leading * root).det())


def column_det(first: sp.Matrix, second: sp.Matrix) -> sp.Expr:
    return sp.factor(sp.Matrix.hstack(column3, first * column3, second * column3).det())


def payload_word(slot: int) -> tuple[int, ...]:
    control = left if slot <= 2 else right
    return (control,) if slot % 2 == 1 else (control, shift)


def audit_placement(placement: tuple[str, ...]) -> None:
    source_by_name = {"P": separator, **roles}
    source = tuple(source_by_name[name] for name in placement)
    generators = pack(source)
    separator_slot = placement.index("P")

    if separator_slot == 0:
        prefixes = (empty, (shift,), (left,), (right,), (left, shift), (right, shift))
        expected_observable = marker_value * pair_row_det(source[2], source[4]) ** 2
    elif separator_slot in (1, 3):
        same_control = left if separator_slot == 1 else right
        other_control = right if separator_slot == 1 else left
        same_trailing = 2 if separator_slot == 1 else 4
        other_trailing = 4 if separator_slot == 1 else 2
        prefixes = (
            empty,
            (shift,),
            (same_control,),
            (other_control,),
            (shift, shift),
            (same_control, shift),
        )
        expected_observable = pair_row_det(
            source[0], source[same_trailing]
        ) * triple_row_det(source[0], source[same_trailing], source[other_trailing])
    else:
        control = left if separator_slot == 2 else right
        leading = 1 if separator_slot == 2 else 3
        prefixes = (
            empty,
            (shift,),
            (shift, shift),
            (control,),
            (control, shift),
            (control, shift, shift),
        )
        expected_observable = (
            marker_value * composite_row_det(source[0], source[leading]) ** 2
        )

    actual_observable = sp.factor(observable(generators, prefixes).det())
    assert sp.factor(actual_observable / expected_observable) in (1, -1)

    easy_names = ("Rb", "Db") if placement[0] in ("Rc", "Dc") else ("Rc", "Dc")
    first_slot, second_slot = (placement.index(name) for name in easy_names)
    first_word, second_word = payload_word(first_slot), payload_word(second_slot)
    suffixes = (
        empty,
        (shift,),
        first_word,
        second_word,
        (shift,) + first_word,
        (shift,) + second_word,
    )
    expected_reachable = column_det(source[first_slot], source[second_slot]) ** 2
    actual_reachable = sp.factor(reachable(generators, suffixes).det())
    assert sp.factor(actual_reachable / expected_reachable) in (1, -1)


def main() -> None:
    placements = tuple(permutations(("P", *roles)))
    for placement in placements:
        audit_placement(placement)
    print(f"verified {len(placements)} CHHN placement certificates")


if __name__ == "__main__":
    main()

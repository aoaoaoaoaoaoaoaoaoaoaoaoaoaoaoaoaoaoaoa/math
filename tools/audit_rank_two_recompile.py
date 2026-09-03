#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///

"""Exact bounded filter for four-state paired-family recompilations."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations
from pathlib import Path
from typing import Final, Self, cast

type Scalar = Fraction
type Vector = tuple[Scalar, Scalar, Scalar, Scalar]
type Matrix = tuple[Vector, Vector, Vector, Vector]
type Word = tuple[str, ...]

CONTROLS: Final = ("b", "c", "t")
ZERO: Final[Scalar] = Fraction(0)
ONE: Final[Scalar] = Fraction(1)


def matrix(raw: tuple[tuple[int, ...], ...]) -> Matrix:
    return cast(Matrix, tuple(tuple(Fraction(entry) for entry in row) for row in raw))


def mul_vec(left: Matrix, right: Vector) -> Vector:
    return cast(
        Vector,
        tuple(
            sum((entry * value for entry, value in zip(row, right)), ZERO)
            for row in left
        ),
    )


def outer(column: Vector, row: Vector) -> Matrix:
    return cast(Matrix, tuple(tuple(x * y for y in row) for x in column))


def scaled(scale: Scalar, source: Matrix) -> Matrix:
    return cast(Matrix, tuple(tuple(scale * entry for entry in row) for row in source))


def rank(rows: list[list[Scalar]]) -> int:
    if not rows:
        return 0
    height = len(rows)
    width = len(rows[0])
    pivot = 0
    for column in range(width):
        found = next((row for row in range(pivot, height) if rows[row][column]), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        divisor = rows[pivot][column]
        rows[pivot] = [entry / divisor for entry in rows[pivot]]
        for row in range(height):
            if row == pivot or not rows[row][column]:
                continue
            multiplier = rows[row][column]
            rows[row] = [
                entry - multiplier * pivot_entry
                for entry, pivot_entry in zip(rows[row], rows[pivot])
            ]
        pivot += 1
        if pivot == height:
            break
    return pivot


def matrix_rank(source: Matrix) -> int:
    return rank([list(row) for row in source])


def block_hankel(moments: tuple[Matrix, ...], width: int) -> list[list[Scalar]]:
    return [
        [moments[left + right][i][j] for right in range(width) for j in range(4)]
        for left in range(width)
        for i in range(4)
    ]


@dataclass(frozen=True, slots=True)
class Candidate:
    toggle: Matrix
    data_b: Matrix
    data_c: Matrix
    row: Vector
    column: Vector

    @classmethod
    def from_json(cls, path: Path) -> Self:
        payload = json.loads(path.read_text())

        def scalar(value: int | str) -> Scalar:
            return Fraction(value)

        def vector(name: str) -> Vector:
            values = payload[name]
            if not isinstance(values, list) or len(values) != 4:
                raise ValueError(f"{name} must have four entries")
            return cast(Vector, tuple(scalar(value) for value in values))

        def square(name: str) -> Matrix:
            values = payload[name]
            if (
                not isinstance(values, list)
                or any(not isinstance(row, list) or len(row) != 4 for row in values)
                or len(values) != 4
            ):
                raise ValueError(f"{name} must be 4 by 4")
            return cast(
                Matrix, tuple(tuple(scalar(value) for value in row) for row in values)
            )

        return cls(
            square("toggle"),
            square("data_b"),
            square("data_c"),
            vector("row"),
            vector("column"),
        )

    def role(self, control: str) -> Matrix:
        match control:
            case "b":
                return self.data_b
            case "c":
                return self.data_c
            case "t":
                return self.toggle
            case _:
                raise ValueError(f"unknown control {control!r}")

    def coefficient(self, word: Word) -> Scalar:
        state = self.column
        for control in reversed(word):
            state = mul_vec(self.role(control), state)
        return sum((x * y for x, y in zip(self.row, state)), ZERO)


def bcbcbb_fixture() -> Candidate:
    """Formal `G3-C07` witness with a silent toggle coordinate."""
    return Candidate(
        toggle=matrix(
            ((1, 0, 0, 0), (0, -1, 21_436_039, 0), (0, 0, 1, 0), (0, 0, 0, 1))
        ),
        data_b=matrix(((2, 2, 1, 0), (0, 5, 3_703_455, 0), (0, 0, 1, 0), (0, 0, 0, 0))),
        data_c=matrix(
            (
                (0, 2, -432_372_898, 0),
                (0, 7, 5_236_172, 0),
                (0, 0, 1, 0),
                (0, 0, 0, 0),
            )
        ),
        row=(ONE, ZERO, ZERO, ZERO),
        column=(ONE, Fraction(21_436_039), ONE, ZERO),
    )


def tag_code(beta: int, letter: str) -> tuple[bool, ...]:
    return (True, *(False for _ in range(beta)), True) if letter == "b" else (True,)


def lower_code(beta: int, body: str, phase: str, letter: str) -> tuple[bool, ...]:
    if phase == "erase":
        return (False,)
    if letter == "b":
        return (True, True, False)
    return (
        True,
        *(bit for symbol in body for bit in tag_code(beta, symbol)),
        True,
        False,
    )


def paired_zero(beta: int, body: str, word: Word) -> bool:
    phase = "rule"
    roles: list[tuple[str, str]] = []
    for control in reversed(word):
        if control == "t":
            phase = "erase" if phase == "rule" else "rule"
        else:
            roles.append((phase, control))
            phase = "erase"
    upper = tuple(
        bit for phase, letter in reversed(roles) for bit in tag_code(beta, letter)
    )
    lower = tuple(
        bit
        for phase, letter in reversed(roles)
        for bit in lower_code(beta, body, phase, letter)
    )
    return upper + (True, *(False for _ in range(beta))) == lower


def bounded_filter(
    candidate: Candidate, beta: int, body: str, depth: int
) -> tuple[int, int]:
    checked = 0
    zeros = 0
    marker = (True, *(False for _ in range(beta)))
    stack: list[tuple[Word, Vector, str, tuple[bool, ...], tuple[bool, ...]]] = [
        ((), candidate.column, "rule", (), ())
    ]
    while stack:
        word, state, phase, upper, lower = stack.pop()
        expected = upper + marker == lower
        actual = sum((x * y for x, y in zip(candidate.row, state)), ZERO) == 0
        if expected != actual:
            spelling = "".join(word) or "ε"
            raise AssertionError(
                f"first mismatch at {spelling}: paired={expected}, candidate={actual}"
            )
        checked += 1
        zeros += expected
        if len(word) == depth:
            continue
        for control in CONTROLS:
            next_word = (control, *word)
            next_state = mul_vec(candidate.role(control), state)
            if control == "t":
                next_phase = "erase" if phase == "rule" else "rule"
                stack.append((next_word, next_state, next_phase, upper, lower))
            else:
                stack.append(
                    (
                        next_word,
                        next_state,
                        "erase",
                        tag_code(beta, control) + upper,
                        lower_code(beta, body, phase, control) + lower,
                    )
                )
    return checked, zeros


def stroke(word: str) -> Word:
    return (word[0], "t", word[1], word[2])


def mixed_terminal(bits: tuple[bool, ...]) -> Word:
    prefix = stroke("cbc") + stroke("bcb") + stroke("bbb")
    block_a = stroke("bbb") + stroke("bcb") + stroke("cbb")
    block_b = stroke("bbb") + stroke("cbc") + stroke("bbb")
    return (
        prefix
        + tuple(control for bit in bits for control in (block_b if bit else block_a))
        + ("t",)
    )


def audit_mixed_terminals(candidate: Candidate) -> None:
    for bits in ((), (False,), (True,), (False, True)):
        word = mixed_terminal(bits)
        assert paired_zero(3, "bcbcbb", word)
        assert candidate.coefficient(word) == 0


def geometric_ranks(candidate: Candidate, ratio: Scalar) -> dict[str, int]:
    separator = outer(candidate.column, candidate.row)
    roles = {"T": candidate.toggle, "B": candidate.data_b, "C": candidate.data_c}
    result: dict[str, int] = {}
    for order in permutations("TBC"):
        moments = tuple(roles[label] for label in order) + tuple(
            scaled(ratio**offset, separator) for offset in range(4)
        )
        result["".join(order)] = rank(block_hankel(moments, 4))
    return result


def period_four_ranks(candidate: Candidate) -> dict[str, int]:
    roles = {
        "T": candidate.toggle,
        "B": candidate.data_b,
        "C": candidate.data_c,
        "P": outer(candidate.column, candidate.row),
    }
    result: dict[str, int] = {}
    for order in permutations("TBCP"):
        moments = tuple(roles[label] for label in order)
        periodic = tuple(moments[index % 4] for index in range(7))
        result["".join(order)] = rank(block_hankel(periodic, 4))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--beta", type=int, default=3)
    parser.add_argument("--body", choices=("b", "c"), action="append")
    parser.add_argument("--max-length", type=int, default=10)
    arguments = parser.parse_args()
    body = "".join(arguments.body) if arguments.body else "bcbcbb"
    candidate = (
        Candidate.from_json(arguments.candidate)
        if arguments.candidate
        else bcbcbb_fixture()
    )
    if not arguments.candidate and (arguments.beta != 3 or body != "bcbcbb"):
        parser.error("the built-in fixture is specific to beta=3, body=bcbcbb")

    checked, zeros = bounded_filter(
        candidate, arguments.beta, body, arguments.max_length
    )
    if not arguments.candidate:
        audit_mixed_terminals(candidate)
    role_ranks = tuple(
        matrix_rank(role)
        for role in (candidate.toggle, candidate.data_b, candidate.data_c)
    )
    geometric = geometric_ranks(candidate, ONE)
    periodic = period_four_ranks(candidate)
    print(f"checked words: {checked}; bounded zeros: {zeros}")
    print(f"ranks T/B/C/P: {role_ranks[0]}/{role_ranks[1]}/{role_ranks[2]}/1")
    print("geometric:", " ".join(f"{key}={value}" for key, value in geometric.items()))
    print(f"geometric minimum: {min(geometric.values())}")
    print(f"period-four minimum: {min(periodic.values())}")


if __name__ == "__main__":
    main()

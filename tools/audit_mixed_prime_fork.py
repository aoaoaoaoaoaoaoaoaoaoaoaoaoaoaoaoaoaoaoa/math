#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = []
# ///

"""Exhaust the physical mixed-prime five-factor fork equation at bounded length.

For positive raw words X, Y, and Z over D(t)=2t/3 and T(t)=3t/5+1, this searches

    Y Z X Y X = X Z Y X Y

as equality of affine actions. Two macros are enumerated exactly. For each possible prime-unique
slope of the third, its offset is forced by the linear action equation and exact meet-in-the-
middle membership decides whether a word realizes it. The only search prune is the proved
fixed-point interval [0,5/2]. All arithmetic uses ``Fraction``.
"""

from __future__ import annotations

import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product

Q = Fraction


@dataclass(frozen=True, slots=True)
class Action:
    slope: Fraction
    offset: Fraction
    word: str
    dilates: int


def append(action: Action, letter: str) -> Action:
    match letter:
        case "D":
            return Action(
                action.slope * Q(2, 3),
                action.offset,
                action.word + letter,
                action.dilates + 1,
            )
        case "T":
            return Action(
                action.slope * Q(3, 5),
                action.offset + action.slope,
                action.word + letter,
                action.dilates,
            )
        case _:
            raise AssertionError(letter)


@cache
def level(length: int) -> tuple[Action, ...]:
    frontier = (Action(Q(1), Q(0), "", 0),)
    for _ in range(length):
        frontier = tuple(
            append(action, letter) for action in frontier for letter in "DT"
        )
    return frontier


@cache
def action_index(length: int, dilates: int) -> dict[tuple[Fraction, Fraction], str]:
    return {
        (action.slope, action.offset): action.word
        for action in level(length)
        if action.dilates == dilates
    }


def slope(length: int, dilates: int) -> Fraction:
    return Q(2, 3) ** dilates * Q(3, 5) ** (length - dilates)


def find_word(
    length: int, dilates: int, target: tuple[Fraction, Fraction]
) -> str | None:
    if length <= 16:
        return action_index(length, dilates).get(target)

    left_length = length // 2
    right_length = length - left_length
    target_slope, target_offset = target
    for left_dilates in range(
        max(0, dilates - right_length), min(left_length, dilates) + 1
    ):
        right_dilates = dilates - left_dilates
        right_index = action_index(right_length, right_dilates)
        for left in level(left_length):
            if left.dilates != left_dilates:
                continue
            right_target = (
                target_slope / left.slope,
                (target_offset - left.offset) / left.slope,
            )
            if (right_word := right_index.get(right_target)) is not None:
                return left.word + right_word
    return None


def compose(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    left_slope, left_offset = left
    right_slope, right_offset = right
    return left_slope * right_slope, left_slope * right_offset + left_offset


def word_action(word: str) -> tuple[Fraction, Fraction]:
    result = (Q(1), Q(0))
    generators = {"D": (Q(2, 3), Q(0)), "T": (Q(3, 5), Q(1))}
    for letter in word:
        result = compose(result, generators[letter])
    return result


def fixed_point(action: tuple[Fraction, Fraction]) -> Fraction:
    action_slope, action_offset = action
    return action_offset / (1 - action_slope)


@cache
def backward_word(dilates: int, translates: int, numerator: int) -> str | None:
    """Invert the exact homogeneous offset recurrence to one raw word, if it exists."""
    if numerator < 0:
        return None
    slope_numerator = 2**dilates * 3**translates
    denominator = 3**dilates * 5**translates
    if 2 * numerator > 5 * (denominator - slope_numerator):
        return None
    if dilates == 0 and translates == 0:
        return "" if numerator == 0 else None
    if dilates > 0 and numerator % 3 == 0:
        prefix = backward_word(dilates - 1, translates, numerator // 3)
        if prefix is not None:
            return prefix + "D"
    if translates > 0 and numerator % 5 == 0:
        preceding_slope_numerator = 2**dilates * 3 ** (translates - 1)
        prefix = backward_word(
            dilates,
            translates - 1,
            numerator // 5 - preceding_slope_numerator,
        )
        if prefix is not None:
            return prefix + "T"
    return None


def backward_target_word(dilates: int, translates: int, offset: Fraction) -> str | None:
    numerator = offset * 3**dilates * 5**translates
    if numerator.denominator != 1:
        return None
    return backward_word(dilates, translates, numerator.numerator)


def search_thin_rectangle(
    data_length_max: int, toggle_length_max: int
) -> tuple[str, str, str] | None:
    """Search short data macros against a much deeper toggle by backward normal form."""
    data_words = tuple(
        action for length in range(1, data_length_max + 1) for action in level(length)
    )
    for x in data_words:
        a, b = x.slope, x.offset
        for y in data_words:
            c, d = y.slope, y.offset
            if (a, b) == (c, d) or a == c or fixed_point((a, b)) == fixed_point((c, d)):
                continue
            for toggle_length in range(1, toggle_length_max + 1):
                for dilates in range(toggle_length + 1):
                    translates = toggle_length - dilates
                    e = slope(toggle_length, dilates)
                    coefficient_b = e * c * (a * c - a + 1) - 1
                    coefficient_d = 1 - a * e * (a * c - c + 1)
                    f = -(coefficient_b * b + coefficient_d * d) / (c - a)
                    z_word = backward_target_word(dilates, translates, f)
                    if z_word is None:
                        continue
                    z = word_action(z_word)
                    if z in ((a, b), (c, d)):
                        continue
                    if fixed_point((a, b)) == fixed_point((c, d)) == fixed_point(z):
                        continue
                    lhs = y.word + z_word + x.word + y.word + x.word
                    rhs = x.word + z_word + y.word + x.word + y.word
                    assert word_action(lhs) == word_action(rhs)
                    return x.word, y.word, z_word
    print(
        f"none 1<=|X|,|Y|<={data_length_max}, 1<=|Z|<={toggle_length_max}",
        flush=True,
    )
    return None


def search_length(relation_length: int) -> tuple[str, str, str] | None:
    started = time.monotonic()
    trial_count = 0
    target_count = 0
    for x_length, y_length in product(range(1, relation_length), repeat=2):
        z_length = relation_length - 2 * x_length - 2 * y_length
        if z_length < 1:
            continue

        def accept(
            x_word: str, y_word: str, z_word: str
        ) -> tuple[str, str, str] | None:
            x = word_action(x_word)
            y = word_action(y_word)
            z = word_action(z_word)
            if x == y or x == z or y == z:
                return None
            if fixed_point(x) == fixed_point(y) == fixed_point(z):
                return None
            lhs = y_word + z_word + x_word + y_word + x_word
            rhs = x_word + z_word + y_word + x_word + y_word
            assert len(lhs) == relation_length == len(rhs)
            assert word_action(lhs) == word_action(rhs)
            return x_word, y_word, z_word

        z_cost = 2 ** (x_length + y_length) * (z_length + 1)
        x_cost = 2 ** (y_length + z_length) * (x_length + 1)
        y_cost = 2 ** (x_length + z_length) * (y_length + 1)
        target = min((z_cost, "z"), (x_cost, "x"), (y_cost, "y"))[1]

        if target == "z":
            for x_action in level(x_length):
                a, b = x_action.slope, x_action.offset
                for y_action in level(y_length):
                    c, d = y_action.slope, y_action.offset
                    trial_count += 1
                    if a == c:
                        continue
                    for dilates in range(z_length + 1):
                        e = slope(z_length, dilates)
                        coefficient_b = e * c * (a * c - a + 1) - 1
                        coefficient_d = 1 - a * e * (a * c - c + 1)
                        f = -(coefficient_b * b + coefficient_d * d) / (c - a)
                        target_count += 1
                        if not Q(0) <= f <= Q(5, 2) * (1 - e):
                            continue
                        if (z_word := find_word(z_length, dilates, (e, f))) is None:
                            continue
                        if (
                            result := accept(x_action.word, y_action.word, z_word)
                        ) is not None:
                            return result

        elif target == "x":
            for y_action in level(y_length):
                c, d = y_action.slope, y_action.offset
                for z_action in level(z_length):
                    e, f = z_action.slope, z_action.offset
                    trial_count += 1
                    for dilates in range(x_length + 1):
                        a = slope(x_length, dilates)
                        coefficient_b = e * c * (a * c - a + 1) - 1
                        coefficient_d = 1 - a * e * (a * c - c + 1)
                        b = -(coefficient_d * d + (c - a) * f) / coefficient_b
                        target_count += 1
                        if not Q(0) <= b <= Q(5, 2) * (1 - a):
                            continue
                        if (x_word := find_word(x_length, dilates, (a, b))) is None:
                            continue
                        if (
                            result := accept(x_word, y_action.word, z_action.word)
                        ) is not None:
                            return result

        else:
            for x_action in level(x_length):
                a, b = x_action.slope, x_action.offset
                for z_action in level(z_length):
                    e, f = z_action.slope, z_action.offset
                    trial_count += 1
                    for dilates in range(y_length + 1):
                        c = slope(y_length, dilates)
                        coefficient_b = e * c * (a * c - a + 1) - 1
                        coefficient_d = 1 - a * e * (a * c - c + 1)
                        d = -(coefficient_b * b + (c - a) * f) / coefficient_d
                        target_count += 1
                        if not Q(0) <= d <= Q(5, 2) * (1 - c):
                            continue
                        if (y_word := find_word(y_length, dilates, (c, d))) is None:
                            continue
                        if (
                            result := accept(x_action.word, y_word, z_action.word)
                        ) is not None:
                            return result

    print(
        f"none N={relation_length} after {time.monotonic() - started:.3f}s "
        f"trials={trial_count} targets={target_count}",
        flush=True,
    )
    return None


def main() -> None:
    if sys.argv[1:] == ["self-check"]:
        assert word_action("") == (Q(1), Q(0))
        assert word_action("DT") == (Q(2, 5), Q(2, 3))
        assert find_word(2, 1, word_action("DT")) == "DT"
        assert backward_target_word(1, 1, word_action("DT")[1]) == "DT"
        assert all(search_length(length) is None for length in range(1, 13))
        print("mixed-prime fork audit self-check: yes")
        return

    if len(sys.argv) == 4 and sys.argv[1] == "thin":
        if (
            words := search_thin_rectangle(int(sys.argv[2]), int(sys.argv[3]))
        ) is not None:
            raise SystemExit(f"fork candidate found: {words}")
        return

    if len(sys.argv) != 3:
        raise SystemExit(
            f"usage: {sys.argv[0]} LOWER UPPER | {sys.argv[0]} thin X_MAX Z_MAX | "
            f"{sys.argv[0]} self-check"
        )
    lower = int(sys.argv[1])
    upper = int(sys.argv[2])
    for relation_length in range(lower, upper + 1):
        if (words := search_length(relation_length)) is None:
            continue
        x, y, z = words
        lhs = y + z + x + y + x
        rhs = x + z + y + x + y
        print(f"x={x!r}\ny={y!r}\nz={z!r}")
        print(f"lhs={lhs}\nrhs={rhs}\ndistinct={lhs != rhs}")
        print(f"X={word_action(x)}\nY={word_action(y)}\nZ={word_action(z)}")
        print(
            "fixed="
            f"{fixed_point(word_action(x))},"
            f"{fixed_point(word_action(y))},"
            f"{fixed_point(word_action(z))}"
        )
        return


if __name__ == "__main__":
    main()

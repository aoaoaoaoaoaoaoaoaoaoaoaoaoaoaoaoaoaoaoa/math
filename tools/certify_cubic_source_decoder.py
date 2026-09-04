#!/usr/bin/env python3
"""Exact cross-check for the cubic binary-pump separator-source decoder."""

from fractions import Fraction
from itertools import product

PRIME = 197
RATIO = (Fraction(1, 625), Fraction(197, 336000))
DIGIT = (Fraction(1712, 5625), Fraction(122527, 432000))
SOURCE_OFFSET = Fraction(11, 123)


def residue(value: Fraction) -> int:
    return value.numerator * pow(value.denominator % PRIME, -1, PRIME) % PRIME


def affine_code(bits: tuple[int, ...]) -> Fraction:
    value = Fraction(0)
    for bit in reversed(bits):
        value = DIGIT[bit] + RATIO[bit] * value
    return value


def source_coordinate(bits: tuple[int, ...]) -> Fraction:
    address = affine_code(tuple(reversed(bits)))
    ratio = Fraction(1)
    for bit in bits:
        ratio *= RATIO[bit]
    return (SOURCE_OFFSET - address) / ratio


def main() -> None:
    q0, d0, d1, target = map(
        residue, (RATIO[0], DIGIT[0], DIGIT[1], SOURCE_OFFSET)
    )
    assert (q0, d0, d1, target) == (29, 88, 66, 109)

    fixed = d0 * pow((1 - q0) % PRIME, -1, PRIME) % PRIME
    assert fixed == 25
    assert pow(q0, 49, PRIME) == 1
    assert pow(target - fixed, 49, PRIME) == 183
    assert pow(-fixed, 49, PRIME) == 1
    assert pow(d1 - fixed, 49, PRIME) == 196

    lower = DIGIT[1] - SOURCE_OFFSET
    upper = DIGIT[0] + RATIO[0] - SOURCE_OFFSET
    assert lower == Fraction(3439607, 17712000)
    assert upper == Fraction(49936, 230625)
    assert 0 < lower <= upper < 625 * lower

    for width in range(15):
        coordinates = {
            source_coordinate(bits) for bits in product((0, 1), repeat=width)
        }
        assert len(coordinates) == 2**width


if __name__ == "__main__":
    main()

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///

"""Explore finite-field shadows of the five-state setter's projective transfer."""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from types import EllipsisType

type Point = int | None


def ternary_code(bits: str) -> int:
    value = 0
    for bit in bits:
        value = 3 * value + (2 if bit == "1" else 1)
    return value


def tag_code(beta: int, letter: str) -> str:
    match letter:
        case "b":
            return "1" + "0" * beta + "1"
        case "c":
            return "1"
        case _:
            raise ValueError(f"invalid tag letter: {letter}")


@dataclass(frozen=True, slots=True)
class SideProduct:
    upper_value: int
    upper_scale: int
    lower_value: int
    lower_scale: int

    def then(self, suffix: SideProduct, modulus: int) -> SideProduct:
        return SideProduct(
            (self.upper_value * suffix.upper_scale + suffix.upper_value) % modulus,
            self.upper_scale * suffix.upper_scale % modulus,
            (self.lower_value * suffix.lower_scale + suffix.lower_value) % modulus,
            self.lower_scale * suffix.lower_scale % modulus,
        )

    def then_exact(self, suffix: SideProduct) -> SideProduct:
        return SideProduct(
            self.upper_value * suffix.upper_scale + suffix.upper_value,
            self.upper_scale * suffix.upper_scale,
            self.lower_value * suffix.lower_scale + suffix.lower_value,
            self.lower_scale * suffix.lower_scale,
        )


@dataclass(frozen=True, slots=True)
class Transfer:
    numerator_slope: int
    numerator_offset: int
    denominator_slope: int
    denominator_offset: int

    def apply(self, point: Point, modulus: int) -> Point | EllipsisType:
        if point is None:
            numerator = self.numerator_slope
            denominator = self.denominator_slope
        else:
            numerator = (self.numerator_slope * point + self.numerator_offset) % modulus
            denominator = (
                self.denominator_slope * point + self.denominator_offset
            ) % modulus
        if denominator == 0:
            return ... if numerator == 0 else None
        return numerator * pow(denominator, -1, modulus) % modulus

    def poles(self, modulus: int) -> frozenset[Point] | None:
        if self.denominator_slope:
            return frozenset(
                {
                    -self.denominator_offset
                    * pow(self.denominator_slope, -1, modulus)
                    % modulus
                }
            )
        if self.denominator_offset:
            return frozenset()
        return None


def role_generators(beta: int, body: str, modulus: int) -> tuple[SideProduct, ...]:
    upper_b = tag_code(beta, "b")
    upper_c = tag_code(beta, "c")
    lower_rule_c = "1" + "".join(tag_code(beta, letter) for letter in body) + "10"

    def role(upper: str, lower: str) -> SideProduct:
        return SideProduct(
            ternary_code(upper) % modulus,
            pow(3, len(upper), modulus),
            ternary_code(lower) % modulus,
            pow(3, len(lower), modulus),
        )

    return (
        role(upper_b, "110"),
        role(upper_b, "0"),
        role(upper_c, lower_rule_c),
        role(upper_c, "0"),
    )


def exact_role_generators(beta: int, body: str) -> tuple[SideProduct, ...]:
    upper_b = tag_code(beta, "b")
    upper_c = tag_code(beta, "c")
    lower_rule_c = "1" + "".join(tag_code(beta, letter) for letter in body) + "10"

    def role(upper: str, lower: str) -> SideProduct:
        return SideProduct(
            ternary_code(upper),
            3 ** len(upper),
            ternary_code(lower),
            3 ** len(lower),
        )

    return (
        role(upper_b, "110"),
        role(upper_b, "0"),
        role(upper_c, lower_rule_c),
        role(upper_c, "0"),
    )


def side_semigroup(beta: int, body: str, modulus: int) -> frozenset[SideProduct]:
    generators = role_generators(beta, body, modulus)
    seen: set[SideProduct] = set(generators)
    queue = deque(generators)
    while queue:
        product = queue.popleft()
        for generator in generators:
            successor = product.then(generator, modulus)
            if successor not in seen:
                seen.add(successor)
                queue.append(successor)
    return frozenset(seen)


def transfers(
    products: frozenset[SideProduct], beta: int, modulus: int
) -> frozenset[Transfer] | None:
    rho = pow(3, beta, modulus)
    marker_value = (5 * rho - 1) * pow(2, -1, modulus) % modulus
    marker_scale = 3 * rho % modulus
    denominator = 2 * (rho + 1) % modulus
    if denominator == 0:
        return None
    coefficient = -(17 * rho - 1) * pow(denominator, -1, modulus) % modulus
    return frozenset(
        Transfer(
            coefficient * product.lower_value % modulus,
            coefficient
            * (
                marker_value * (product.upper_scale - 1)
                - marker_scale * product.upper_value
            )
            % modulus,
            -product.lower_value % modulus,
            (marker_value + marker_scale * product.upper_value) % modulus,
        )
        for product in products
    )


@dataclass(frozen=True, slots=True)
class Shadow:
    modulus: int
    side_products: int
    transfers: int
    pole_points: int
    reachable_points: int
    pole_intersection: int
    indeterminate: bool


@dataclass(frozen=True, slots=True)
class Collision:
    start: int
    image_word: tuple[int, int]
    pole_word: tuple[int, int]
    value: Fraction


@dataclass(frozen=True, slots=True)
class OrbitCollision:
    start: int
    blocks: tuple[tuple[int, int], ...]


@dataclass(frozen=True, slots=True)
class OrbitSearch:
    collision: OrbitCollision | None
    depths: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class ReverseDiscrepancy:
    """Exact right-to-left cancellation state for one Neary role word."""

    common_suffix: int
    processed_roles: int
    upper_residual: str
    lower_residual: str
    mismatch: bool


@dataclass(frozen=True, slots=True)
class IntegralUnitPole:
    word: tuple[int, ...]
    normalized_pole: int


def role_words(beta: int, body: str) -> tuple[tuple[str, str], ...]:
    upper_b = tag_code(beta, "b")
    upper_c = tag_code(beta, "c")
    lower_rule_c = "1" + "".join(tag_code(beta, letter) for letter in body) + "10"
    return (
        (upper_b, "110"),
        (upper_b, "0"),
        (upper_c, lower_rule_c),
        (upper_c, "0"),
    )


def reverse_discrepancy(
    beta: int, body: str, word: tuple[int, ...]
) -> ReverseDiscrepancy:
    """Expose the first mismatch in ``upper(word)·marker`` versus ``lower(word)``.

    Reversal turns common-suffix cancellation into common-prefix cancellation.
    Before the first mismatch, at least one residual is empty. Once both
    residuals are nonempty, their first bits differ and no unprocessed role can
    enlarge the common suffix.
    """

    roles = role_words(beta, body)
    upper = ("1" + "0" * beta)[::-1]
    lower = ""
    matched = 0

    for processed, role in enumerate(reversed(word), start=1):
        role_upper, role_lower = roles[role]
        upper += role_upper[::-1]
        lower += role_lower[::-1]
        common = 0
        for upper_bit, lower_bit in zip(upper, lower, strict=False):
            if upper_bit != lower_bit:
                break
            common += 1
        matched += common
        upper = upper[common:]
        lower = lower[common:]
        if upper and lower:
            return ReverseDiscrepancy(matched, processed, upper, lower, True)

    return ReverseDiscrepancy(matched, len(word), upper, lower, False)


def normalized_boundary_discrepancy(
    beta: int, body: str, word: tuple[int, ...]
) -> tuple[int, int]:
    """Return the boundary-one resonance gap and its 3-adic unit."""

    roles = role_words(beta, body)
    discrepancy = reverse_discrepancy(beta, body, word)
    upper = "".join(roles[role][0] for role in word)
    lower = "".join(roles[role][1] for role in word)
    difference = ternary_code(upper + "1" + "0" * beta) - ternary_code(lower)
    divisor = 3**discrepancy.common_suffix
    quotient, remainder = divmod(difference, divisor)
    assert remainder == 0
    return len(upper) - discrepancy.common_suffix, quotient


def find_false_integral_unit_pole(
    beta: int, body: str, max_role_length: int
) -> IntegralUnitPole | None:
    """Find a nonterminal valuation-one pole with integral normalized value."""

    rho = 3**beta
    marker = (5 * rho - 1) // 2
    head = (17 * rho - 1) // 2
    tail = rho + 1
    generators = exact_role_generators(beta, body)

    def visit(
        product: SideProduct, word: tuple[int, ...], remaining: int
    ) -> IntegralUnitPole | None:
        if len(word) >= 2 and word[-1] in (1, 3):
            punctuated_upper = marker + 3 * rho * product.upper_value
            centered_pole = tail * punctuated_upper - head * product.lower_value
            if three_adic_valuation(centered_pole) == 1:
                numerator = -3 * head * marker * product.lower_value
                normalized, remainder = divmod(numerator, centered_pole)
                if (
                    remainder == 0
                    and normalized % 3
                    and punctuated_upper != product.lower_value
                ):
                    return IntegralUnitPole(word, normalized)
        if remaining == 0:
            return None
        for role, generator in enumerate(generators):
            found = visit(product.then_exact(generator), (*word, role), remaining - 1)
            if found is not None:
                return found
        return None

    return visit(SideProduct(0, 1, 0, 1), (), max_role_length)


def exact_transfer(product: SideProduct, start: Fraction, beta: int) -> Fraction | None:
    rho = 3**beta
    marker_value = (5 * rho - 1) // 2
    marker_scale = 3 * rho
    coefficient = Fraction(-(17 * rho - 1), 2 * (rho + 1))
    denominator = (
        marker_value + marker_scale * product.upper_value - product.lower_value * start
    )
    if denominator == 0:
        return None
    numerator = (
        product.lower_value * start
        + marker_value * (product.upper_scale - 1)
        - marker_scale * product.upper_value
    )
    return coefficient * Fraction(numerator, denominator)


def exact_pole(product: SideProduct, beta: int) -> Fraction:
    rho = 3**beta
    marker_value = (5 * rho - 1) // 2
    marker_scale = 3 * rho
    return Fraction(
        marker_value + marker_scale * product.upper_value,
        product.lower_value,
    )


def power_of_three_exponent(value: int) -> int:
    exponent = 0
    while value > 1:
        quotient, remainder = divmod(value, 3)
        if remainder:
            raise ValueError(f"{value} is not a power of three")
        value = quotient
        exponent += 1
    return exponent


def three_adic_valuation(value: int) -> int:
    if value == 0:
        raise ValueError("the 3-adic valuation of zero is infinite")
    valuation = 0
    while value % 3 == 0:
        value //= 3
        valuation += 1
    return valuation


def centered_point(x: int, y: int, beta: int) -> Fraction:
    rho = 3**beta
    marker_value = (5 * rho - 1) // 2
    setter_head = (17 * rho - 1) // 2
    setter_tail = rho + 1
    return Fraction(setter_head, setter_tail) - Fraction(
        setter_head * marker_value * x, y
    )


def centered_step(x: int, y: int, product: SideProduct, beta: int) -> tuple[int, int]:
    rho = 3**beta
    marker_value = (5 * rho - 1) // 2
    marker_scale = 3 * rho
    setter_head = (17 * rho - 1) // 2
    setter_tail = rho + 1
    punctuated_upper = marker_value + marker_scale * product.upper_value
    centered_pole = setter_tail * punctuated_upper - setter_head * product.lower_value
    coupling = setter_tail * setter_head * marker_value
    return (
        product.upper_scale * y,
        centered_pole * y + coupling * product.lower_value * x,
    )


def audit_centered_carry() -> None:
    beta = 3
    rho = 3**beta
    marker_value = (5 * rho - 1) // 2
    setter_head = (17 * rho - 1) // 2
    setter_tail = rho + 1
    starts = (
        (0, (1, setter_tail * marker_value)),
        (1, (3, setter_tail * setter_head)),
    )
    blocks = exact_blocks(beta, "bbcc", 3)

    for start, (x, y) in starts:
        assert centered_point(x, y, beta) == start
        for product, _word in blocks:
            stepped_x, stepped_y = centered_step(x, y, product, beta)
            image = exact_transfer(product, Fraction(start), beta)
            assert (
                image is None
                if stepped_y == 0
                else (centered_point(stepped_x, stepped_y, beta) == image)
            )

    for product, _word in blocks:
        punctuated_upper = marker_value + 3 * rho * product.upper_value
        centered_pole = (
            setter_tail * punctuated_upper - setter_head * product.lower_value
        )
        shell = three_adic_valuation(centered_pole)
        upper_length = power_of_three_exponent(product.upper_scale)
        for d in range(-2, upper_length + beta + 3):
            if d == shell:
                continue
            expected = upper_length - min(d, shell)
            x = 3 ** max(d, 0)
            y = 3 ** max(-d, 0)
            stepped_x, stepped_y = centered_step(x, y, product, beta)
            actual = three_adic_valuation(stepped_x) - three_adic_valuation(stepped_y)
            assert actual == expected

    roles = role_words(beta, "bbcc")
    layer = [(index,) for index in range(len(roles))]
    for _length in range(1, 6):
        for word in layer:
            discrepancy = reverse_discrepancy(beta, "bbcc", word)
            upper = "".join(roles[role][0] for role in word) + "1" + "0" * beta
            lower = "".join(roles[role][1] for role in word)
            expected_suffix = 0
            for upper_bit, lower_bit in zip(
                reversed(upper), reversed(lower), strict=False
            ):
                if upper_bit != lower_bit:
                    break
                expected_suffix += 1
            assert discrepancy.common_suffix == expected_suffix

            upper_length = len(upper) - beta - 1
            gap = upper_length - expected_suffix
            prefix = word[: len(word) - discrepancy.processed_roles]
            prefix_upper_length = sum(len(roles[role][0]) for role in prefix)
            if discrepancy.mismatch:
                assert prefix_upper_length <= gap + beta + 1
            elif gap in (1, beta):
                assert not discrepancy.lower_residual
                assert len(discrepancy.upper_residual) == gap + beta + 1

            checked_gap, unit = normalized_boundary_discrepancy(beta, "bbcc", word)
            assert checked_gap == gap
            if gap == beta:
                assert unit != -marker_value

            upper_bits = "".join(roles[role][0] for role in word)
            assert "0" + "1" + "0" * beta not in upper_bits + "1" + "0" * beta

        layer = [(*word, role) for word in layer for role in range(len(roles))]

    for width in range(3, 9):
        power = 3**width
        marker = (5 * power - 1) // 2
        head = (17 * power - 1) // 2
        tail = power + 1
        upper_b = ternary_code(tag_code(width, "b"))
        punctuated_b = marker + 3 * power * upper_b
        centered_b = tail * punctuated_b - head
        assert centered_b == power * (45 * power**2 + 53 * power - 10) // 2
        required_b = Fraction(-head * marker * power, centered_b)
        assert -1 < required_b < 0

        punctuated_c = marker + 3 * power * ternary_code(tag_code(width, "c"))
        assert punctuated_c == head
        centered_c = tail * punctuated_c - head
        assert Fraction(-head * marker * power, centered_c) == -marker


def next_exact_layer(
    layer: list[tuple[SideProduct, int]],
    generators: tuple[SideProduct, ...],
) -> list[tuple[SideProduct, int]]:
    return [
        (product.then_exact(generator), 4 * code + role)
        for product, code in layer
        for role, generator in enumerate(generators)
    ]


def find_exact_collision(
    beta: int, body: str, max_role_length: int
) -> Collision | None:
    generators = exact_role_generators(beta, body)
    poles: dict[Fraction, tuple[int, int]] = {}
    layer = [(SideProduct(0, 1, 0, 1), 0)]
    for length in range(1, max_role_length + 1):
        layer = next_exact_layer(layer, generators)
        for product, code in layer:
            poles.setdefault(exact_pole(product, beta), (length, code))

    layer = [(SideProduct(0, 1, 0, 1), 0)]
    for length in range(1, max_role_length + 1):
        layer = next_exact_layer(layer, generators)
        for product, code in layer:
            for start in (0, 1):
                image = exact_transfer(product, Fraction(start), beta)
                if image is not None and image in poles:
                    return Collision(start, (length, code), poles[image], image)
    return None


def exact_blocks(
    beta: int, body: str, max_role_length: int
) -> tuple[tuple[SideProduct, tuple[int, int]], ...]:
    generators = exact_role_generators(beta, body)
    blocks: list[tuple[SideProduct, tuple[int, int]]] = []
    layer = [(SideProduct(0, 1, 0, 1), 0)]
    for length in range(1, max_role_length + 1):
        layer = next_exact_layer(layer, generators)
        blocks.extend((product, (length, code)) for product, code in layer)
    return tuple(blocks)


def search_exact_orbits(
    beta: int,
    body: str,
    max_role_length: int,
    max_square_runs: int,
) -> OrbitSearch:
    blocks = exact_blocks(beta, body, max_role_length)
    states: dict[Fraction, tuple[int, tuple[tuple[int, int], ...]]] = {
        Fraction(0): (0, ()),
        Fraction(1): (1, ()),
    }
    depths: list[int] = []
    for depth in range(1, max_square_runs + 1):
        successors: dict[Fraction, tuple[int, tuple[tuple[int, int], ...]]] = {}
        for state, (start, path) in states.items():
            for product, word in blocks:
                image = exact_transfer(product, state, beta)
                if image is None:
                    if depth == 1 and start == 1:
                        continue
                    return OrbitSearch(
                        OrbitCollision(start, (*path, word)),
                        tuple(depths),
                    )
                successors.setdefault(image, (start, (*path, word)))
        states = successors
        depths.append(len(states))
    return OrbitSearch(None, tuple(depths))


def shadow(beta: int, body: str, modulus: int) -> Shadow | None:
    products = side_semigroup(beta, body, modulus)
    transfer_set = transfers(products, beta, modulus)
    if transfer_set is None:
        return None

    pole_points: set[Point] = set()
    for transfer in transfer_set:
        poles = transfer.poles(modulus)
        if poles is None:
            return Shadow(
                modulus,
                len(products),
                len(transfer_set),
                modulus + 1,
                0,
                0,
                True,
            )
        pole_points.update(poles)

    seeds: set[Point] = set()
    indeterminate = False
    for start in (0, 1):
        for transfer in transfer_set:
            image = transfer.apply(start, modulus)
            if image is ...:
                indeterminate = True
            elif image is not None:
                seeds.add(image)

    reachable = set(seeds)
    queue = deque(seeds)
    while queue:
        point = queue.popleft()
        for transfer in transfer_set:
            image = transfer.apply(point, modulus)
            if image is ...:
                indeterminate = True
            elif image is not None and image not in reachable:
                reachable.add(image)
                queue.append(image)

    return Shadow(
        modulus,
        len(products),
        len(transfer_set),
        len(pole_points),
        len(reachable),
        len(reachable & pole_points),
        indeterminate,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta", type=int, default=3)
    parser.add_argument("--body", default="bb")
    parser.add_argument(
        "--primes",
        type=int,
        nargs="+",
        default=[5, 7, 11, 13, 17, 19, 23],
    )
    parser.add_argument("--max-role-length", type=int, default=0)
    parser.add_argument("--max-square-runs", type=int, default=0)
    parser.add_argument("--search-unit-poles", type=int, default=0)
    parser.add_argument("--audit", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.audit:
        audit_centered_carry()
        assert find_exact_collision(3, "bbcc", 5) is None
        audit_orbits = search_exact_orbits(3, "bbcc", 3, 2)
        assert audit_orbits == OrbitSearch(None, (96, 8064))
        print("bounded exact setter audit:", audit_orbits)
    if args.max_role_length:
        print(
            "exact collision:",
            find_exact_collision(args.beta, args.body, args.max_role_length),
        )
    if args.max_square_runs:
        print(
            "exact orbit search:",
            search_exact_orbits(
                args.beta,
                args.body,
                args.max_role_length,
                args.max_square_runs,
            ),
        )
    if args.search_unit_poles:
        print(
            "false integral unit pole:",
            find_false_integral_unit_pole(
                args.beta,
                args.body,
                args.search_unit_poles,
            ),
        )
    for prime in args.primes:
        result = shadow(args.beta, args.body, prime)
        print(prime, "singular constants" if result is None else result)


if __name__ == "__main__":
    main()

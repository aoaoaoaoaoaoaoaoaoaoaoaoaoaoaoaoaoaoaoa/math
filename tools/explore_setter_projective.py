#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///

"""Explore exact and finite-field shadows of both five-state setter digit orders."""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from types import EllipsisType

type Point = int | None


@dataclass(frozen=True, slots=True)
class SetterConstants:
    rho: int
    marker: int
    scale: int
    head: int
    tail: int


def ternary_code(bits: str, *, swapped: bool = False) -> int:
    value = 0
    for bit in bits:
        value = 3 * value + (
            (1 if bit == "1" else 2) if swapped else (2 if bit == "1" else 1)
        )
    return value


def setter_constants(beta: int, *, swapped: bool = False) -> SetterConstants:
    rho = 3**beta
    marker = ternary_code("1" + "0" * beta, swapped=swapped)
    scale = 3 * rho
    head = marker + scale * ternary_code("1", swapped=swapped)
    return SetterConstants(rho, marker, scale, head, head - 3 * marker)


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


def role_generators(
    beta: int, body: str, modulus: int, *, swapped: bool = False
) -> tuple[SideProduct, ...]:
    upper_b = tag_code(beta, "b")
    upper_c = tag_code(beta, "c")
    lower_rule_c = "1" + "".join(tag_code(beta, letter) for letter in body) + "10"

    def role(upper: str, lower: str) -> SideProduct:
        return SideProduct(
            ternary_code(upper, swapped=swapped) % modulus,
            pow(3, len(upper), modulus),
            ternary_code(lower, swapped=swapped) % modulus,
            pow(3, len(lower), modulus),
        )

    return (
        role(upper_b, "110"),
        role(upper_b, "0"),
        role(upper_c, lower_rule_c),
        role(upper_c, "0"),
    )


def exact_role_generators(
    beta: int, body: str, *, swapped: bool = False
) -> tuple[SideProduct, ...]:
    upper_b = tag_code(beta, "b")
    upper_c = tag_code(beta, "c")
    lower_rule_c = "1" + "".join(tag_code(beta, letter) for letter in body) + "10"

    def role(upper: str, lower: str) -> SideProduct:
        return SideProduct(
            ternary_code(upper, swapped=swapped),
            3 ** len(upper),
            ternary_code(lower, swapped=swapped),
            3 ** len(lower),
        )

    return (
        role(upper_b, "110"),
        role(upper_b, "0"),
        role(upper_c, lower_rule_c),
        role(upper_c, "0"),
    )


def side_semigroup(
    beta: int, body: str, modulus: int, *, swapped: bool = False
) -> frozenset[SideProduct]:
    generators = role_generators(beta, body, modulus, swapped=swapped)
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
    products: frozenset[SideProduct],
    beta: int,
    modulus: int,
    *,
    swapped: bool = False,
) -> frozenset[Transfer] | None:
    constants = setter_constants(beta, swapped=swapped)
    marker_value = constants.marker % modulus
    marker_scale = constants.scale % modulus
    setter_head = constants.head % modulus
    setter_tail = constants.tail % modulus
    if setter_tail == 0:
        return None
    coefficient = -setter_head * pow(setter_tail, -1, modulus) % modulus
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
class BidirectionalOrbitSearch:
    collision: OrbitCollision | None
    forward_depths: tuple[int, ...]
    backward_depths: tuple[int, ...]


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


@dataclass(frozen=True, slots=True)
class BoundaryShellHit:
    word: tuple[int, ...]
    normalized_discrepancy: int


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


def free_monoid_excludes_factor(generators: tuple[str, ...], factor: str) -> bool:
    """Decide whether every generator concatenation avoids ``factor``."""

    reachable = {0}
    queue = deque(reachable)
    while queue:
        matched = queue.popleft()
        for generator in generators:
            successor = matched
            for symbol in generator:
                candidate = factor[:successor] + symbol
                successor = max(
                    length
                    for length in range(min(len(factor), len(candidate)) + 1)
                    if candidate.endswith(factor[:length])
                )
                if successor == len(factor):
                    return False
            if successor not in reachable:
                reachable.add(successor)
                queue.append(successor)
    return True


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
    beta: int,
    body: str,
    word: tuple[int, ...],
    *,
    swapped: bool = False,
) -> tuple[int, int]:
    """Return the boundary-one resonance gap and its 3-adic unit."""

    roles = role_words(beta, body)
    discrepancy = reverse_discrepancy(beta, body, word)
    upper = "".join(roles[role][0] for role in word)
    lower = "".join(roles[role][1] for role in word)
    difference = ternary_code(
        upper + "1" + "0" * beta,
        swapped=swapped,
    ) - ternary_code(lower, swapped=swapped)
    divisor = 3**discrepancy.common_suffix
    quotient, remainder = divmod(difference, divisor)
    assert remainder == 0
    return len(upper) - discrepancy.common_suffix, quotient


def find_swapped_beta_shell_hit(
    beta: int,
    body: str,
    max_role_length: int,
) -> BoundaryShellHit | None:
    """Find a distinguished-boundary discrepancy able to hit swapped ``D_c``."""

    target = 2 * setter_constants(beta, swapped=True).marker
    roles = range(len(role_words(beta, body)))
    layer = [(role,) for role in roles]
    for _length in range(1, max_role_length + 1):
        for word in layer:
            gap, discrepancy = normalized_boundary_discrepancy(
                beta,
                body,
                word,
                swapped=True,
            )
            if gap == beta and discrepancy == target:
                return BoundaryShellHit(word, discrepancy)
        layer = [(*word, role) for word in layer for role in roles]
    return None


def find_false_integral_unit_pole(
    beta: int,
    body: str,
    max_role_length: int,
    *,
    swapped: bool = False,
) -> IntegralUnitPole | None:
    """Find a nonterminal valuation-one pole with integral normalized value."""

    constants = setter_constants(beta, swapped=swapped)
    generators = exact_role_generators(beta, body, swapped=swapped)

    def visit(
        product: SideProduct, word: tuple[int, ...], remaining: int
    ) -> IntegralUnitPole | None:
        if len(word) >= 2 and word[-1] in (1, 3):
            punctuated_upper = constants.marker + constants.scale * product.upper_value
            centered_pole = (
                constants.tail * punctuated_upper - constants.head * product.lower_value
            )
            if three_adic_valuation(centered_pole) == 1:
                numerator = -3 * constants.head * constants.marker * product.lower_value
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


def exact_transfer(
    product: SideProduct,
    start: Fraction,
    beta: int,
    *,
    swapped: bool = False,
) -> Fraction | None:
    constants = setter_constants(beta, swapped=swapped)
    denominator = (
        constants.marker
        + constants.scale * product.upper_value
        - product.lower_value * start
    )
    if denominator == 0:
        return None
    return Fraction(constants.head, constants.tail) * (
        1 - Fraction(constants.marker * product.upper_scale, denominator)
    )


def exact_preimage(
    product: SideProduct,
    target: Fraction,
    beta: int,
    *,
    swapped: bool = False,
) -> Fraction | None:
    """Invert one projective transfer on the finite affine chart."""

    constants = setter_constants(beta, swapped=swapped)
    center = Fraction(constants.head, constants.tail)
    if target == center:
        return None
    punctuated_upper = constants.marker + constants.scale * product.upper_value
    return (
        punctuated_upper
        - Fraction(constants.marker * product.upper_scale) * center / (center - target)
    ) / product.lower_value


def exact_pole(product: SideProduct, beta: int, *, swapped: bool = False) -> Fraction:
    constants = setter_constants(beta, swapped=swapped)
    return Fraction(
        constants.marker + constants.scale * product.upper_value,
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


def audit_swapped_digit_setter() -> None:
    beta = 3
    constants = setter_constants(beta, swapped=True)
    assert constants == SetterConstants(27, 53, 81, 134, -25)

    blocks = exact_blocks(beta, "bbcc", 3, swapped=True)
    for product, (length, code) in blocks:
        punctuated_upper = constants.marker + constants.scale * product.upper_value
        centered_pole = (
            constants.tail * punctuated_upper - constants.head * product.lower_value
        )
        assert centered_pole < 0
        assert exact_pole(product, beta, swapped=True) > 0
        expected_shell = beta if length == 1 and code in (1, 3) else 1
        assert three_adic_valuation(centered_pole) == expected_shell
        for start in (Fraction(-3, 5), Fraction(0), Fraction(1), Fraction(7, 4)):
            image = exact_transfer(product, start, beta, swapped=True)
            if image is not None:
                assert exact_preimage(product, image, beta, swapped=True) == start

    for width in range(3, 9):
        values = setter_constants(width, swapped=True)
        power = values.rho
        upper_b = ternary_code(tag_code(width, "b"), swapped=True)
        punctuated_b = values.marker + values.scale * upper_b
        centered_b = values.tail * punctuated_b - 2 * values.head
        assert centered_b == -power * (18 * power**2 - 40 * power + 17)
        required_b = Fraction(
            -power * values.head * values.marker * 2,
            centered_b,
        )
        assert 1 < required_b < 2

        punctuated_c = values.marker + values.scale
        centered_c = values.tail * punctuated_c - 2 * values.head
        assert centered_c == -power * values.head
        assert (
            Fraction(-power * values.head * values.marker * 2, centered_c)
            == 2 * values.marker
        )

        modulus = 9 * power
        discrepancy = power - 1
        target_factor = "01" + "0" * width
        target_residue = (
            discrepancy
            * (power - 2)
            * pow(3 * values.marker - discrepancy, -1, modulus)
            % modulus
        )
        assert target_residue == 8 * power - 1
        assert target_residue == ternary_code(target_factor, swapped=True)
        for body in ("b" * (width - 1), "c" * (width - 1), "bc" * width):
            lower_roles = tuple(lower for _upper, lower in role_words(width, body))
            assert free_monoid_excludes_factor(lower_roles, target_factor)

    assert find_exact_collision(beta, "bbcc", 5, swapped=True) is None
    assert search_exact_orbits(beta, "bbcc", 3, 2, swapped=True) == OrbitSearch(
        None, (95, 7979)
    )
    assert meet_exact_orbits(
        beta,
        "bbcc",
        3,
        6,
        swapped=True,
    ) == BidirectionalOrbitSearch(
        None,
        (2, 95, 7979, 670235),
        (84, 7056, 592704),
    )
    assert (
        find_false_integral_unit_pole(
            beta,
            "bbcc",
            8,
            swapped=True,
        )
        is None
    )
    assert find_swapped_beta_shell_hit(beta, "bbcc", 8) is None


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
    beta: int,
    body: str,
    max_role_length: int,
    *,
    swapped: bool = False,
) -> Collision | None:
    generators = exact_role_generators(beta, body, swapped=swapped)
    poles: dict[Fraction, tuple[int, int]] = {}
    layer = [(SideProduct(0, 1, 0, 1), 0)]
    for length in range(1, max_role_length + 1):
        layer = next_exact_layer(layer, generators)
        for product, code in layer:
            poles.setdefault(
                exact_pole(product, beta, swapped=swapped),
                (length, code),
            )

    layer = [(SideProduct(0, 1, 0, 1), 0)]
    for length in range(1, max_role_length + 1):
        layer = next_exact_layer(layer, generators)
        for product, code in layer:
            for start in (0, 1):
                image = exact_transfer(
                    product,
                    Fraction(start),
                    beta,
                    swapped=swapped,
                )
                if image is not None and image in poles:
                    return Collision(start, (length, code), poles[image], image)
    return None


def exact_blocks(
    beta: int,
    body: str,
    max_role_length: int,
    *,
    swapped: bool = False,
) -> tuple[tuple[SideProduct, tuple[int, int]], ...]:
    generators = exact_role_generators(beta, body, swapped=swapped)
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
    *,
    swapped: bool = False,
) -> OrbitSearch:
    blocks = exact_blocks(beta, body, max_role_length, swapped=swapped)
    constants = setter_constants(beta, swapped=swapped)
    states: dict[Fraction, tuple[int, tuple[tuple[int, int], ...]]] = {
        Fraction(0): (0, ()),
        Fraction(1): (1, ()),
    }
    depths: list[int] = []
    for depth in range(1, max_square_runs + 1):
        successors: dict[Fraction, tuple[int, tuple[tuple[int, int], ...]]] = {}
        for state, (start, path) in states.items():
            for product, word in blocks:
                image = exact_transfer(product, state, beta, swapped=swapped)
                if image is None:
                    punctuated_upper = (
                        constants.marker + constants.scale * product.upper_value
                    )
                    if (
                        depth == 1
                        and start == 1
                        and punctuated_upper == product.lower_value
                    ):
                        continue
                    return OrbitSearch(
                        OrbitCollision(start, (*path, word)),
                        tuple(depths),
                    )
                successors.setdefault(image, (start, (*path, word)))
        states = successors
        depths.append(len(states))
    return OrbitSearch(None, tuple(depths))


def _decode_block_path(
    code: int,
    length: int,
    blocks: tuple[tuple[SideProduct, tuple[int, int]], ...],
) -> tuple[tuple[int, int], ...]:
    radix = len(blocks)
    indices = [0] * length
    for index in range(length - 1, -1, -1):
        code, indices[index] = divmod(code, radix)
    assert code == 0
    return tuple(blocks[index][1] for index in indices)


def meet_exact_orbits(
    beta: int,
    body: str,
    max_role_length: int,
    max_square_runs: int,
    *,
    swapped: bool = False,
) -> BidirectionalOrbitSearch:
    """Find every collision through ``max_square_runs`` by exact bisection.

    A collision of length ``n`` consists of ``n - 1`` finite transfers followed
    by one pole block.  Forward and inverse layers therefore need total depth
    only ``max_square_runs - 1``.
    """

    if max_square_runs < 1:
        raise ValueError("max_square_runs must be positive")
    if max_role_length < 1:
        raise ValueError("max_role_length must be positive")

    blocks = exact_blocks(beta, body, max_role_length, swapped=swapped)
    radix = len(blocks)
    constants = setter_constants(beta, swapped=swapped)
    # The backward tree has one pole seed per block, while the forward tree has
    # only two resets.  Put the unmatched level on the forward side.
    forward_limit = max_square_runs // 2
    backward_limit = max_square_runs - 1 - forward_limit

    # Values encode ``2 * path_code + start`` to avoid one tuple allocation per
    # projective state.  The low bit records reset zero or distinguished
    # boundary one.
    forward_layers: list[dict[Fraction, int]] = [{Fraction(0): 0, Fraction(1): 1}]
    for depth in range(1, forward_limit + 1):
        successors: dict[Fraction, int] = {}
        for state, witness in forward_layers[-1].items():
            start = witness & 1
            path_code = witness >> 1
            for block_index, (product, _word) in enumerate(blocks):
                image = exact_transfer(
                    product,
                    state,
                    beta,
                    swapped=swapped,
                )
                next_code = path_code * radix + block_index
                if image is None:
                    punctuated_upper = (
                        constants.marker + constants.scale * product.upper_value
                    )
                    if (
                        depth == 1
                        and start == 1
                        and punctuated_upper == product.lower_value
                    ):
                        continue
                    return BidirectionalOrbitSearch(
                        OrbitCollision(
                            start,
                            _decode_block_path(next_code, depth, blocks),
                        ),
                        tuple(len(layer) for layer in forward_layers),
                        (),
                    )
                successors.setdefault(image, 2 * next_code + start)
        forward_layers.append(successors)

    # A backward depth-zero path is one pole block.  If several blocks have the
    # same pole, prefer a nonterminal block so direct-boundary exemption cannot
    # hide a false collision.
    backward_seed: dict[Fraction, int] = {}
    for block_index, (product, _word) in enumerate(blocks):
        pole = exact_pole(product, beta, swapped=swapped)
        punctuated_upper = constants.marker + constants.scale * product.upper_value
        terminal = punctuated_upper == product.lower_value
        previous = backward_seed.get(pole)
        if previous is None:
            backward_seed[pole] = block_index
        elif (
            constants.marker + constants.scale * blocks[previous][0].upper_value
            == blocks[previous][0].lower_value
            and not terminal
        ):
            backward_seed[pole] = block_index

    backward_layers: list[dict[Fraction, int]] = [backward_seed]
    radix_power = radix
    for _inverse_depth in range(1, backward_limit + 1):
        predecessors: dict[Fraction, int] = {}
        for target, suffix_code in backward_layers[-1].items():
            for block_index, (product, _word) in enumerate(blocks):
                predecessor = exact_preimage(
                    product,
                    target,
                    beta,
                    swapped=swapped,
                )
                if predecessor is not None:
                    predecessors.setdefault(
                        predecessor,
                        block_index * radix_power + suffix_code,
                    )
        backward_layers.append(predecessors)
        radix_power *= radix

    for total_length in range(1, max_square_runs + 1):
        for forward_depth in range(forward_limit + 1):
            backward_depth = total_length - forward_depth - 1
            if not 0 <= backward_depth <= backward_limit:
                continue
            forward = forward_layers[forward_depth]
            backward = backward_layers[backward_depth]
            common = forward.keys() & backward.keys()
            for state in common:
                witness = forward[state]
                start = witness & 1
                forward_code = witness >> 1
                suffix_code = backward[state]
                if total_length == 1 and start == 1:
                    product = blocks[suffix_code][0]
                    punctuated_upper = (
                        constants.marker + constants.scale * product.upper_value
                    )
                    if punctuated_upper == product.lower_value:
                        continue
                suffix_length = backward_depth + 1
                combined_code = forward_code * radix**suffix_length + suffix_code
                return BidirectionalOrbitSearch(
                    OrbitCollision(
                        start,
                        _decode_block_path(combined_code, total_length, blocks),
                    ),
                    tuple(len(layer) for layer in forward_layers),
                    tuple(len(layer) for layer in backward_layers),
                )

    return BidirectionalOrbitSearch(
        None,
        tuple(len(layer) for layer in forward_layers),
        tuple(len(layer) for layer in backward_layers),
    )


def shadow(
    beta: int,
    body: str,
    modulus: int,
    *,
    swapped: bool = False,
) -> Shadow | None:
    products = side_semigroup(beta, body, modulus, swapped=swapped)
    transfer_set = transfers(products, beta, modulus, swapped=swapped)
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
    parser.add_argument("--meet-square-runs", type=int, default=0)
    parser.add_argument("--search-unit-poles", type=int, default=0)
    parser.add_argument("--search-beta-shell", type=int, default=0)
    parser.add_argument("--swapped-digits", action="store_true")
    parser.add_argument("--audit", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.audit:
        audit_centered_carry()
        audit_swapped_digit_setter()
        assert find_exact_collision(3, "bbcc", 5) is None
        audit_orbits = search_exact_orbits(3, "bbcc", 3, 2)
        assert audit_orbits == OrbitSearch(None, (96, 8064))
        print("bounded exact setter audit:", audit_orbits)
    if args.max_role_length:
        print(
            "exact collision:",
            find_exact_collision(
                args.beta,
                args.body,
                args.max_role_length,
                swapped=args.swapped_digits,
            ),
        )
    if args.max_square_runs:
        print(
            "exact orbit search:",
            search_exact_orbits(
                args.beta,
                args.body,
                args.max_role_length,
                args.max_square_runs,
                swapped=args.swapped_digits,
            ),
        )
    if args.meet_square_runs:
        print(
            "bidirectional exact orbit search:",
            meet_exact_orbits(
                args.beta,
                args.body,
                args.max_role_length,
                args.meet_square_runs,
                swapped=args.swapped_digits,
            ),
        )
    if args.search_unit_poles:
        print(
            "false integral unit pole:",
            find_false_integral_unit_pole(
                args.beta,
                args.body,
                args.search_unit_poles,
                swapped=args.swapped_digits,
            ),
        )
    if args.search_beta_shell:
        print(
            "swapped beta-shell hit:",
            find_swapped_beta_shell_hit(
                args.beta,
                args.body,
                args.search_beta_shell,
            ),
        )
    for prime in args.primes:
        result = shadow(
            args.beta,
            args.body,
            prime,
            swapped=args.swapped_digits,
        )
        print(prime, "singular constants" if result is None else result)


if __name__ == "__main__":
    main()

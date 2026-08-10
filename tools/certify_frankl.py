#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# dependencies = ["python-flint==0.9.0"]
# ///

"""Outward-rounded certificates for the Frankl abundance bound and affine wall.

The analytic reduction leaves two compact bivariate entropy gaps.  This script
certifies those gaps with Arb ball arithmetic.  Two entropy-zero corner squares
of the endpoint family are discharged by the rational estimates checked in
``audit_scalar_lemmas``; every other point is covered by the interval boxes.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
import heapq
import itertools
import sys

# PEP 723 installs python-flint only in the script runtime; standalone ty cannot
# discover that ephemeral environment.
from flint import arb, ctx  # ty: ignore[unresolved-import]


Q = Fraction
Gradient = tuple[arb, arb]
Interval = tuple[Q, Q]
Box = tuple[Interval, Interval]

ctx.prec = 160


@dataclass(frozen=True)
class Parameters:
    target: Q
    dependent_share: Q
    entropy_slack: Q


TARGETS = {
    "19099/50000": Parameters(Q(19099, 50000), Q(7, 200), Q(1, 10_000_000)),
    "76469/200000": Parameters(Q(76469, 200000), Q(7, 200), Q(1, 10_000_000)),
    "38234553336670271/100000000000000000": Parameters(
        Q(38_234_553_336_670_271, 100_000_000_000_000_000),
        Q(356_069_804_374_481, 10_000_000_000_000_000),
        Q(1, 1_000_000_000_000_000_000),
    ),
}


def target_argument(arguments: list[str]) -> tuple[str, Parameters]:
    match arguments:
        case []:
            label = "38234553336670271/100000000000000000"
        case ["--target", label]:
            pass
        case _:
            raise SystemExit("usage: certify_frankl.py [--target TARGET]")
    if label not in TARGETS:
        raise SystemExit(
            f"unsupported target {label!r}; expected one of {tuple(TARGETS)}"
        )
    return label, TARGETS[label]


TARGET_LABEL, PARAMETERS = target_argument(sys.argv[1:])
TARGET_Q = PARAMETERS.target
ALPHA_Q = PARAMETERS.dependent_share
SLACK_Q = PARAMETERS.entropy_slack
CORNER_Q = Q(1, 1000)


def point(value: Q) -> arb:
    return arb(value.numerator) / value.denominator


TARGET = point(TARGET_Q)
ALPHA = point(ALPHA_Q)
SLACK = point(SLACK_Q)
ZERO = arb(0)
HALF = point(Q(1, 2))
QUARTER = point(Q(1, 4))
LOG_TWO = arb(2).log()

AFFINE_WALL_Y_LOWER_Q = Q(6_705_452_614_969_630_276_082_946_160, 10**28)
AFFINE_WALL_Y_UPPER_Q = Q(6_705_452_614_969_630_276_082_946_162, 10**28)
AFFINE_WALL_C_LOWER_Q = Q(38_234_553_336_670_272_114_599_300, 10**26)
AFFINE_WALL_C_UPPER_Q = Q(38_234_553_336_670_272_114_599_301, 10**26)


def ball(lower: Q, upper: Q) -> arb:
    midpoint = (lower + upper) / 2
    radius = (upper - lower) / 2
    exact_radius = arb(radius.numerator) / radius.denominator
    return point(midpoint) + arb(0, exact_radius)


@dataclass(frozen=True)
class Dual:
    value: arb
    gradient: Gradient | None = (ZERO, ZERO)

    @staticmethod
    def variable(value: arb, coordinate: int) -> Dual:
        gradient = [ZERO, ZERO]
        gradient[coordinate] = arb(1)
        return Dual(value, (gradient[0], gradient[1]))

    def __add__(self, other: object) -> Dual:
        right = lift(other)
        if self.gradient is None or right.gradient is None:
            gradient = None
        else:
            gradient = tuple(
                self.gradient[index] + right.gradient[index] for index in range(2)
            )
        return Dual(self.value + right.value, gradient)  # type: ignore[arg-type]

    __radd__ = __add__

    def __neg__(self) -> Dual:
        gradient = (
            None if self.gradient is None else tuple(-entry for entry in self.gradient)
        )
        return Dual(-self.value, gradient)  # type: ignore[arg-type]

    def __sub__(self, other: object) -> Dual:
        return self + (-lift(other))

    def __rsub__(self, other: object) -> Dual:
        return lift(other) - self

    def __mul__(self, other: object) -> Dual:
        right = lift(other)
        if self.gradient is None or right.gradient is None:
            gradient = None
        else:
            gradient = tuple(
                self.gradient[index] * right.value + self.value * right.gradient[index]
                for index in range(2)
            )
        return Dual(self.value * right.value, gradient)  # type: ignore[arg-type]

    __rmul__ = __mul__

    def inverse(self) -> Dual:
        gradient = (
            None
            if self.gradient is None
            else tuple(-entry / (self.value * self.value) for entry in self.gradient)
        )
        return Dual(1 / self.value, gradient)  # type: ignore[arg-type]

    def __truediv__(self, other: object) -> Dual:
        return self * lift(other).inverse()

    def __rtruediv__(self, other: object) -> Dual:
        return lift(other) / self

    def log(self) -> Dual:
        gradient = (
            None
            if self.gradient is None
            else tuple(entry / self.value for entry in self.gradient)
        )
        return Dual(self.value.log(), gradient)  # type: ignore[arg-type]


def lift(value: object) -> Dual:
    if isinstance(value, Dual):
        return value
    if isinstance(value, arb):
        return Dual(value)
    if isinstance(value, Q):
        return Dual(point(value))
    if isinstance(value, int):
        return Dual(arb(value))
    raise TypeError(f"cannot lift {type(value)!r}")


def entropy_value(value: arb) -> arb:
    return -value * value.log() - (1 - value) * (1 - value).log()


def entropy(value: Dual) -> Dual:
    """Enclose binary entropy, including semantic endpoint intervals.

    Every caller proves separately that the true argument lies in ``[0, 1]``.
    Dependency overestimation may make its Arb enclosure protrude slightly past
    an endpoint; monotonicity then gives the endpoint ranges below.
    """

    lower = value.value.lower()
    upper = value.value.upper()
    if lower > 0 and upper < 1:
        return -value * value.log() - (1 - value) * (1 - value).log()

    if lower <= 0:
        if upper >= HALF:
            enclosure = ZERO.union(LOG_TWO)
        elif upper <= 0:
            enclosure = ZERO
        else:
            enclosure = ZERO.union(entropy_value(upper))
    elif upper >= 1:
        if lower <= HALF:
            enclosure = ZERO.union(LOG_TWO)
        elif lower >= 1:
            enclosure = ZERO
        else:
            enclosure = ZERO.union(entropy_value(lower))
    else:
        raise AssertionError("unreachable entropy range")
    return Dual(enclosure, None)


def join(left: Dual, right: Dual) -> Dual:
    return 1 - (1 - left) * (1 - right)


def square_nonnegative(value: Dual) -> Dual:
    if value.value.lower() < 0:
        return value * value
    enclosure = (value.value.lower() ** 2).union(value.value.upper() ** 2)
    gradient = (
        None
        if value.gradient is None
        else tuple(2 * value.value * entry for entry in value.gradient)
    )
    return Dual(enclosure, gradient)  # type: ignore[arg-type]


def self_join(value: Dual) -> Dual:
    return 1 - square_nonnegative(1 - value)


def coupled_entropy(mean: Dual) -> Dual:
    if mean.value.upper() <= QUARTER:
        return entropy(2 * mean)
    if mean.value.lower() >= QUARTER:
        return entropy(lift(Q(1, 2)))
    # Across 1/4, h(2m) encloses h(min(2m, 1/2)); its derivative interval
    # also encloses the zero derivative of the cap.
    return entropy(2 * mean)


def endpoint_gap(variables: tuple[Dual, Dual]) -> Dual:
    mean, endpoint = variables
    weight = 2 * (lift(TARGET) - mean) / (1 + endpoint - 2 * mean)
    low_weight = 1 - weight
    independent = low_weight * low_weight * entropy(self_join(mean))
    independent += weight * low_weight * entropy(join(mean, endpoint))
    independent += weight * weight / 4 * entropy(self_join(endpoint))
    marginal = low_weight * entropy(mean) + weight / 2 * entropy(endpoint)
    coupled = low_weight * coupled_entropy(mean)
    return (1 - ALPHA) * independent + ALPHA * coupled - (1 + SLACK) * marginal


def diagonal_gap(variables: tuple[Dual, Dual], region: int) -> Dual:
    weight, displacement = variables
    if region == 0:
        separation = displacement * (lift(Q(1, 2)) - TARGET) / (1 - weight)
        lower_mean = lift(TARGET) - weight * separation
        upper_mean = lift(TARGET) + displacement * (lift(Q(1, 2)) - TARGET)
    else:
        separation = displacement * TARGET / weight
        lower_mean = lift(TARGET) * (1 - displacement)
        upper_mean = lift(TARGET) + (1 - weight) * separation

    low_weight = 1 - weight
    independent = low_weight * low_weight * entropy(self_join(lower_mean))
    independent += 2 * weight * low_weight * entropy(join(lower_mean, upper_mean))
    independent += weight * weight * entropy(self_join(upper_mean))
    marginal = low_weight * entropy(lower_mean) + weight * entropy(upper_mean)
    coupled = low_weight * coupled_entropy(lower_mean) + weight * coupled_entropy(
        upper_mean
    )
    return (1 - ALPHA) * independent + ALPHA * coupled - (1 + SLACK) * marginal


def variables(box: Box) -> tuple[Dual, Dual]:
    return (
        Dual.variable(ball(box[0][0], box[0][1]), 0),
        Dual.variable(ball(box[1][0], box[1][1]), 1),
    )


def center_variables(box: Box) -> tuple[Dual, Dual]:
    return (
        Dual.variable(point((box[0][0] + box[0][1]) / 2), 0),
        Dual.variable(point((box[1][0] + box[1][1]) / 2), 1),
    )


def freeze_box(intervals: list[list[Q]]) -> Box:
    return (
        (intervals[0][0], intervals[0][1]),
        (intervals[1][0], intervals[1][1]),
    )


@dataclass(frozen=True)
class Assessment:
    certified: bool
    priority: float
    split_costs: tuple[float, float]


def assess(box: Box, objective) -> Assessment:
    face = [list(interval) for interval in box]
    for _ in range(2):
        face_box = freeze_box(face)
        result = objective(variables(face_box))
        if result.gradient is None:
            break
        changed = False
        for index in range(2):
            if face[index][0] == face[index][1]:
                continue
            derivative = result.gradient[index]
            if derivative.lower() > 0:
                face[index][1] = face[index][0]
                changed = True
            elif derivative.upper() < 0:
                face[index][0] = face[index][1]
                changed = True
        if not changed:
            break

    face_box = freeze_box(face)
    result = objective(variables(face_box))
    direct_lower = result.value.lower()
    widths = (
        float(face_box[0][1] - face_box[0][0]),
        float(face_box[1][1] - face_box[1][0]),
    )
    if direct_lower > 0:
        return Assessment(True, float(direct_lower), widths)  # type: ignore[arg-type]
    if result.gradient is None:
        return Assessment(False, float(direct_lower), widths)  # type: ignore[arg-type]

    center = objective(center_variables(face_box))
    error = ZERO
    costs: list[float] = []
    for index, (lower, upper) in enumerate(face_box):
        radius = point((upper - lower) / 2)
        term = result.gradient[index].abs_upper() * radius
        error += term
        costs.append(float(term.upper()))
    taylor_lower = (center.value - error).lower()
    certified = taylor_lower > 0
    priority = max(float(direct_lower), float(taylor_lower))
    return Assessment(certified, priority, (costs[0], costs[1]))  # type: ignore[arg-type]


def split_box(box: Box, coordinate: int) -> tuple[Box, Box]:
    midpoint = (box[coordinate][0] + box[coordinate][1]) / 2
    if coordinate == 0:
        return (
            ((box[0][0], midpoint), box[1]),
            ((midpoint, box[0][1]), box[1]),
        )
    return (
        (box[0], (box[1][0], midpoint)),
        (box[0], (midpoint, box[1][1])),
    )


def encode_box(box: Box) -> bytes:
    entries = (
        f"{value.numerator}/{value.denominator}"
        for interval in box
        for value in interval
    )
    return (",".join(entries) + "\n").encode()


def verify(name: str, initial: list[Box], objective) -> tuple[int, str]:
    queue: list[tuple[float, int, Box, tuple[float, float]]] = []
    serial = itertools.count()
    leaves: list[Box] = []
    count = len(initial)

    for box in initial:
        assessment = assess(box, objective)
        if assessment.certified:
            leaves.append(box)
        else:
            heapq.heappush(
                queue,
                (assessment.priority, next(serial), box, assessment.split_costs),
            )

    while queue:
        if count >= 1_000_000:
            raise RuntimeError(f"{name}: certificate exceeded one million boxes")
        _, _, box, costs = heapq.heappop(queue)
        coordinate = max(range(2), key=costs.__getitem__)
        if costs[coordinate] <= 0:
            coordinate = max(range(2), key=lambda index: box[index][1] - box[index][0])
        for child in split_box(box, coordinate):
            assessment = assess(child, objective)
            if assessment.certified:
                leaves.append(child)
            else:
                heapq.heappush(
                    queue,
                    (
                        assessment.priority,
                        next(serial),
                        child,
                        assessment.split_costs,
                    ),
                )
            count += 1

    digest = hashlib.sha256()
    for leaf in sorted(leaves):
        digest.update(encode_box(leaf))
    certificate_hash = digest.hexdigest()
    print(f"{name}: {count} assessed boxes; {len(leaves)} certified leaves")
    print(f"{name}: sha256 {certificate_hash}")
    return count, certificate_hash


def cells(cuts: list[Q]) -> list[Interval]:
    return list(zip(cuts, cuts[1:]))


def product_boxes(horizontal: list[Interval], vertical: list[Interval]) -> list[Box]:
    return [
        ((left, right), (bottom, top))
        for left, right in horizontal
        for bottom, top in vertical
    ]


def require_positive(name: str, value: arb) -> None:
    if not value.lower() > 0:
        raise AssertionError(f"{name} was not certified positive: {value}")


def audit_affine_wall() -> None:
    """Localize the centered-endpoint obstruction to the affine scheme."""
    lower = point(AFFINE_WALL_Y_LOWER_Q)
    upper = point(AFFINE_WALL_Y_UPPER_Q)
    interval = ball(AFFINE_WALL_Y_LOWER_Q, AFFINE_WALL_Y_UPPER_Q)

    def phi(value: arb) -> arb:
        entropy_y = entropy_value(value)
        entropy_square = entropy_value(value * value)
        return entropy_y * entropy_y - LOG_TWO * (2 * entropy_y - entropy_square)

    entropy_y = entropy_value(interval)
    entropy_square = entropy_value(interval * interval)
    entropy_deriv = ((1 - interval) / interval).log()
    entropy_square_deriv = (
        2 * interval * ((1 - interval * interval) / (interval * interval)).log()
    )
    phi_deriv = 2 * entropy_y * entropy_deriv - LOG_TWO * (
        2 * entropy_deriv - entropy_square_deriv
    )
    complement = 1 - interval * entropy_y / entropy_square

    require_positive("affine-wall lower sign", -phi(lower))
    require_positive("affine-wall upper sign", phi(upper))
    require_positive("affine-wall local monotonicity", phi_deriv - point(Q(27, 100)))
    require_positive(
        "affine-wall lower enclosure",
        complement - point(AFFINE_WALL_C_LOWER_Q),
    )
    require_positive(
        "affine-wall upper enclosure",
        point(AFFINE_WALL_C_UPPER_Q) - complement,
    )
    require_positive(
        "affine-wall gap exceeds 11e-18",
        complement - TARGET - point(Q(11, 10**18)),
    )
    require_positive(
        "affine-wall gap is below 12e-18",
        TARGET + point(Q(12, 10**18)) - complement,
    )
    print(
        "affine wall: certified in "
        "(0.38234553336670272114599300, "
        "0.38234553336670272114599301)"
    )


def audit_scalar_lemmas() -> None:
    one = Q(1)
    complement = one - TARGET_Q
    weighted_denominator = (one + SLACK_Q) / (one - ALPHA_Q)
    require_positive(
        "target beats the golden-ratio constant",
        TARGET - (3 - arb(5).sqrt()) / 2,
    )
    assert 2 * complement - weighted_denominator > 0
    assert complement - weighted_denominator * (1 - complement / 2) < 0
    support_endpoint_derivative = (
        -4 * ((1 + TARGET) / 2).log() - 2 * point(weighted_denominator) * LOG_TWO
    )
    require_positive(
        "support-elimination endpoint derivative", support_endpoint_derivative
    )

    # Elementary logarithm bounds used in the two entropy-zero corner proofs.
    require_positive("log(1000) > 6.9", arb(1000).log() - point(Q(69, 10)))
    require_positive("log(3) < 1.1", point(Q(11, 10)) - arb(3).log())
    require_positive("log(2) < 0.7", point(Q(7, 10)) - LOG_TWO)

    # h(2x-x²), h(2x) >= (9/5)h(x) for 0 <= x <= 1/1000.
    assert Q(199, 1000) * Q(79, 10) - Q(7, 5) - Q(1, 250) > 0

    beta_max = 2 * TARGET_Q
    beta_min = 2 * (TARGET_Q - CORNER_Q) / (1 - CORNER_Q)
    low_min = 1 - beta_max
    low_max = 1 - beta_min
    amplification = Q(9, 5)
    coefficient_mean = low_min * (
        (amplification - 1) * ((1 - ALPHA_Q) * low_min + ALPHA_Q) - SLACK_Q
    )
    coefficient_endpoint = (
        beta_min
        / 2
        * ((1 - ALPHA_Q) * (2 * low_min + amplification * beta_min / 2) - (1 + SLACK_Q))
    )
    entropy_error = (1 - ALPHA_Q) * beta_max * low_max
    assert Q(69, 10) * coefficient_mean > Q(11, 10) * entropy_error
    assert Q(69, 10) * coefficient_endpoint > Q(11, 10) * entropy_error

    # In the corner a <= 1/1000, 1-q <= 1/1000, beta < 2/5 and W > 3/5.
    assert 2 * TARGET_Q / (2 - CORNER_Q) < Q(2, 5)
    assert (1 - ALPHA_Q) * amplification * Q(3, 5) + ALPHA_Q * amplification - (
        1 + SLACK_Q
    ) > 0
    assert (1 - ALPHA_Q) * Q(3, 5) * (1 - CORNER_Q) - (1 + SLACK_Q) / 2 > 0
    print("scalar lemmas: certified")


def main() -> None:
    if TARGET_LABEL == "38234553336670271/100000000000000000":
        audit_affine_wall()
    audit_scalar_lemmas()
    zero = Q(0)
    one = Q(1)
    quarter = Q(1, 4)
    half = Q(1, 2)

    endpoint_boxes = product_boxes(
        cells([zero, CORNER_Q, Q(1, 20), Q(1, 8), quarter, TARGET_Q]),
        cells(
            [
                zero,
                CORNER_Q,
                Q(1, 20),
                Q(1, 8),
                quarter,
                half,
                Q(3, 4),
                one - CORNER_Q,
                one,
            ]
        ),
    )
    endpoint_boxes.remove(((zero, CORNER_Q), (zero, CORNER_Q)))
    endpoint_boxes.remove(((zero, CORNER_Q), (one - CORNER_Q, one)))
    verify("diagonal-endpoint", endpoint_boxes, endpoint_gap)

    split = 2 * TARGET_Q
    lower_region = product_boxes(
        cells([zero, Q(1, 8), quarter, half, split]),
        cells([zero, Q(1, 8), quarter, half, one]),
    )
    verify(
        "diagonal-diagonal-lower", lower_region, lambda value: diagonal_gap(value, 0)
    )
    upper_region = product_boxes(
        cells([split, Q(4, 5), Q(7, 8), one]),
        cells([zero, Q(1, 8), quarter, half, one]),
    )
    verify(
        "diagonal-diagonal-upper", upper_region, lambda value: diagonal_gap(value, 1)
    )
    print(f"Frankl entropy certificate at {TARGET_LABEL}: PASS")


if __name__ == "__main__":
    main()

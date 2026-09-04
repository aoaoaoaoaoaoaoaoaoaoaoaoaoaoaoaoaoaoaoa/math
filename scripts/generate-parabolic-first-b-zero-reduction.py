#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact leading-``b`` outer and tail reductions.

The checker enumerates the cleared outer-root window, compresses its tail rectangles into
maximal middle-wait ranges, and emits ordinary Lean proofs for every exact corner sign.
``--write`` replaces the generated modules; ``--check`` rejects stale output.
"""

from __future__ import annotations

import argparse
import textwrap
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

OUTER_MODULE = Path("MatrixMortality/ParabolicFirstBZeroOuter.lean")
REDUCTION_PREFIX = "ParabolicFirstBZeroReductionCertificate"
DISPATCH_PREFIX = "ParabolicFirstBZeroReductionDispatch"
AGGREGATE_MODULE = Path("MatrixMortality/ParabolicFirstBZeroReduction.lean")
LEAN_FILE_LIMIT = 1500
LEAN_LINE_LIMIT = 100


@dataclass(frozen=True, slots=True)
class Kill:
    sign: int
    kind: str
    gap: int = 0


@dataclass(frozen=True, slots=True)
class Chamber:
    x: int
    y: int
    j: int
    lower: int
    upper: int | None
    threshold: int
    exact: tuple[Kill | None, ...]
    envelope: Kill


@dataclass(frozen=True, slots=True)
class KillRange:
    x: int
    lower: int
    upper: int
    threshold: int
    exact: tuple[Kill, ...]
    envelope: Kill


Segment = KillRange | Chamber


def root_lower_numerator(y: int) -> int:
    return 242 * (
        243 * 243 * (72 * y - 9) + 9 - 8 * y
    ) * 2_408_152_393 - 9_477 * 243 * (58_005_064_872 * y + 37_838_186_340)


def root_lower_denominator(y: int) -> int:
    return (
        242 * (243 * 243 * (72 * y - 9) + 9 - 8 * y) * 11_209_824
        + 9_477 * 243 * 59_048_086_536
    )


def root_upper_numerator(y: int) -> int:
    return 243 * (72 * y - 9) * 25_766_986_436 - 39 * (
        620_717_828_832 * y + 422_435_605_080
    )


def root_upper_denominator(y: int) -> int:
    return 243 * (72 * y - 9) * 119_911_680 + 39 * 631_601_581_536


def outer_window_pairs() -> tuple[tuple[int, int], ...]:
    pairs: list[tuple[int, int]] = []
    for y in range(6, 51_768):
        lower_denominator = root_lower_denominator(y)
        upper_denominator = root_upper_denominator(y)
        assert lower_denominator > 0 and upper_denominator > 0
        lower = -((-root_lower_numerator(y)) // lower_denominator)
        upper = (root_upper_numerator(y) - 1) // upper_denominator
        pairs.extend((x, y) for x in range(max(0, lower), upper + 1))
    assert len(pairs) == 3_243
    return tuple(pairs)


def root_ranges() -> tuple[tuple[int, int, int], ...]:
    by_x: dict[int, list[int]] = {}
    for x, y in outer_window_pairs():
        by_x.setdefault(x, []).append(y)
    ranges = tuple((x, min(ys), max(ys)) for x, ys in by_x.items())
    assert len(ranges) == 40
    assert sum(upper - lower + 1 for _, lower, upper in ranges) == 3_243
    return ranges


def tail_endpoints(
    y: int, j: int, *, envelope: bool
) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    a_lower = Fraction(243 * (72 * y - 9)) + Fraction(9 - 8 * y, 3 ** (j + 5))
    a_upper = Fraction(243 * (72 * y - 9))
    d_lower = Fraction(39) if envelope else Fraction(39) + Fraction(13, 81 * 3**j)
    d_upper = Fraction(39) + Fraction(39, 242 * 3**j)
    return a_lower, a_upper, d_lower, d_upper


def inner_numerator_denominator(
    x: int, y: int, a: Fraction, d: Fraction
) -> tuple[Fraction, Fraction]:
    denominator = a * (25_766_986_436 - 119_911_680 * x) - d * (
        620_717_828_832 * y + 631_601_581_536 * x + 422_435_605_080
    )
    numerator = d * (58_005_064_872 * y + 59_048_086_536 * x + 37_838_186_340) - a * (
        2_408_152_393 - 11_209_824 * x
    )
    return numerator, denominator


def rectangle_data(
    x: int,
    y_lower: int,
    y_upper: int,
    j: int,
    *,
    envelope: bool,
) -> tuple[tuple[Fraction, Fraction], ...]:
    corners: list[tuple[Fraction, Fraction]] = []
    for y in (y_lower, y_upper):
        a_lower, a_upper, d_lower, d_upper = tail_endpoints(y, j, envelope=envelope)
        corners.extend(
            inner_numerator_denominator(x, y, a, d)
            for a in (a_lower, a_upper)
            for d in (d_lower, d_upper)
        )
    return tuple(corners)


def classify_rectangle(
    x: int,
    y_lower: int,
    y_upper: int,
    j: int,
    *,
    envelope: bool,
) -> Kill | None:
    corners = rectangle_data(x, y_lower, y_upper, j, envelope=envelope)
    denominators = tuple(denominator for _, denominator in corners)
    if all(value > 0 for value in denominators):
        sign = 1
    elif all(value < 0 for value in denominators):
        sign = -1
    else:
        return None
    if all(sign * numerator < 0 for numerator, _ in corners):
        return Kill(sign, "negative")
    roots = tuple(numerator / denominator for numerator, denominator in corners)
    lower = min(roots)
    upper = max(roots)
    gap = lower.numerator // lower.denominator
    if gap >= 0 and gap < lower and upper < gap + 1:
        return Kill(sign, "gap", gap)
    return None


def classify_cylinder(
    x: int, y_lower: int, y_upper: int
) -> tuple[int, tuple[Kill, ...], Kill] | None:
    for threshold in range(16):
        envelope = classify_rectangle(x, y_lower, y_upper, threshold, envelope=True)
        if envelope is None:
            continue
        exact = tuple(
            classify_rectangle(x, y_lower, y_upper, j, envelope=False)
            for j in range(threshold)
        )
        if all(kill is not None for kill in exact):
            return (
                threshold,
                tuple(kill for kill in exact if kill is not None),
                envelope,
            )
    return None


def terminal_chambers() -> tuple[Chamber, ...]:
    chambers: list[Chamber] = []
    for x, y in outer_window_pairs():
        if classify_cylinder(x, y, y) is not None:
            continue
        threshold = next(
            j
            for j in range(129)
            if classify_rectangle(x, y, y, j, envelope=True) is not None
        )
        envelope = classify_rectangle(x, y, y, threshold, envelope=True)
        assert envelope is not None
        exact = tuple(
            classify_rectangle(x, y, y, j, envelope=False) for j in range(threshold)
        )
        unresolved = [j for j, kill in enumerate(exact) if kill is None]
        assert len(unresolved) == 1
        j = unresolved[0]
        corners = rectangle_data(x, y, y, j, envelope=False)
        denominators = tuple(denominator for _, denominator in corners)
        if all(value > 0 for value in denominators) or all(
            value < 0 for value in denominators
        ):
            roots = tuple(numerator / denominator for numerator, denominator in corners)
            lower_root = min(roots)
            upper_root = max(roots)
            lower = max(0, -((-lower_root.numerator) // lower_root.denominator))
            upper = upper_root.numerator // upper_root.denominator
            assert lower <= upper
        else:
            lower, upper = 0, None
        chambers.append(Chamber(x, y, j, lower, upper, threshold, exact, envelope))
    assert len(chambers) == 146
    assert sum(chamber.upper is None for chamber in chambers) == 11
    return tuple(chambers)


def reduction_segments(chambers: tuple[Chamber, ...]) -> dict[int, tuple[Segment, ...]]:
    chamber_by_pair = {(chamber.x, chamber.y): chamber for chamber in chambers}
    result: dict[int, tuple[Segment, ...]] = {}
    for x, lower, upper in root_ranges():
        segments: list[Segment] = []
        y = lower
        while y <= upper:
            chamber = chamber_by_pair.get((x, y))
            if chamber is not None:
                segments.append(chamber)
                y += 1
                continue
            search_lower, search_upper = y, upper
            best: tuple[int, tuple[int, tuple[Kill, ...], Kill]] | None = None
            while search_lower <= search_upper:
                middle = (search_lower + search_upper) // 2
                if any((x, value) in chamber_by_pair for value in range(y, middle + 1)):
                    search_upper = middle - 1
                    continue
                certificate = classify_cylinder(x, y, middle)
                if certificate is None:
                    search_upper = middle - 1
                else:
                    best = middle, certificate
                    search_lower = middle + 1
            assert best is not None
            end, (threshold, exact, envelope) = best
            segments.append(KillRange(x, y, end, threshold, exact, envelope))
            y = end + 1
        result[x] = tuple(segments)
    flattened = [segment for segments in result.values() for segment in segments]
    assert len(flattened) == 325
    assert sum(isinstance(segment, KillRange) for segment in flattened) == 179
    assert sum(isinstance(segment, Chamber) for segment in flattened) == 146
    return result


def wrap_lean(source: str) -> str:
    lines: list[str] = []
    for line in source.splitlines():
        if len(line) <= LEAN_LINE_LIMIT:
            lines.append(line)
            continue
        indent = line[: len(line) - len(line.lstrip())]
        wrapped = textwrap.wrap(
            line[len(indent) :],
            width=LEAN_LINE_LIMIT,
            initial_indent=indent,
            subsequent_indent=indent + "  ",
            break_long_words=False,
            break_on_hyphens=False,
        )
        assert wrapped and all(len(part) <= LEAN_LINE_LIMIT for part in wrapped), line
        lines.extend(wrapped)
    return "\n".join(lines) + "\n"


def root_candidate_term(x: int, lower: int, upper: int) -> str:
    if lower == upper:
        return f"(x = {x} ∧ y = {lower})"
    return f"(x = {x} ∧ {lower} ≤ y ∧ y ≤ {upper})"


def render_match(
    name: str, values: tuple[str, ...], default: str, result_type: str
) -> str:
    branches = "\n".join(
        f"  | {index} => {value}" for index, value in enumerate(values)
    )
    return f"def {name} : Nat → {result_type}\n{branches}\n  | _ => {default}"


def render_outer(chambers: tuple[Chamber, ...]) -> str:
    ranges = root_ranges()
    root_terms = " ∨\n    ".join(root_candidate_term(*item) for item in ranges)
    tail_x = render_match(
        "firstBZeroTailX", tuple(str(chamber.x) for chamber in chambers), "0", "Nat"
    )
    tail_y = render_match(
        "firstBZeroTailY", tuple(str(chamber.y) for chamber in chambers), "0", "Nat"
    )
    tail_j = render_match(
        "firstBZeroTailPosition",
        tuple(str(chamber.j) for chamber in chambers),
        "0",
        "Nat",
    )
    tail_lower = render_match(
        "firstBZeroTailLower",
        tuple(str(chamber.lower) for chamber in chambers),
        "0",
        "Nat",
    )
    tail_upper = render_match(
        "firstBZeroTailUpper",
        tuple(
            "none" if chamber.upper is None else f"some {chamber.upper}"
            for chamber in chambers
        ),
        "none",
        "Option Nat",
    )
    source = f"""import MatrixMortality.ParabolicFirstBZeroCore

/-!
# Exact outer-root classification for the leading first-`b` cylinder

This file is generated by `scripts/generate-parabolic-first-b-zero-reduction.py`.
The cleared outer window contains 3,243 integral points in 40 contiguous ranges. Its
tail rectangles retain 146 indexed terminal chambers.
-/

namespace MatrixMortality.ParabolicBlade

/-- The 40 exact integral ranges in the leading-`b` outer-root window. -/
def FirstBZeroRootCandidate (x y : Nat) : Prop :=
  {root_terms}

private theorem firstBZeroRootWindow_x_le
    (x y : Nat) (six_le_y : 6 ≤ y) (window : FirstBLateRootWindow 0 x y) :
    x ≤ 203 := by
  rcases window with ⟨lower, upper⟩
  clear lower
  by_contra x_not_bounded
  have x_large : 204 ≤ x := by omega
  have denominator_positive : 0 < firstBLateRootUpperDenominator 0 y := by
    norm_num [firstBLateRootUpperDenominator, firstBLatePrefixScale]
    omega
  have scaled := Int.mul_le_mul_of_nonneg_right
    (show (204 : ℤ) ≤ x by exact_mod_cast x_large) denominator_positive.le
  norm_num [firstBLateRootUpperNumerator, firstBLateRootUpperDenominator,
    firstBLatePrefixScale] at upper scaled
  omega

private theorem firstBZeroRootWindow_x_ge
    (x y : Nat) (six_le_y : 6 ≤ y) (window : FirstBLateRootWindow 0 x y) :
    81 ≤ x := by
  rcases window with ⟨lower, upper⟩
  by_contra x_not_bounded
  have x_small : x ≤ 80 := by omega
  have denominator_positive : 0 < firstBLateRootLowerDenominator 0 y := by
    norm_num [firstBLateRootLowerDenominator, firstBLatePrefixScale]
    omega
  have scaled := Int.mul_le_mul_of_nonneg_right
    (show (x : ℤ) ≤ 80 by exact_mod_cast x_small) denominator_positive.le
  have y_small : y ≤ 7 := by
    norm_num [firstBLateRootLowerNumerator, firstBLateRootLowerDenominator,
      firstBLatePrefixScale] at lower scaled
    omega
  interval_cases y <;>
    norm_num [firstBLateRootLowerNumerator, firstBLateRootLowerDenominator,
      firstBLateRootUpperNumerator, firstBLateRootUpperDenominator,
      firstBLatePrefixScale] at lower upper <;>
    omega

set_option maxHeartbeats 8000000 in
/-- Exact classification of the integral leading-`b` outer-root window. -/
theorem firstBZeroRootWindow_candidates
    (x y : Nat) (six_le_y : 6 ≤ y) (y_upper : y ≤ 51767)
    (window : FirstBLateRootWindow 0 x y) :
    FirstBZeroRootCandidate x y := by
  have x_lower := firstBZeroRootWindow_x_ge x y six_le_y window
  have x_upper := firstBZeroRootWindow_x_le x y six_le_y window
  rcases window with ⟨lower, upper⟩
  unfold FirstBZeroRootCandidate
  interval_cases x <;>
    norm_num [firstBLateRootLowerNumerator, firstBLateRootLowerDenominator,
      firstBLateRootUpperNumerator, firstBLateRootUpperDenominator,
      firstBLatePrefixScale] at lower upper ⊢ <;>
    omega

/-- Every physical leading-`b` zero above the boundary belongs to the exact outer-root
classification. -/
theorem firstBZeroRootCandidate_of_core_zero
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat) (six_le_y : 6 ≤ y)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 (.b :: tail)).length)
        (ternaryCode (tagEncode 3 (.b :: tail))) x y z = 0) :
    FirstBZeroRootCandidate x y := by
  have window := firstBZeroRootWindow_of_core_zero
    tail contains_b x y z six_le_y core_zero
  have y_upper := bZeroBDefectCOne_y_le_of_first_b 0 tail x y z (by
    simpa only [List.replicate_zero, List.nil_append] using core_zero)
  exact firstBZeroRootWindow_candidates x y six_le_y y_upper window

/-- Indexed outer wait of a retained leading-`b` tail chamber. -/
{tail_x}

/-- Indexed middle wait of a retained leading-`b` tail chamber. -/
{tail_y}

/-- Indexed position of the second body `b` in a retained tail chamber. -/
{tail_j}

/-- Inclusive inner-wait floor of a retained leading-`b` tail chamber. -/
{tail_lower}

/-- Inclusive inner-wait ceiling, absent exactly on the eleven retained rays. -/
{tail_upper}

/-- Membership in one of the 146 exact leading-`b` terminal chambers. -/
def FirstBZeroTailCandidate (x y j z : Nat) : Prop :=
  ∃ i, i < 146 ∧
    x = firstBZeroTailX i ∧
    y = firstBZeroTailY i ∧
    j = firstBZeroTailPosition i ∧
    firstBZeroTailLower i ≤ z ∧
    match firstBZeroTailUpper i with
    | none => True
    | some upper => z ≤ upper

end MatrixMortality.ParabolicBlade
"""
    return wrap_lean(source)


def corner_definitions(kind: str) -> str:
    corner = (
        "FirstBTwoTailNegativeCorners"
        if kind == "negative"
        else "FirstBTwoTailOpenCorners"
    )
    return (
        f"{corner}, firstBLateTailALower, firstBLateTailABase, "
        "firstBTwoTailDLower, firstBTwoTailDUpper, firstBTwoTailZDenominator, "
        "firstBTwoTailZNumerator, firstBLatePrefixScale"
    )


def emit_kill(
    lines: list[str],
    *,
    indent: str,
    x: int,
    y: str,
    position: int,
    tail_position: str,
    envelope: bool,
    kill: Kill,
    variable_y: bool,
) -> None:
    lines.extend(
        (
            f"{indent}let a := firstBLateTailA 0",
            f"{indent}  (List.replicate {tail_position} .c ++ .b :: rest) {y}",
            f"{indent}let d := firstBTwoTailD",
            f"{indent}  (List.replicate {tail_position} .c ++ .b :: rest)",
            f"{indent}change firstBTwoTailZDenominator a d {x} {y} * z =",
            f"{indent}  firstBTwoTailZNumerator a d {x} {y} at root_eq",
        )
    )
    a_lower = f"(firstBLateTailALower 0 {position} {y})"
    a_upper = f"(firstBLateTailABase 0 {y})"
    d_lower = "39" if envelope else f"(firstBTwoTailDLower {position})"
    d_upper = f"(firstBTwoTailDUpper {position})"
    rectangle = (
        "firstBLateTail_envelope_rectangle"
        if envelope
        else "firstBLateTail_exact_rectangle"
    )
    arguments = (
        f"0 {position} j rest {y} position_bound (by omega)"
        if envelope
        else f"0 {position} rest {y} (by omega)"
    )
    lines.extend(
        (
            f"{indent}have rectangle := {rectangle} {arguments}",
            f"{indent}dsimp only at rectangle",
            f"{indent}change FirstBTwoTailRectangle {a_lower} {a_upper} {d_lower}",
            f"{indent}  {d_upper} a d at rectangle",
        )
    )
    sign = str(kill.sign) if kill.sign > 0 else "(-1)"
    if kill.kind == "negative":
        corner_type = (
            f"FirstBTwoTailNegativeCorners {x} {y} {sign} "
            f"{a_lower} {a_upper} {d_lower} {d_upper}"
        )
    else:
        corner_type = (
            f"FirstBTwoTailOpenCorners {x} {y} {kill.gap} {kill.gap + 1} "
            f"{sign} {a_lower} {a_upper} {d_lower} {d_upper}"
        )
    lines.extend(
        (
            f"{indent}have corners : {corner_type} := by",
            f"{indent}  norm_num [{corner_definitions(kill.kind)}]",
        )
    )
    if variable_y:
        lines.append(f"{indent}  (repeat' apply And.intro) <;> nlinarith")
    if kill.kind == "negative":
        lines.append(
            f"{indent}exact firstBTwoTailZ_no_nat_of_negative {x} {y} z {sign}"
        )
    else:
        lines.append(
            f"{indent}exact firstBTwoTailZ_no_nat_of_gap {x} {y} {kill.gap} z {sign}"
        )
    lines.extend(
        (
            f"{indent}  {a_lower} {a_upper} {d_lower} {d_upper}",
            f"{indent}  a d rectangle corners root_eq",
        )
    )


def kill_range_name(item: KillRange) -> str:
    return f"firstBZeroTail_false_{item.x}_{item.lower}_{item.upper}"


def emit_kill_range(item: KillRange) -> str:
    lines = [
        "set_option maxHeartbeats 2000000 in",
        "/-- A generated maximal middle-wait range has no natural tail root. -/",
        f"theorem {kill_range_name(item)}",
        "    (j : Nat) (rest : List TagLetter) (y z : Nat)",
        f"    (y_lower : {item.lower} ≤ y) (y_upper : y ≤ {item.upper})",
        "    (root_eq : firstBTwoTailZDenominator",
        "      (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)",
        f"      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) {item.x} y * z =",
        "        firstBTwoTailZNumerator",
        "          (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)",
        f"          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) {item.x} y) :",
        "    False := by",
        f"  have y_lower_rat : ({item.lower} : ℚ) ≤ y := by exact_mod_cast y_lower",
        f"  have y_upper_rat : (y : ℚ) ≤ {item.upper} := by exact_mod_cast y_upper",
        f"  by_cases position_small : j < {item.threshold}",
        f"  · have position_bound : j ≤ {item.threshold - 1} := by omega",
        "    interval_cases j",
    ]
    for position, kill in enumerate(item.exact):
        start = len(lines)
        emit_kill(
            lines,
            indent="      ",
            x=item.x,
            y="y",
            position=position,
            tail_position=str(position),
            envelope=False,
            kill=kill,
            variable_y=True,
        )
        lines[start] = "    · " + lines[start].strip()
    lines.append(f"  · have position_bound : {item.threshold} ≤ j := by omega")
    emit_kill(
        lines,
        indent="    ",
        x=item.x,
        y="y",
        position=item.threshold,
        tail_position="j",
        envelope=True,
        kill=item.envelope,
        variable_y=True,
    )
    return "\n".join(lines)


def chamber_name(chamber: Chamber) -> str:
    return f"firstBZeroTail_candidate_{chamber.x}_{chamber.y}"


def emit_candidate_witness(lines: list[str], indent: str, index: int) -> None:
    lines.extend(
        (
            f"{indent}refine ⟨{index}, by norm_num, ?_, ?_, ?_, ?_, ?_⟩",
            f"{indent}· norm_num [firstBZeroTailX]",
            f"{indent}· norm_num [firstBZeroTailY]",
            f"{indent}· norm_num [firstBZeroTailPosition]",
            f"{indent}· norm_num [firstBZeroTailLower]",
            f"{indent}· norm_num [firstBZeroTailUpper]",
            f"{indent}  omega",
        )
    )


def emit_survivor(chamber: Chamber, index: int) -> str:
    lines = [
        "set_option maxHeartbeats 2000000 in",
        "/-- One generated outer-root survivor enters its exact indexed terminal chamber. -/",
        f"theorem {chamber_name(chamber)}",
        "    (j : Nat) (rest : List TagLetter) (z : Nat)",
        "    (root_eq : firstBTwoTailZDenominator",
        f"      (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) {chamber.y})",
        (
            f"      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) "
            f"{chamber.x} {chamber.y} * z ="
        ),
        "        firstBTwoTailZNumerator",
        f"          (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) {chamber.y})",
        (
            f"          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) "
            f"{chamber.x} {chamber.y}) :"
        ),
        f"    FirstBZeroTailCandidate {chamber.x} {chamber.y} j z := by",
        f"  by_cases position_small : j < {chamber.threshold}",
        f"  · have position_bound : j ≤ {chamber.threshold - 1} := by omega",
        "    interval_cases j",
    ]
    for position, kill in enumerate(chamber.exact):
        start = len(lines)
        if kill is not None:
            lines.append("      exfalso")
            emit_kill(
                lines,
                indent="      ",
                x=chamber.x,
                y=str(chamber.y),
                position=position,
                tail_position=str(position),
                envelope=False,
                kill=kill,
                variable_y=False,
            )
        else:
            assert position == chamber.j
            if chamber.upper is None:
                emit_candidate_witness(lines, "      ", index)
            else:
                a_lower = f"(firstBLateTailALower 0 {position} {chamber.y})"
                a_upper = f"(firstBLateTailABase 0 {chamber.y})"
                d_lower = f"(firstBTwoTailDLower {position})"
                d_upper = f"(firstBTwoTailDUpper {position})"
                lines.extend(
                    (
                        "      let a := firstBLateTailA 0",
                        f"        (List.replicate {position} .c ++ .b :: rest) {chamber.y}",
                        "      let d := firstBTwoTailD",
                        f"        (List.replicate {position} .c ++ .b :: rest)",
                        (
                            f"      change firstBTwoTailZDenominator a d {chamber.x} "
                            f"{chamber.y} * z ="
                        ),
                        (
                            f"        firstBTwoTailZNumerator a d {chamber.x} "
                            f"{chamber.y} at root_eq"
                        ),
                        "      have rectangle := firstBLateTail_exact_rectangle",
                        f"        0 {position} rest {chamber.y} (by norm_num)",
                        "      dsimp only at rectangle",
                        f"      change FirstBTwoTailRectangle {a_lower} {a_upper}",
                        f"        {d_lower} {d_upper} a d at rectangle",
                    )
                )
                if chamber.lower == 0:
                    assert chamber.upper is not None
                    lines.extend(
                        (
                            "      have corners : FirstBTwoTailUpperCorners",
                            f"          {chamber.x} {chamber.y} {chamber.upper + 1} 1",
                            f"          {a_lower} {a_upper} {d_lower} {d_upper} := by",
                            "        norm_num [FirstBTwoTailUpperCorners,",
                            "          firstBLateTailALower, firstBLateTailABase,",
                            "          firstBTwoTailDLower, firstBTwoTailDUpper,",
                            "          firstBTwoTailZDenominator, firstBTwoTailZNumerator,",
                            "          firstBLatePrefixScale]",
                            "      have z_strict := firstBTwoTailZ_lt_of_upper_corners",
                            f"        {chamber.x} {chamber.y} {chamber.upper + 1} z 1",
                            f"        {a_lower} {a_upper} {d_lower} {d_upper}",
                            "        a d rectangle corners root_eq",
                        )
                    )
                else:
                    assert chamber.upper is not None
                    lines.extend(
                        (
                            "      have corners : FirstBTwoTailOpenCorners",
                            (
                                f"          {chamber.x} {chamber.y} "
                                f"{chamber.lower - 1} {chamber.upper + 1} 1"
                            ),
                            f"          {a_lower} {a_upper} {d_lower} {d_upper} := by",
                            "        norm_num [FirstBTwoTailOpenCorners,",
                            "          firstBLateTailALower, firstBLateTailABase,",
                            "          firstBTwoTailDLower, firstBTwoTailDUpper,",
                            "          firstBTwoTailZDenominator, firstBTwoTailZNumerator,",
                            "          firstBLatePrefixScale]",
                            "      have z_interval := firstBTwoTailZ_mem_open_interval",
                            (
                                f"        {chamber.x} {chamber.y} "
                                f"{chamber.lower - 1} {chamber.upper + 1} z 1"
                            ),
                            f"        {a_lower} {a_upper} {d_lower} {d_upper}",
                            "        a d rectangle corners root_eq",
                        )
                    )
                emit_candidate_witness(lines, "      ", index)
        lines[start] = "    · " + lines[start].strip()
    lines.append(f"  · have position_bound : {chamber.threshold} ≤ j := by omega")
    lines.append("    exfalso")
    emit_kill(
        lines,
        indent="    ",
        x=chamber.x,
        y=str(chamber.y),
        position=chamber.threshold,
        tail_position="j",
        envelope=True,
        kill=chamber.envelope,
        variable_y=False,
    )
    return "\n".join(lines)


def render_shard(
    title: str,
    generator_index: int,
    declarations: tuple[str, ...],
    imported_modules: tuple[Path, ...],
) -> str:
    imports = "\n".join(
        ["import MatrixMortality.ParabolicFirstBZeroOuter"]
        + [f"import MatrixMortality.{module.stem}" for module in imported_modules]
    )
    source = f"""{imports}

/-!
# {title} {generator_index}

This file is generated by `scripts/generate-parabolic-first-b-zero-reduction.py`.
-/

namespace MatrixMortality.ParabolicBlade

{chr(10).join(declarations)}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped


def emit_segment_tree(
    lines: list[str], segments: tuple[Segment, ...], indent: str
) -> None:
    if len(segments) == 1:
        segment = segments[0]
        if isinstance(segment, KillRange):
            lines.append(
                f"{indent}exact False.elim ({kill_range_name(segment)} "
                f"j rest y z (by omega) (by omega) root_eq)"
            )
        else:
            lines.extend(
                (
                    f"{indent}have y_eq : y = {segment.y} := by omega",
                    f"{indent}subst y",
                    f"{indent}exact {chamber_name(segment)} j rest z root_eq",
                )
            )
        return
    middle = len(segments) // 2
    left = segments[:middle]
    right = segments[middle:]
    pivot = left[-1].upper if isinstance(left[-1], KillRange) else left[-1].y
    lines.extend((f"{indent}by_cases y_left : y ≤ {pivot}", f"{indent}·"))
    emit_segment_tree(lines, left, indent + "  ")
    lines.append(f"{indent}·")
    emit_segment_tree(lines, right, indent + "  ")


def root_dispatch_name(x: int) -> str:
    return f"firstBZeroTailCandidate_of_outer_{x}"


def emit_root_dispatch(
    x: int, lower: int, upper: int, segments: tuple[Segment, ...]
) -> str:
    lines = [
        "/-- One generated outer-wait fiber contracts to the indexed terminal chamber set. -/",
        f"theorem {root_dispatch_name(x)}",
        "    (j : Nat) (rest : List TagLetter) (y z : Nat)",
        f"    (y_lower : {lower} ≤ y) (y_upper : y ≤ {upper})",
        "    (root_eq : firstBTwoTailZDenominator",
        "      (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)",
        f"      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) {x} y * z =",
        "        firstBTwoTailZNumerator",
        "          (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)",
        f"          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) {x} y) :",
        f"    FirstBZeroTailCandidate {x} y j z := by",
    ]
    emit_segment_tree(lines, segments, "  ")
    return "\n".join(lines)


def render_aggregate(modules: tuple[Path, ...]) -> str:
    imports = "\n".join(f"import MatrixMortality.{module.stem}" for module in modules)
    ranges = root_ranges()
    names = [f"outer{index}" for index in range(len(ranges))]
    lines = [
        "/-- The generated exact rectangle reduction maps every outer-root point to one of",
        "the 146 indexed terminal chambers. -/",
        "theorem firstBZeroTailCandidate_of_root_candidate",
        "    (j : Nat) (rest : List TagLetter) (x y z : Nat)",
        "    (candidate : FirstBZeroRootCandidate x y)",
        "    (root_eq : firstBTwoTailZDenominator",
        "      (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)",
        "      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y * z =",
        "        firstBTwoTailZNumerator",
        "          (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)",
        "          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y) :",
        "    FirstBZeroTailCandidate x y j z := by",
        "  unfold FirstBZeroRootCandidate at candidate",
        f"  rcases candidate with {' | '.join(names)}",
    ]
    for name, (x, lower, upper) in zip(names, ranges, strict=True):
        if lower == upper:
            lines.append(f"  · rcases {name} with ⟨rfl, rfl⟩")
        else:
            lines.append(f"  · rcases {name} with ⟨rfl, y_lower, y_upper⟩")
        if lower == upper:
            lines.append(
                f"    exact {root_dispatch_name(x)} j rest {lower} z "
                "(by norm_num) (by norm_num) root_eq"
            )
        else:
            lines.append(
                f"    exact {root_dispatch_name(x)} j rest y z y_lower y_upper root_eq"
            )
    source = f"""{imports}

/-!
# Exact tail reduction for the leading first-`b` cylinder

The 3,243 outer-root points contract through 179 maximal killed ranges to 146 indexed
terminal chambers. Generated arithmetic is rechecked by the rational rectangle calculus.
-/

namespace MatrixMortality.ParabolicBlade

{chr(10).join(lines)}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped


def generate() -> dict[Path, str]:
    chambers = terminal_chambers()
    segments = reduction_segments(chambers)
    declarations: list[str] = []
    for x_segments in segments.values():
        for segment in x_segments:
            if isinstance(segment, KillRange):
                declarations.append(emit_kill_range(segment))
            else:
                declarations.append(emit_survivor(segment, chambers.index(segment)))
    dispatch_declarations = [
        emit_root_dispatch(x, lower, upper, segments[x])
        for x, lower, upper in root_ranges()
    ]
    def groups_for(items: list[str]) -> list[list[str]]:
        groups: list[list[str]] = [[]]
        line_count = 12
        for declaration in items:
            declaration_lines = len(wrap_lean(declaration).splitlines()) + 2
            if groups[-1] and line_count + declaration_lines > LEAN_FILE_LIMIT - 12:
                groups.append([])
                line_count = 12
            groups[-1].append(declaration)
            line_count += declaration_lines
        return groups

    certificate_groups = groups_for(declarations)
    certificate_modules = tuple(
        Path(f"MatrixMortality/{REDUCTION_PREFIX}{index}.lean")
        for index in range(len(certificate_groups))
    )
    dispatch_groups = groups_for(dispatch_declarations)
    dispatch_modules = tuple(
        Path(f"MatrixMortality/{DISPATCH_PREFIX}{index}.lean")
        for index in range(len(dispatch_groups))
    )
    generated = {OUTER_MODULE: render_outer(chambers)}
    generated.update(
        {
            module: render_shard(
                "Leading-`b` tail reduction certificate shard", index, tuple(group), ()
            )
            for index, (module, group) in enumerate(
                zip(certificate_modules, certificate_groups, strict=True)
            )
        }
    )
    generated.update(
        {
            module: render_shard(
                "Leading-`b` tail reduction dispatch shard",
                index,
                tuple(group),
                certificate_modules,
            )
            for index, (module, group) in enumerate(
                zip(dispatch_modules, dispatch_groups, strict=True)
            )
        }
    )
    generated[AGGREGATE_MODULE] = render_aggregate(dispatch_modules)
    return generated


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = generate()
    if args.check:
        stale = [
            path
            for path, source in generated.items()
            if not path.exists() or path.read_text() != source
        ]
        if stale:
            raise SystemExit(
                "stale generated leading-b reduction modules: "
                + ", ".join(map(str, stale))
            )
        return
    if args.write:
        for path, source in generated.items():
            path.write_text(source)
        return
    print(generated[AGGREGATE_MODULE], end="")


if __name__ == "__main__":
    main()

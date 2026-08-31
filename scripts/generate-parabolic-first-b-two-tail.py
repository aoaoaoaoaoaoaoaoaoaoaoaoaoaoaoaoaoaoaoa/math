#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact Lean tail certificate for the second-first-``b`` chamber.

The default output is the generated region. ``--write`` replaces only the explicit marker
region in ``ParabolicFirstBTwoTail.lean``; ``--check`` fails when that region is stale. The
generator derives every branch sign and integral gap with exact fractions. The emitted Lean
proofs independently recheck every affine-rectangle corner with ``norm_num``.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

Q = Fraction
MODULE = Path("MatrixMortality/ParabolicFirstBTwoTail.lean")
BEGIN = "-- BEGIN GENERATED SECOND-FIRST-B TAIL CERTIFICATE"
END = "-- END GENERATED SECOND-FIRST-B TAIL CERTIFICATE"

CANDIDATE_RANGES = (
    (183, 8, 8),
    (186, 9, 9),
    (199, 18, 18),
    (202, 23, 23),
    (204, 28, 28),
    (206, 36, 36),
    (208, 49, 49),
    (209, 60, 60),
    (210, 77, 78),
    (211, 107, 109),
    (212, 174, 181),
    (213, 465, 520),
)
CANDIDATES = tuple(
    (x, y) for x, lower, upper in CANDIDATE_RANGES for y in range(lower, upper + 1)
)
STABILIZATION = {candidate: 0 for candidate in CANDIDATES} | {
    (183, 8): 1,
    (186, 9): 1,
    (199, 18): 2,
    (202, 23): 1,
    (204, 28): 2,
    (206, 36): 1,
    (208, 49): 1,
    (210, 77): 1,
    (210, 78): 1,
    (211, 107): 1,
    (211, 109): 1,
    (212, 174): 2,
    (212, 175): 1,
    (212, 180): 4,
    (212, 181): 1,
    (213, 465): 4,
    (213, 466): 3,
    (213, 467): 2,
    (213, 468): 2,
    (213, 469): 2,
    (213, 470): 2,
    (213, 471): 1,
    (213, 472): 1,
    (213, 473): 1,
    (213, 474): 1,
    (213, 514): 2,
    (213, 515): 2,
    (213, 516): 1,
    (213, 517): 1,
    (213, 518): 1,
    (213, 519): 1,
    (213, 520): 1,
}


@dataclass(frozen=True, slots=True)
class Branch:
    sign: int
    kind: str
    gap: int | None = None


def q_coefficients(x: int) -> tuple[int, int]:
    return 25_766_986_436 - 119_911_680 * x, 2_408_152_393 - 11_209_824 * x


def j_coefficients(x: int, y: int) -> tuple[int, int]:
    return (
        620_717_828_832 * y + 631_601_581_536 * x + 422_435_605_080,
        58_005_064_872 * y + 59_048_086_536 * x + 37_838_186_340,
    )


def a_upper(y: int) -> Q:
    return Q(2187 * (72 * y - 9))


def a_lower(y: int, j: int) -> Q:
    return a_upper(y) + Q(9 - 8 * y, 3 ** (j + 5))


def density_bounds(j: int, envelope: bool) -> tuple[Q, Q]:
    lower = Q(0) if envelope else Q(13, 81 * 3**j)
    return Q(39) + lower, Q(39) + Q(39, 242 * 3**j)


def root(x: int, y: int, a: Q, d: Q) -> tuple[Q, Q]:
    q_one, q_zero = q_coefficients(x)
    j_one, j_zero = j_coefficients(x, y)
    denominator = a * q_one - d * j_one
    numerator = d * j_zero - a * q_zero
    return numerator / denominator, denominator


def classify(x: int, y: int, j: int, envelope: bool) -> Branch:
    d_zero, d_one = density_bounds(j, envelope)
    corners = tuple(
        root(x, y, a, d) for a in (a_lower(y, j), a_upper(y)) for d in (d_zero, d_one)
    )
    denominators = tuple(denominator for _, denominator in corners)
    if all(value > 0 for value in denominators):
        sign = 1
    else:
        assert all(value < 0 for value in denominators)
        sign = -1
    roots = tuple(value for value, _ in corners)
    lower, upper = min(roots), max(roots)
    if upper < 0:
        return Branch(sign, "negative")
    lower_integer = -((-lower.numerator) // lower.denominator)
    upper_integer = upper.numerator // upper.denominator
    integers = tuple(range(max(0, lower_integer), upper_integer + 1))
    if (x, y, j, envelope) == (213, 465, 2, False):
        assert integers == (38,)
        return Branch(sign, "survivor")
    assert not integers
    gap = lower.numerator // lower.denominator
    assert gap < lower <= upper < gap + 1
    return Branch(sign, "gap", gap)


def endpoints(j: int, exact: bool) -> tuple[str, str, str, str]:
    d_lower = f"(firstBTwoTailDLower {j})" if exact else "39"
    return (
        f"(firstBTwoTailALower {j} Y)",
        "(firstBTwoTailAUpper Y)",
        d_lower,
        f"(firstBTwoTailDUpper {j})",
    )


def emit_branch(
    x: int, y: int, j: int, branch: Branch, exact: bool, indent: str
) -> str:
    a_zero, a_one, d_zero, d_one = (
        value.replace("Y", str(y)) for value in endpoints(j, exact)
    )
    rectangle_source = (
        f"firstBTwoTail_exact_rectangle {j} rest {y} (by omega)"
        if exact
        else f"firstBTwoTail_envelope_rectangle {j} j rest {y} k_le_j (by omega)"
    )
    lines = [
        f"{indent}have rectangle := {rectangle_source}",
        f"{indent}change FirstBTwoTailRectangle",
        f"{indent}  {a_zero} {a_one}",
        f"{indent}  {d_zero} {d_one} a d at rectangle",
    ]
    sign = str(branch.sign) if branch.sign > 0 else "(-1)"
    if branch.kind == "negative":
        lines.extend(
            (
                f"{indent}have corners : FirstBTwoTailNegativeCorners {x} {y} {sign}",
                f"{indent}    {a_zero} {a_one} {d_zero} {d_one} := by",
                f"{indent}  norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,",
                f"{indent}    firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,",
                f"{indent}    firstBTwoTailZDenominator, firstBTwoTailZNumerator]",
                f"{indent}exact (firstBTwoTailZ_no_nat_of_negative {x} {y} z {sign}",
                f"{indent}  {a_zero} {a_one} {d_zero} {d_one} a d rectangle corners root_eq).elim",
            )
        )
    else:
        lower, upper = (
            (37, 39) if branch.kind == "survivor" else (branch.gap, branch.gap + 1)
        )
        assert lower is not None and upper is not None
        lines.extend(
            (
                f"{indent}have corners : FirstBTwoTailOpenCorners {x} {y} {lower} {upper} {sign}",
                f"{indent}    {a_zero} {a_one} {d_zero} {d_one} := by",
                f"{indent}  norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,",
                f"{indent}    firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,",
                f"{indent}    firstBTwoTailZDenominator, firstBTwoTailZNumerator]",
            )
        )
        if branch.kind == "survivor":
            lines.extend(
                (
                    f"{indent}have interval := firstBTwoTailZ_mem_open_interval {x} {y} {lower} {upper}",
                    f"{indent}  z {sign} {a_zero} {a_one} {d_zero} {d_one}",
                    f"{indent}  a d rectangle corners root_eq",
                    f"{indent}exact ⟨rfl, by omega⟩",
                )
            )
        else:
            lines.extend(
                (
                    f"{indent}exact (firstBTwoTailZ_no_nat_of_gap {x} {y} {branch.gap} z {sign}",
                    f"{indent}  {a_zero} {a_one} {d_zero} {d_one} a d rectangle corners root_eq).elim",
                )
            )
    return "\n".join(lines)


def emit_candidate_theorem(x: int, y: int) -> str:
    exceptional = (x, y) == (213, 465)
    conclusion = "j = 2 ∧ z = 38" if exceptional else "False"
    lines = [
        f"private theorem firstBTwoTail_root_{x}_{y}",
        "    (j : Nat) (rest : List TagLetter) (z : Nat)",
        "    (root_eq :",
        "      let tail := List.replicate j .c ++ .b :: rest",
        f"      firstBTwoTailZDenominator (firstBTwoTailA tail {y})",
        f"          (firstBTwoTailD tail) {x} {y} * z =",
        f"        firstBTwoTailZNumerator (firstBTwoTailA tail {y})",
        f"          (firstBTwoTailD tail) {x} {y}) :",
        f"    {conclusion} := by",
        "  let tail := List.replicate j .c ++ .b :: rest",
        f"  let a := firstBTwoTailA tail {y}",
        "  let d := firstBTwoTailD tail",
        f"  change firstBTwoTailZDenominator a d {x} {y} * z =",
        f"    firstBTwoTailZNumerator a d {x} {y} at root_eq",
    ]
    stabilization = STABILIZATION[x, y]
    if stabilization == 0:
        lines.append("  have k_le_j : 0 ≤ j := Nat.zero_le j")
        lines.append(emit_branch(x, y, 0, classify(x, y, 0, True), False, "  "))
    else:
        cases = " ∨ ".join(f"j = {branch_j}" for branch_j in range(stabilization))
        lines.extend(
            (
                f"  have j_cases : {cases} ∨ {stabilization} ≤ j := by omega",
                "  rcases j_cases with "
                + " | ".join("rfl" for _ in range(stabilization))
                + " | k_le_j",
            )
        )
        for branch_j in range(stabilization):
            lines.append(
                "  · "
                + emit_branch(
                    x, y, branch_j, classify(x, y, branch_j, False), True, "    "
                ).lstrip()
            )
        lines.append(
            "  · "
            + emit_branch(
                x,
                y,
                stabilization,
                classify(x, y, stabilization, True),
                False,
                "    ",
            ).lstrip()
        )
    return "\n".join(lines)


def impossible_call(x: int, y: int) -> str:
    return f"exact (firstBTwoTail_root_{x}_{y} j rest z root_eq).elim"


def emit_main_theorem() -> str:
    lines = [
        "/-- A candidate tail root is the explicit `(213, 465, 38)` point on the `ccb` cylinder. -/",
        "theorem firstBTwoTail_root_eq_exception",
        "    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat)",
        "    (candidate : FirstBTwoRootCandidate x y)",
        "    (root_eq :",
        "      firstBTwoTailZDenominator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y * z =",
        "        firstBTwoTailZNumerator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y) :",
        "    x = 213 ∧ y = 465 ∧ z = 38 ∧ ∃ rest, tail = [.c, .c, .b] ++ rest := by",
        "  obtain ⟨j, rest, tail_eq⟩ := firstBTwoTail_first_b_decomposition tail contains_b",
        "  subst tail",
        "  unfold FirstBTwoRootCandidate at candidate",
        "  rcases candidate with c183 | c186 | c199 | c202 | c204 | c206 |",
        "    c208 | c209 | c210 | c211 | c212 | c213",
    ]
    for x, lower, upper in CANDIDATE_RANGES:
        candidate_case = (
            f"rcases c{x} with ⟨rfl, rfl⟩"
            if lower == upper
            else f"rcases c{x} with ⟨rfl, lower, upper⟩"
        )
        lines.append("  · " + candidate_case)
        if lower == upper:
            lines.append("    " + impossible_call(x, lower))
            continue
        lines.append("    interval_cases y")
        for y in range(lower, upper + 1):
            if (x, y) == (213, 465):
                lines.extend(
                    (
                        "    · obtain ⟨j_eq, z_eq⟩ := firstBTwoTail_root_213_465 j rest z root_eq",
                        "      refine ⟨rfl, rfl, z_eq, rest, ?_⟩",
                        "      simp [j_eq]",
                    )
                )
            else:
                lines.append("    · " + impossible_call(x, y))
    return "\n".join(lines)


def generate() -> str:
    assert len(CANDIDATES) == 77
    declarations = [emit_candidate_theorem(x, y) for x, y in CANDIDATES]
    declarations.append(emit_main_theorem())
    return f"{BEGIN}\n\n" + "\n\n".join(declarations) + f"\n\n{END}"


def replace_generated(source: str, generated: str) -> str:
    start = source.index(BEGIN)
    finish = source.index(END, start) + len(END)
    return source[:start] + generated + source[finish:]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = generate()
    if not (args.write or args.check):
        print(generated)
        return
    source = MODULE.read_text()
    expected = replace_generated(source, generated)
    if args.check:
        if source != expected:
            raise SystemExit("generated tail certificate is stale")
        return
    MODULE.write_text(expected)


if __name__ == "__main__":
    main()

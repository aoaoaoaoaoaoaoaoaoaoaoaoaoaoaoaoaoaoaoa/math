#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact Lean tail certificate for the second-first-``b`` chamber.

The default output is the three generated certificate modules. ``--write`` replaces those
modules; ``--check`` fails when any is stale. The generator derives every branch sign and
integral gap with exact fractions. The emitted Lean proofs independently recheck every
affine-rectangle corner with ``norm_num``. Sharding keeps every module within the strict
1,500-line source limit without weakening either style linter.
"""

from __future__ import annotations

import argparse
import textwrap
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

Q = Fraction
BEFORE_MODULE = Path("MatrixMortality/ParabolicFirstBTwoTailBefore.lean")
LOWER_MODULE = Path("MatrixMortality/ParabolicFirstBTwoTailLower.lean")
UPPER_MODULE = Path("MatrixMortality/ParabolicFirstBTwoTailUpper.lean")
BEGIN = "-- BEGIN GENERATED SECOND-FIRST-B TAIL CERTIFICATE"
END = "-- END GENERATED SECOND-FIRST-B TAIL CERTIFICATE"
LEAN_LINE_LIMIT = 100
LEAN_FILE_LIMIT = 1500

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


def emit_before_theorem() -> str:
    lines = [
        "/-- No canonical candidate before outer wait `213` has an integral tail root. -/",
        "theorem firstBTwoTail_root_before_213_ne",
        "    (j : Nat) (rest : List TagLetter) (x y z : Nat)",
        "    (candidate : FirstBTwoRootCandidate x y)",
        "    (x_lt : x < 213)",
        "    (root_eq :",
        "      let tail := List.replicate j .c ++ .b :: rest",
        "      firstBTwoTailZDenominator (firstBTwoTailA tail y)",
        "          (firstBTwoTailD tail) x y * z =",
        "        firstBTwoTailZNumerator (firstBTwoTailA tail y)",
        "          (firstBTwoTailD tail) x y) :",
        "    False := by",
        "  unfold FirstBTwoRootCandidate at candidate",
        "  rcases candidate with c183 | c186 | c199 | c202 | c204 | c206 |",
        "    c208 | c209 | c210 | c211 | c212 | c213",
    ]
    for x, lower, upper in CANDIDATE_RANGES[:-1]:
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
            lines.append("    · " + impossible_call(x, y))
    lines.extend(("  · rcases c213 with ⟨rfl, _, _⟩", "    omega"))
    return "\n".join(lines)


def emit_lower_theorem() -> str:
    lines = [
        "/-- The lower `x = 213` tail range contains only `(y, z, j) = (465, 38, 2)`. -/",
        "theorem firstBTwoTail_root_213_lower_exception",
        "    (j : Nat) (rest : List TagLetter) (y z : Nat)",
        "    (y_lower : 465 ≤ y) (y_upper : y ≤ 492)",
        "    (root_eq :",
        "      let tail := List.replicate j .c ++ .b :: rest",
        "      firstBTwoTailZDenominator (firstBTwoTailA tail y)",
        "          (firstBTwoTailD tail) 213 y * z =",
        "        firstBTwoTailZNumerator (firstBTwoTailA tail y)",
        "          (firstBTwoTailD tail) 213 y) :",
        "    j = 2 ∧ y = 465 ∧ z = 38 := by",
        "  interval_cases y",
    ]
    for y in range(465, 493):
        if y == 465:
            lines.extend(
                (
                    "  · obtain ⟨j_eq, z_eq⟩ := firstBTwoTail_root_213_465 j rest z root_eq",
                    "    exact ⟨j_eq, rfl, z_eq⟩",
                )
            )
        else:
            lines.append("  · " + impossible_call(213, y))
    return "\n".join(lines)


def emit_upper_theorem() -> str:
    lines = [
        "/-- The upper `x = 213` tail range has no integral tail root. -/",
        "theorem firstBTwoTail_root_213_upper_ne",
        "    (j : Nat) (rest : List TagLetter) (y z : Nat)",
        "    (y_lower : 493 ≤ y) (y_upper : y ≤ 520)",
        "    (root_eq :",
        "      let tail := List.replicate j .c ++ .b :: rest",
        "      firstBTwoTailZDenominator (firstBTwoTailA tail y)",
        "          (firstBTwoTailD tail) 213 y * z =",
        "        firstBTwoTailZNumerator (firstBTwoTailA tail y)",
        "          (firstBTwoTailD tail) 213 y) :",
        "    False := by",
        "  interval_cases y",
    ]
    lines.extend("  · " + impossible_call(213, y) for y in range(493, 521))
    return "\n".join(lines)


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
        assert wrapped and all(len(part) <= LEAN_LINE_LIMIT for part in wrapped)
        lines.extend(wrapped)
    return "\n".join(lines)


def generate_module(title: str, declarations: list[str]) -> str:
    generated = f"{BEGIN}\n\n" + "\n\n".join(declarations) + f"\n\n{END}"
    source = f"""import MatrixMortality.ParabolicFirstBTwoTailCore

/-!
# {title}

This exact certificate shard is generated by
`scripts/generate-parabolic-first-b-two-tail.py`.
-/

namespace MatrixMortality.ParabolicBlade

{generated}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped + "\n"


def generate() -> dict[Path, str]:
    assert len(CANDIDATES) == 77
    before_candidates = [(x, y) for x, y in CANDIDATES if x < 213]
    lower_candidates = [(213, y) for y in range(465, 493)]
    upper_candidates = [(213, y) for y in range(493, 521)]
    assert len(before_candidates) + len(lower_candidates) + len(upper_candidates) == 77
    return {
        BEFORE_MODULE: generate_module(
            "Tail roots before outer wait 213",
            [
                *(emit_candidate_theorem(x, y) for x, y in before_candidates),
                emit_before_theorem(),
            ],
        ),
        LOWER_MODULE: generate_module(
            "Lower tail roots at outer wait 213",
            [
                *(emit_candidate_theorem(x, y) for x, y in lower_candidates),
                emit_lower_theorem(),
            ],
        ),
        UPPER_MODULE: generate_module(
            "Upper tail roots at outer wait 213",
            [
                *(emit_candidate_theorem(x, y) for x, y in upper_candidates),
                emit_upper_theorem(),
            ],
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    modules = generate()
    if not (args.write or args.check):
        for path, source in modules.items():
            print(f"-- {path}")
            print(source, end="")
        return
    if args.check:
        stale = [
            path
            for path, source in modules.items()
            if not path.exists() or path.read_text() != source
        ]
        if stale:
            raise SystemExit(
                "stale generated tail certificates: " + ", ".join(map(str, stale))
            )
        return
    for path, source in modules.items():
        path.write_text(source)


if __name__ == "__main__":
    main()

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact Lean tail certificate for the first-``b``-after-one-``c`` chamber.

The default output is the generated certificate modules. ``--write`` replaces those
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
CORE_MODULE = Path("MatrixMortality/ParabolicFirstBOneOuterCertificateCore.lean")
SHARD_MODULES = tuple(
    Path(f"MatrixMortality/ParabolicFirstBOneOuterCertificate{index}.lean")
    for index in range(5)
)
AGGREGATE_MODULE = Path("MatrixMortality/ParabolicFirstBOneOuterCertificate.lean")
BEGIN = "-- BEGIN GENERATED FIRST-B-ONE-OUTER TAIL CERTIFICATE"
END = "-- END GENERATED FIRST-B-ONE-OUTER TAIL CERTIFICATE"
LEAN_LINE_LIMIT = 100
LEAN_FILE_LIMIT = 1500

CANDIDATE_RANGES = (
    (134, 7, 7),
    (146, 9, 9),
    (169, 16, 16),
    (171, 17, 17),
    (180, 23, 23),
    (184, 27, 27),
    (189, 34, 34),
    (192, 40, 40),
    (194, 45, 45),
    (195, 48, 48),
    (198, 60, 60),
    (200, 72, 72),
    (201, 79, 79),
    (202, 88, 89),
    (203, 100, 100),
    (204, 115, 115),
    (205, 134, 135),
    (206, 161, 163),
    (207, 202, 206),
    (208, 270, 276),
    (209, 404, 419),
    (210, 796, 858),
)
CANDIDATES = tuple(
    (x, y) for x, lower, upper in CANDIDATE_RANGES for y in range(lower, upper + 1)
)
SURVIVOR_INTERVALS = {
    (206, 162, 0): (6, 9),
    (207, 202, 2): (0, 2),
    (210, 802, 1): (3, 5),
    (210, 812, 0): (8, 10),
}
RAY = (210, 801, 1)


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
    return Q(729 * (72 * y - 9))


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
    if not envelope and (x, y, j) == RAY:
        return Branch(0, "ray")
    corners = tuple(
        root(x, y, a, d) for a in (a_lower(y, j), a_upper(y)) for d in (d_zero, d_one)
    )
    denominators = tuple(denominator for _, denominator in corners)
    if all(value > 0 for value in denominators):
        sign = 1
    elif all(value < 0 for value in denominators):
        sign = -1
    else:
        return Branch(0, "cross")
    roots = tuple(value for value, _ in corners)
    lower, upper = min(roots), max(roots)
    if upper < 0:
        return Branch(sign, "negative")
    lower_integer = -((-lower.numerator) // lower.denominator)
    upper_integer = upper.numerator // upper.denominator
    integers = tuple(range(max(0, lower_integer), upper_integer + 1))
    survivor_interval = SURVIVOR_INTERVALS.get((x, y, j)) if not envelope else None
    if survivor_interval is not None:
        interval_lower, interval_upper = survivor_interval
        assert integers == tuple(range(interval_lower + 1, interval_upper))
        return Branch(sign, "survivor")
    if integers:
        return Branch(sign, "open")
    gap = lower.numerator // lower.denominator
    assert gap < lower <= upper < gap + 1
    return Branch(sign, "gap", gap)


def stabilization(x: int, y: int) -> int:
    for j in range(9):
        if classify(x, y, j, True).kind in {"gap", "negative"}:
            return j
    raise AssertionError(f"tail envelope did not stabilize for ({x}, {y})")


STABILIZATION = {candidate: stabilization(*candidate) for candidate in CANDIDATES}


def endpoints(j: int, exact: bool) -> tuple[str, str, str, str]:
    d_lower = f"(firstBTwoTailDLower {j})" if exact else "39"
    return (
        f"(firstBOneOuterALower {j} Y)",
        "(firstBOneOuterAUpper Y)",
        d_lower,
        f"(firstBTwoTailDUpper {j})",
    )


def emit_ray_branch(
    a_zero: str, a_one: str, d_zero: str, d_one: str, indent: str
) -> list[str]:
    corner_definitions = (
        "[firstBOneOuterALower, firstBOneOuterAUpper, firstBTwoTailDLower, "
        "firstBTwoTailDUpper]"
    )
    return [
        f"{indent}have numerator_positive :",
        f"{indent}    0 < firstBTwoTailZNumerator a d 210 801 := by",
        f"{indent}  have positive := firstBTwoTail_affine_rectangle_pos",
        f"{indent}    (-54089353) 58899993321372 0",
        f"{indent}    {a_zero} {a_one} {d_zero} {d_one} a d rectangle",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}  have identity : firstBTwoTailZNumerator a d 210 801 =",
        f"{indent}      (-54089353) * a + 58899993321372 * d + 0 := by",
        f"{indent}    norm_num [firstBTwoTailZNumerator]",
        f"{indent}    ring",
        f"{indent}  rw [identity]",
        f"{indent}  exact positive",
        f"{indent}have lower_margin_positive :",
        f"{indent}    0 < firstBTwoTailZNumerator a d 210 801 -",
        f"{indent}      379 * firstBTwoTailZDenominator a d 210 801 := by",
        f"{indent}  have positive := firstBTwoTail_affine_rectangle_pos",
        f"{indent}    (-221971337397) 238925070721086660 0",
        f"{indent}    {a_zero} {a_one} {d_zero} {d_one} a d rectangle",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}    (by norm_num {corner_definitions})",
        f"{indent}  have identity :",
        f"{indent}      firstBTwoTailZNumerator a d 210 801 -",
        f"{indent}          379 * firstBTwoTailZDenominator a d 210 801 =",
        f"{indent}        (-221971337397) * a + 238925070721086660 * d + 0 := by",
        f"{indent}    norm_num [firstBTwoTailZNumerator, firstBTwoTailZDenominator]",
        f"{indent}    ring",
        f"{indent}  rw [identity]",
        f"{indent}  exact positive",
        f"{indent}have product_positive :",
        f"{indent}    0 < firstBTwoTailZDenominator a d 210 801 * (z : ℚ) := by",
        f"{indent}  rw [root_eq]",
        f"{indent}  exact numerator_positive",
        f"{indent}have denominator_positive :",
        f"{indent}    0 < firstBTwoTailZDenominator a d 210 801 := by",
        f"{indent}  rcases mul_pos_iff.mp product_positive with positive | negative",
        f"{indent}  · exact positive.1",
        f"{indent}  · exact (not_lt_of_ge (by positivity : (0 : ℚ) ≤ z) negative.2).elim",
        f"{indent}have factored :",
        f"{indent}    firstBTwoTailZNumerator a d 210 801 -",
        f"{indent}        379 * firstBTwoTailZDenominator a d 210 801 =",
        f"{indent}      firstBTwoTailZDenominator a d 210 801 * ((z : ℚ) - 379) := by",
        f"{indent}  rw [← root_eq]",
        f"{indent}  ring",
        f"{indent}rw [factored] at lower_margin_positive",
        f"{indent}have offset_positive : (0 : ℚ) < z - 379 := by",
        f"{indent}  rcases mul_pos_iff.mp lower_margin_positive with positive | negative",
        f"{indent}  · exact positive.2",
        f"{indent}  · exact (not_lt_of_ge denominator_positive.le negative.1).elim",
        f"{indent}have z_lower : 380 ≤ z := by",
        f"{indent}  have z_strict : 379 < z := by exact_mod_cast (by linarith : (379 : ℚ) < z)",
        f"{indent}  omega",
        f"{indent}unfold FirstBOneOuterCandidate",
        f"{indent}omega",
    ]


def emit_branch(
    x: int, y: int, j: int, branch: Branch, exact: bool, indent: str
) -> str:
    a_zero, a_one, d_zero, d_one = (
        value.replace("Y", str(y)) for value in endpoints(j, exact)
    )
    rectangle_source = (
        f"firstBOneOuter_exact_rectangle {j} rest {y} (by omega)"
        if exact
        else f"firstBOneOuter_envelope_rectangle {j} j rest {y} k_le_j (by omega)"
    )
    lines = [
        f"{indent}have rectangle := {rectangle_source}",
        f"{indent}change FirstBTwoTailRectangle",
        f"{indent}  {a_zero} {a_one}",
        f"{indent}  {d_zero} {d_one} a d at rectangle",
    ]
    if branch.kind == "ray":
        lines.extend(emit_ray_branch(a_zero, a_one, d_zero, d_one, indent))
        return "\n".join(lines)
    sign = str(branch.sign) if branch.sign > 0 else "(-1)"
    if branch.kind == "negative":
        lines.extend(
            (
                f"{indent}have corners : FirstBTwoTailNegativeCorners {x} {y} {sign}",
                f"{indent}    {a_zero} {a_one} {d_zero} {d_one} := by",
                f"{indent}  norm_num [FirstBTwoTailNegativeCorners, firstBOneOuterALower,",
                f"{indent}    firstBOneOuterAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,",
                f"{indent}    firstBTwoTailZDenominator, firstBTwoTailZNumerator]",
                f"{indent}exact (firstBTwoTailZ_no_nat_of_negative {x} {y} z {sign}",
                f"{indent}  {a_zero} {a_one} {d_zero} {d_one} a d rectangle corners root_eq).elim",
            )
        )
    else:
        if branch.kind == "survivor":
            lower, upper = SURVIVOR_INTERVALS[x, y, j]
        else:
            assert branch.gap is not None
            lower, upper = branch.gap, branch.gap + 1
        lines.extend(
            (
                f"{indent}have corners : FirstBTwoTailOpenCorners {x} {y} {lower} {upper} {sign}",
                f"{indent}    {a_zero} {a_one} {d_zero} {d_one} := by",
                f"{indent}  norm_num [FirstBTwoTailOpenCorners, firstBOneOuterALower,",
                f"{indent}    firstBOneOuterAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,",
                f"{indent}    firstBTwoTailZDenominator, firstBTwoTailZNumerator]",
            )
        )
        if branch.kind == "survivor":
            lines.extend(
                (
                    f"{indent}have interval := firstBTwoTailZ_mem_open_interval {x} {y} {lower} {upper}",
                    f"{indent}  z {sign} {a_zero} {a_one} {d_zero} {d_one}",
                    f"{indent}  a d rectangle corners root_eq",
                    f"{indent}unfold FirstBOneOuterCandidate",
                    f"{indent}omega",
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
    lines = [
        f"private theorem firstBOneOuter_root_{x}_{y}",
        "    (j : Nat) (rest : List TagLetter) (z : Nat)",
        "    (root_eq :",
        "      let tail := List.replicate j .c ++ .b :: rest",
        f"      firstBTwoTailZDenominator (firstBOneOuterA tail {y})",
        f"          (firstBOneOuterD tail) {x} {y} * z =",
        f"        firstBTwoTailZNumerator (firstBOneOuterA tail {y})",
        f"          (firstBOneOuterD tail) {x} {y}) :",
        f"    FirstBOneOuterCandidate {x} j {y} z := by",
        "  let tail := List.replicate j .c ++ .b :: rest",
        f"  let a := firstBOneOuterA tail {y}",
        "  let d := firstBOneOuterD tail",
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


SHARD_CANDIDATES = (
    tuple((x, y) for x, y in CANDIDATES if x <= 206),
    tuple((x, y) for x, y in CANDIDATES if 207 <= x <= 209),
    tuple((x, y) for x, y in CANDIDATES if x == 210 and y <= 816),
    tuple((x, y) for x, y in CANDIDATES if x == 210 and 817 <= y <= 837),
    tuple((x, y) for x, y in CANDIDATES if x == 210 and 838 <= y),
)
SHARD_RANGES = (
    "x ≤ 206",
    "207 ≤ x ∧ x ≤ 209",
    "x = 210 ∧ y ≤ 816",
    "x = 210 ∧ 817 ≤ y ∧ y ≤ 837",
    "x = 210 ∧ 838 ≤ y",
)


def candidate_call(x: int, y: int) -> str:
    return f"exact firstBOneOuter_root_{x}_{y} j rest z root_eq"


def emit_shard_dispatch(index: int) -> str:
    shard_candidates = frozenset(SHARD_CANDIDATES[index])
    names = " | ".join(f"c{x}" for x, _, _ in CANDIDATE_RANGES)
    lines = [
        f"/-- Exact tail classification on certificate shard {index}. -/",
        f"theorem firstBOneOuter_candidate_shard_{index}",
        "    (j : Nat) (rest : List TagLetter) (x y z : Nat)",
        "    (candidate : FirstBOneOuterRootCandidate x y)",
        f"    (chamber_range : {SHARD_RANGES[index]})",
        "    (root_eq :",
        "      let tail := List.replicate j .c ++ .b :: rest",
        "      firstBTwoTailZDenominator (firstBOneOuterA tail y)",
        "          (firstBOneOuterD tail) x y * z =",
        "        firstBTwoTailZNumerator (firstBOneOuterA tail y)",
        "          (firstBOneOuterD tail) x y) :",
        "    FirstBOneOuterCandidate x j y z := by",
        "  unfold FirstBOneOuterRootCandidate at candidate",
        f"  rcases candidate with {names}",
    ]
    for x, lower, upper in CANDIDATE_RANGES:
        if lower == upper:
            lines.append(f"  · rcases c{x} with ⟨rfl, rfl⟩")
            lines.append(
                "    "
                + (
                    candidate_call(x, lower)
                    if (x, lower) in shard_candidates
                    else "omega"
                )
            )
            continue
        lines.append(f"  · rcases c{x} with ⟨rfl, y_lower, y_upper⟩")
        matching = [y for y in range(lower, upper + 1) if (x, y) in shard_candidates]
        if not matching:
            lines.append("    omega")
            continue
        lines.append("    interval_cases y")
        for y in range(lower, upper + 1):
            lines.append(
                "    · " + (candidate_call(x, y) if y in matching else "omega")
            )
    return "\n".join(lines)


def emit_aggregate_dispatch() -> str:
    return """/-- The 113 outer-root pairs refine to exactly five integral tail chambers. -/
theorem firstBOneOuterCandidate_of_root_candidate
    (j : Nat) (rest : List TagLetter) (x y z : Nat)
    (candidate : FirstBOneOuterRootCandidate x y)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBOneOuterA tail y)
          (firstBOneOuterD tail) x y * z =
        firstBTwoTailZNumerator (firstBOneOuterA tail y)
          (firstBOneOuterD tail) x y) :
    FirstBOneOuterCandidate x j y z := by
  by_cases x_lower : x ≤ 206
  · exact firstBOneOuter_candidate_shard_0 j rest x y z candidate x_lower root_eq
  by_cases x_middle : x ≤ 209
  · have chamber_range : 207 ≤ x ∧ x ≤ 209 := by omega
    exact firstBOneOuter_candidate_shard_1 j rest x y z candidate chamber_range root_eq
  have x_eq : x = 210 := by
    unfold FirstBOneOuterRootCandidate at candidate
    omega
  by_cases y_lower : y ≤ 816
  · exact firstBOneOuter_candidate_shard_2 j rest x y z candidate ⟨x_eq, y_lower⟩ root_eq
  by_cases y_middle : y ≤ 837
  · have chamber_range : x = 210 ∧ 817 ≤ y ∧ y ≤ 837 := by omega
    exact firstBOneOuter_candidate_shard_3 j rest x y z candidate chamber_range root_eq
  have chamber_range : x = 210 ∧ 838 ≤ y := by omega
  exact firstBOneOuter_candidate_shard_4 j rest x y z candidate chamber_range root_eq"""


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


def generate_module(import_name: str, title: str, declarations: list[str]) -> str:
    generated = f"{BEGIN}\n\n" + "\n\n".join(declarations) + f"\n\n{END}"
    source = f"""import {import_name}

/-!
# {title}

This exact certificate shard is generated by
`scripts/generate-parabolic-first-b-one-outer.py`.
-/

namespace MatrixMortality.ParabolicBlade

{generated}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped + "\n"


def generate_core() -> str:
    return generate_module(
        "MatrixMortality.ParabolicFirstBOneOuterCore",
        "Five tail chambers after the initial cb",
        [
            """/-- The five integral tail chambers left by the exact outer-root certificate. -/
def FirstBOneOuterCandidate (x j y z : Nat) : Prop :=
  (x = 206 ∧ j = 0 ∧ y = 162 ∧ 7 ≤ z ∧ z ≤ 8) ∨
    (x = 207 ∧ j = 2 ∧ y = 202 ∧ z = 1) ∨
    (x = 210 ∧ j = 1 ∧ y = 801 ∧ 380 ≤ z) ∨
    (x = 210 ∧ j = 1 ∧ y = 802 ∧ z = 4) ∨
    (x = 210 ∧ j = 0 ∧ y = 812 ∧ z = 9)"""
        ],
    )


def generate_aggregate() -> str:
    imports = "\n".join(
        f"import {path.with_suffix('').as_posix().replace('/', '.')}"
        for path in SHARD_MODULES
    )
    source = f"""{imports}

/-!
# Exact tail classification after the initial cb

This generated aggregate dispatches the 113 outer-root pairs to five exact certificate
shards.
-/

namespace MatrixMortality.ParabolicBlade

{BEGIN}

{emit_aggregate_dispatch()}

{END}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped + "\n"


def validate_certificate() -> None:
    distribution = {
        j: tuple(STABILIZATION.values()).count(j)
        for j in range(9)
        if j in STABILIZATION.values()
    }
    assert distribution == {0: 34, 1: 51, 2: 14, 3: 7, 4: 4, 5: 2, 8: 1}
    exceptional = {
        (x, y, j): classify(x, y, j, False).kind
        for x, y in CANDIDATES
        for j in range(STABILIZATION[x, y])
        if classify(x, y, j, False).kind not in {"gap", "negative"}
    }
    assert exceptional == {
        (206, 162, 0): "survivor",
        (207, 202, 2): "survivor",
        (210, 801, 1): "ray",
        (210, 802, 1): "survivor",
        (210, 812, 0): "survivor",
    }
    ray_corners = tuple(
        root(210, 801, a, d)
        for a in (a_lower(801, 1), a_upper(801))
        for d in density_bounds(1, False)
    )
    assert {denominator > 0 for _, denominator in ray_corners} == {False, True}
    assert all(value * denominator > 0 for value, denominator in ray_corners)
    assert all(
        value * denominator - 379 * denominator > 0
        for value, denominator in ray_corners
    )


def generate() -> dict[Path, str]:
    assert len(CANDIDATES) == 113
    assert tuple(map(len, SHARD_CANDIDATES)) == (22, 28, 21, 21, 21)
    assert max(STABILIZATION.values()) == 8
    validate_certificate()
    modules = {CORE_MODULE: generate_core()}
    modules.update(
        {
            path: generate_module(
                "MatrixMortality.ParabolicFirstBOneOuterCertificateCore",
                f"Exact initial-cb tail certificate shard {index}",
                [
                    *(emit_candidate_theorem(x, y) for x, y in SHARD_CANDIDATES[index]),
                    emit_shard_dispatch(index),
                ],
            )
            for index, path in enumerate(SHARD_MODULES)
        }
    )
    modules[AGGREGATE_MODULE] = generate_aggregate()
    return modules


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
                "stale generated first-b-one outer certificates: "
                + ", ".join(map(str, stale))
            )
        return
    for path, source in modules.items():
        path.write_text(source)


if __name__ == "__main__":
    main()

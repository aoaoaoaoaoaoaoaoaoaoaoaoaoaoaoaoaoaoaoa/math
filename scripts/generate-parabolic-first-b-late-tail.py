#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact suffix-rectangle certificate for first-`b` positions 3--11."""

from __future__ import annotations

import argparse
import textwrap
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

SHARDS = tuple(
    Path(f"MatrixMortality/ParabolicFirstBLateCertificate{index}.lean")
    for index in range(4)
)
AGGREGATE = Path("MatrixMortality/ParabolicFirstBLateCertificate.lean")
LEAN_LINE_LIMIT = 100

CANDIDATES = (
    (3, 209, 17),
    (3, 210, 21),
    (3, 211, 27),
    (3, 212, 38),
    *((3, 213, y) for y in range(64, 67)),
    *((3, 214, y) for y in range(206, 237)),
    (4, 213, 18),
    *((4, 214, y) for y in range(43, 46)),
    (5, 214, 13),
    (6, 213, 2),
)


@dataclass(frozen=True, slots=True)
class Kill:
    sign: int
    kind: str
    gap: int = 0


def endpoints(k: int, y: int, j: int, envelope: bool) -> tuple[Fraction, ...]:
    r = 243 * 3**k
    a_lower = Fraction(r * (72 * y - 9)) + Fraction(9 - 8 * y, 3 ** (j + 5))
    a_upper = Fraction(r * (72 * y - 9))
    d_lower = Fraction(39) if envelope else Fraction(39) + Fraction(13, 81 * 3**j)
    d_upper = Fraction(39) + Fraction(39, 242 * 3**j)
    return a_lower, a_upper, d_lower, d_upper


def z_fraction(x: int, y: int, a: Fraction, d: Fraction) -> tuple[Fraction, Fraction]:
    denominator = a * (25_766_986_436 - 119_911_680 * x) - d * (
        620_717_828_832 * y + 631_601_581_536 * x + 422_435_605_080
    )
    numerator = d * (58_005_064_872 * y + 59_048_086_536 * x + 37_838_186_340) - a * (
        2_408_152_393 - 11_209_824 * x
    )
    return numerator, denominator


def classify(k: int, x: int, y: int, j: int, envelope: bool) -> Kill | None:
    a_lower, a_upper, d_lower, d_upper = endpoints(k, y, j, envelope)
    corners = tuple(
        z_fraction(x, y, a, d) for a in (a_lower, a_upper) for d in (d_lower, d_upper)
    )
    denominators = tuple(denominator for _, denominator in corners)
    if all(value > 0 for value in denominators):
        sign = 1
    elif all(value < 0 for value in denominators):
        sign = -1
    else:
        return None
    roots = tuple(numerator / denominator for numerator, denominator in corners)
    if max(roots) < 0:
        return Kill(sign, "negative")
    lower = min(roots)
    upper = max(roots)
    gap = lower.numerator // lower.denominator
    if gap >= 0 and gap < lower and upper < gap + 1:
        return Kill(sign, "gap", gap)
    return None


def classify_candidate(k: int, x: int, y: int) -> tuple[int, tuple[Kill, ...], Kill]:
    for threshold in range(16):
        envelope = classify(k, x, y, threshold, True)
        if envelope is None:
            continue
        exact = tuple(classify(k, x, y, j, False) for j in range(threshold))
        if all(kill is not None for kill in exact):
            return (
                threshold,
                tuple(kill for kill in exact if kill is not None),
                envelope,
            )
    raise AssertionError(f"no certificate for {(k, x, y)}")


def definitions(kind: str) -> str:
    corner = (
        "FirstBTwoTailNegativeCorners"
        if kind == "negative"
        else "FirstBTwoTailOpenCorners"
    )
    return ", ".join(
        (
            corner,
            "firstBLateTailALower",
            "firstBLateTailABase",
            "firstBTwoTailDLower",
            "firstBTwoTailDUpper",
            "firstBTwoTailZDenominator",
            "firstBTwoTailZNumerator",
            "firstBLatePrefixScale",
        )
    )


def emit_kill(
    lines: list[str],
    *,
    indent: str,
    k: int,
    x: int,
    y: int,
    position: int,
    envelope: bool,
    kill: Kill,
) -> None:
    tail_position = "j" if envelope else str(position)
    lines.extend(
        (
            f"{indent}let a := firstBLateTailA {k}",
            f"{indent}  (List.replicate {tail_position} .c ++ .b :: rest) {y}",
            f"{indent}let d := firstBTwoTailD",
            f"{indent}  (List.replicate {tail_position} .c ++ .b :: rest)",
            f"{indent}change firstBTwoTailZDenominator a d {x} {y} * z =",
            f"{indent}  firstBTwoTailZNumerator a d {x} {y} at root_eq",
        )
    )
    a_lower = f"(firstBLateTailALower {k} {position} {y})"
    a_upper = f"(firstBLateTailABase {k} {y})"
    d_lower = "39" if envelope else f"(firstBTwoTailDLower {position})"
    d_upper = f"(firstBTwoTailDUpper {position})"
    rectangle = (
        "firstBLateTail_envelope_rectangle"
        if envelope
        else "firstBLateTail_exact_rectangle"
    )
    rectangle_arguments = (
        f"{k} {position} j rest {y} position_bound (by norm_num)"
        if envelope
        else f"{k} {position} rest {y} (by norm_num)"
    )
    lines.extend(
        (
            f"{indent}have rectangle := {rectangle} {rectangle_arguments}",
            f"{indent}dsimp only at rectangle",
            f"{indent}change FirstBTwoTailRectangle {a_lower} {a_upper} {d_lower} {d_upper}",
            f"{indent}  a d at rectangle",
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
            f"FirstBTwoTailOpenCorners {x} {y} {kill.gap} {kill.gap + 1} {sign} "
            f"{a_lower} {a_upper} {d_lower} {d_upper}"
        )
    lines.extend(
        (
            f"{indent}have corners : {corner_type} := by",
            f"{indent}  norm_num [{definitions(kill.kind)}]",
        )
    )
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


def theorem_name(k: int, x: int, y: int) -> str:
    return f"firstBLateTail_false_{k}_{x}_{y}"


def emit_theorem(k: int, x: int, y: int) -> str:
    threshold, exact, envelope = classify_candidate(k, x, y)
    lines = [
        "set_option maxHeartbeats 2000000 in",
        "/-- The complete tail cylinder over one exact outer-root point contains no natural",
        "inner root. -/",
        f"theorem {theorem_name(k, x, y)}",
        "    (j : Nat) (rest : List TagLetter) (z : Nat)",
        "    (root_eq : firstBTwoTailZDenominator",
        f"      (firstBLateTailA {k} (List.replicate j .c ++ .b :: rest) {y})",
        f"      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) {x} {y} * z =",
        "        firstBTwoTailZNumerator",
        f"          (firstBLateTailA {k} (List.replicate j .c ++ .b :: rest) {y})",
        f"          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) {x} {y}) : False := by",
    ]
    if threshold:
        lines.extend(
            (
                f"  by_cases position_small : j < {threshold}",
                "  · have position_bound : j ≤ " + str(threshold - 1) + " := by omega",
                "    interval_cases j",
            )
        )
        for position, kill in enumerate(exact):
            branch_start = len(lines)
            emit_kill(
                lines,
                indent="      ",
                k=k,
                x=x,
                y=y,
                position=position,
                envelope=False,
                kill=kill,
            )
            lines[branch_start] = "    · " + lines[branch_start].strip()
        lines.extend(
            ("  · have position_bound : " + str(threshold) + " ≤ j := by omega",)
        )
        emit_kill(
            lines,
            indent="    ",
            k=k,
            x=x,
            y=y,
            position=threshold,
            envelope=True,
            kill=envelope,
        )
    else:
        lines.append("  have position_bound : 0 ≤ j := Nat.zero_le j")
        emit_kill(
            lines,
            indent="  ",
            k=k,
            x=x,
            y=y,
            position=0,
            envelope=True,
            kill=envelope,
        )
    return "\n".join(lines)


def emit_aggregate() -> str:
    lines = [
        "/-- Every one of the 44 exact outer-root points dies in its complete tail cylinder. -/",
        "theorem firstBLateTail_false_of_candidate",
        "    (k j : Nat) (rest : List TagLetter) (x y z : Nat)",
        "    (candidate : FirstBLateRootCandidate k x y)",
        "    (root_eq : firstBTwoTailZDenominator",
        "      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) y)",
        "      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y * z =",
        "        firstBTwoTailZNumerator",
        "          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) y)",
        "          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y) : False := by",
        "  unfold FirstBLateRootCandidate at candidate",
        "  rcases candidate with c209 | c210 | c211 | c212 | c213 | c214 |",
        "    c418 | c443 | c513 | c602",
    ]
    singletons = (
        ("c209", 3, 209, 17),
        ("c210", 3, 210, 21),
        ("c211", 3, 211, 27),
        ("c212", 3, 212, 38),
    )
    for variable, k, x, y in singletons:
        lines.extend(
            (
                f"  · rcases {variable} with ⟨rfl, rfl, rfl⟩",
                f"    exact {theorem_name(k, x, y)} j rest z root_eq",
            )
        )
    ranges = (
        ("c213", 3, 213, 64, 66),
        ("c214", 3, 214, 206, 236),
    )
    for variable, k, x, lower, upper in ranges:
        lines.extend(
            (
                f"  · rcases {variable} with ⟨rfl, rfl, y_lower, y_upper⟩",
                "    interval_cases y",
            )
        )
        for y in range(lower, upper + 1):
            lines.extend((f"    · exact {theorem_name(k, x, y)} j rest z root_eq",))
    lines.extend(
        (
            "  · rcases c418 with ⟨rfl, rfl, rfl⟩",
            f"    exact {theorem_name(4, 213, 18)} j rest z root_eq",
            "  · rcases c443 with ⟨rfl, rfl, y_lower, y_upper⟩",
            "    interval_cases y",
        )
    )
    for y in range(43, 46):
        lines.append(f"    · exact {theorem_name(4, 214, y)} j rest z root_eq")
    lines.extend(
        (
            "  · rcases c513 with ⟨rfl, rfl, rfl⟩",
            f"    exact {theorem_name(5, 214, 13)} j rest z root_eq",
            "  · rcases c602 with ⟨rfl, rfl, rfl⟩",
            f"    exact {theorem_name(6, 213, 2)} j rest z root_eq",
        )
    )
    return "\n".join(lines)


def render_shard(index: int, candidates: tuple[tuple[int, int, int], ...]) -> str:
    theorems = "\n\n".join(emit_theorem(*candidate) for candidate in candidates)
    source = f"""import MatrixMortality.ParabolicFirstBLateTailCore

/-!
# Later-position suffix certificate shard {index}

This file is generated by `scripts/generate-parabolic-first-b-late-tail.py`.
-/

namespace MatrixMortality.ParabolicBlade

{theorems}

end MatrixMortality.ParabolicBlade
"""
    return wrap_lean(source)


def render_aggregate() -> str:
    imports = "\n".join(
        f"import MatrixMortality.ParabolicFirstBLateCertificate{index}"
        for index in range(4)
    )
    source = f"""{imports}

/-!
# Later-position suffix certificate

The four generated shards partition and recheck the 44 exact outer-root points. This module
exposes their aggregate classifier.
-/

namespace MatrixMortality.ParabolicBlade

{emit_aggregate()}

end MatrixMortality.ParabolicBlade
"""
    return wrap_lean(source)


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
    return "\n".join(lines) + "\n"


def outputs() -> dict[Path, str]:
    assert len(CANDIDATES) == 44
    result = {
        path: render_shard(index, tuple(CANDIDATES[index * 11 : (index + 1) * 11]))
        for index, path in enumerate(SHARDS)
    }
    result[AGGREGATE] = render_aggregate()
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = outputs()
    if args.write:
        for path, source in rendered.items():
            path.write_text(source)
        return
    stale = [
        path
        for path, source in rendered.items()
        if not path.exists() or path.read_text() != source
    ]
    if stale:
        raise SystemExit("stale generated files: " + ", ".join(map(str, stale)))


if __name__ == "__main__":
    main()

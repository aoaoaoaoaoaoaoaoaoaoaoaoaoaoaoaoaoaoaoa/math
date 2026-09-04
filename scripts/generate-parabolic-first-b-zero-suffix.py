#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact terminal suffix certificate for the leading-``b`` cylinder.

The generator proves every affine sign on inclusive inner-wait intervals, constructs the
complete suffix decision trees, and separately proves the eleven semi-infinite rays. Lean
independently rechecks every sign and grammar transition. ``--write`` replaces the generated
modules; ``--check`` rejects stale output.
"""

from __future__ import annotations

import argparse
import textwrap
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

Line = tuple[int, int]

SHARD_PREFIX = "ParabolicFirstBZeroSuffixCertificate"
AGGREGATE_MODULE = Path("MatrixMortality/ParabolicFirstBZeroSuffixCertificate.lean")
LEAN_FILE_LIMIT = 1500
LEAN_LINE_LIMIT = 100

ARITH_DEFS = (
    "hRoot",
    "aRoot",
    "corr",
    "qRoot",
    "jRoot",
)


def add(left: Line, right: Line) -> Line:
    return left[0] + right[0], left[1] + right[1]


def sub(left: Line, right: Line) -> Line:
    return left[0] - right[0], left[1] - right[1]


def scale(factor: int, line: Line) -> Line:
    return factor * line[0], factor * line[1]


def minimum(line: Line, lower: int, upper: int) -> int:
    return min(line[0] * lower + line[1], line[0] * upper + line[1])


def maximum(line: Line, lower: int, upper: int) -> int:
    return max(line[0] * lower + line[1], line[0] * upper + line[1])


def positive(line: Line, lower: int, upper: int) -> bool:
    return minimum(line, lower, upper) > 0


def negative(line: Line, lower: int, upper: int) -> bool:
    return maximum(line, lower, upper) < 0


def nonpositive(line: Line, lower: int, upper: int) -> bool:
    return maximum(line, lower, upper) <= 0


def nonzero(line: Line, lower: int, upper: int) -> bool:
    return positive(line, lower, upper) or negative(line, lower, upper)


def root_lines(x: int, j: int, y: int) -> tuple[Line, Line, Line]:
    q = (
        25_766_986_436 - 119_911_680 * x,
        2_408_152_393 - 11_209_824 * x,
    )
    complement = (
        631_601_581_536 * x + 620_717_828_832 * y + 422_435_605_080,
        59_048_086_536 * x + 58_005_064_872 * y + 37_838_186_340,
    )
    coefficient = scale(243 * (72 * y - 9), q)
    correction = scale(8 * y - 9, q)
    suffix = sub(
        scale(243 * 3**j, sub(coefficient, scale(39, complement))),
        scale(39, complement),
    )
    return suffix, complement, correction


@dataclass(frozen=True, slots=True)
class Chamber:
    x: int
    y: int
    j: int
    lower: int
    upper: int | None


def outer_window_pairs() -> tuple[tuple[int, int], ...]:
    pairs: list[tuple[int, int]] = []
    for y in range(6, 51_768):
        lower_numerator = 242 * (
            243 * 243 * (72 * y - 9) + 9 - 8 * y
        ) * 2_408_152_393 - 9_477 * 243 * (58_005_064_872 * y + 37_838_186_340)
        lower_denominator = (
            242 * (243 * 243 * (72 * y - 9) + 9 - 8 * y) * 11_209_824
            + 9_477 * 243 * 59_048_086_536
        )
        upper_numerator = 243 * (72 * y - 9) * 25_766_986_436 - 39 * (
            620_717_828_832 * y + 422_435_605_080
        )
        upper_denominator = 243 * (72 * y - 9) * 119_911_680 + 39 * 631_601_581_536
        assert lower_denominator > 0 and upper_denominator > 0
        lower = -((-lower_numerator) // lower_denominator)
        upper = (upper_numerator - 1) // upper_denominator
        pairs.extend((x, y) for x in range(max(0, lower), upper + 1))
    assert len(pairs) == 3_243
    return tuple(pairs)


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


def tail_rectangle_data(
    x: int, y: int, j: int, *, envelope: bool
) -> tuple[tuple[Fraction, Fraction], ...]:
    a_lower, a_upper, d_lower, d_upper = tail_endpoints(y, j, envelope=envelope)
    return tuple(
        inner_numerator_denominator(x, y, a, d)
        for a in (a_lower, a_upper)
        for d in (d_lower, d_upper)
    )


def rectangle_killed(x: int, y: int, j: int, *, envelope: bool) -> bool:
    corners = tail_rectangle_data(x, y, j, envelope=envelope)
    denominators = tuple(denominator for _, denominator in corners)
    if not (
        all(value > 0 for value in denominators)
        or all(value < 0 for value in denominators)
    ):
        return False
    roots = tuple(numerator / denominator for numerator, denominator in corners)
    if max(roots) < 0:
        return True
    lower = min(roots)
    upper = max(roots)
    gap = lower.numerator // lower.denominator
    return gap >= 0 and gap < lower and upper < gap + 1


def cylinder_killed(x: int, y: int) -> bool:
    return any(
        rectangle_killed(x, y, threshold, envelope=True)
        and all(rectangle_killed(x, y, j, envelope=False) for j in range(threshold))
        for threshold in range(33)
    )


def terminal_chambers() -> tuple[Chamber, ...]:
    chambers: list[Chamber] = []
    for x, y in outer_window_pairs():
        if cylinder_killed(x, y):
            continue
        threshold = next(
            j for j in range(129) if rectangle_killed(x, y, j, envelope=True)
        )
        unresolved = [
            j for j in range(threshold) if not rectangle_killed(x, y, j, envelope=False)
        ]
        assert len(unresolved) == 1
        j = unresolved[0]
        corners = tail_rectangle_data(x, y, j, envelope=False)
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
            chambers.append(Chamber(x, y, j, lower, upper))
        else:
            chambers.append(Chamber(x, y, j, 0, None))
    assert len(chambers) == 146
    assert sum(chamber.upper is None for chamber in chambers) == 11
    return tuple(chambers)


def gap_index(
    suffix: Line,
    complement: Line,
    correction: Line,
    lower: int,
    upper: int,
) -> int | None:
    for k in range(32):
        low = sub(
            scale(242 * 3 ** (k + 1), suffix),
            add(
                scale(39, complement),
                scale(242 * 3 ** (k + 1), correction),
            ),
        )
        high = sub(scale(81 * 3**k, suffix), scale(13, complement))
        if positive(low, lower, upper) and negative(high, lower, upper):
            return k
    return None


@dataclass(frozen=True, slots=True)
class Tree:
    kind: str
    gap: int | None = None
    b: Tree | None = None
    c: Tree | None = None


def certificate_tree(
    suffix: Line,
    complement: Line,
    correction: Line,
    lower: int,
    upper: int,
    depth: int = 0,
) -> Tree | None:
    gap = gap_index(suffix, complement, correction, lower, upper)
    if gap is not None:
        return Tree("gap", gap=gap)
    if nonpositive(suffix, lower, upper):
        return Tree("nonpositive")
    global_gap = sub(
        scale(242, suffix),
        add(scale(39, complement), scale(242, correction)),
    )
    if positive(global_gap, lower, upper):
        return Tree("global")
    if not nonzero(sub(suffix, correction), lower, upper):
        return None
    if depth >= 12:
        return None
    b_child = certificate_tree(
        sub(scale(243, suffix), scale(39, complement)),
        complement,
        correction,
        lower,
        upper,
        depth + 1,
    )
    c_child = certificate_tree(
        scale(3, suffix),
        complement,
        correction,
        lower,
        upper,
        depth + 1,
    )
    if b_child is None or c_child is None:
        return None
    return Tree("branch", b=b_child, c=c_child)


def ray_positive(line: Line, lower: int) -> bool:
    return line[0] >= 0 and line[0] * lower + line[1] > 0


def ray_negative(line: Line, lower: int) -> bool:
    return line[0] <= 0 and line[0] * lower + line[1] < 0


def ray_nonpositive(line: Line, lower: int) -> bool:
    return line[0] <= 0 and line[0] * lower + line[1] <= 0


def ray_gap_index(
    suffix: Line, complement: Line, correction: Line, lower: int
) -> int | None:
    for k in range(64):
        low = sub(
            scale(242 * 3 ** (k + 1), suffix),
            add(
                scale(39, complement),
                scale(242 * 3 ** (k + 1), correction),
            ),
        )
        high = sub(scale(81 * 3**k, suffix), scale(13, complement))
        if ray_positive(low, lower) and ray_negative(high, lower):
            return k
    return None


def certificate_ray(
    suffix: Line,
    complement: Line,
    correction: Line,
    lower: int,
    depth: int = 0,
) -> Tree | None:
    gap = ray_gap_index(suffix, complement, correction, lower)
    if gap is not None:
        return Tree("gap", gap=gap)
    if ray_nonpositive(suffix, lower):
        return Tree("nonpositive")
    global_gap = sub(
        scale(242, suffix),
        add(scale(39, complement), scale(242, correction)),
    )
    if ray_positive(global_gap, lower):
        return Tree("global")
    difference = sub(suffix, correction)
    if not (ray_positive(difference, lower) or ray_negative(difference, lower)):
        return None
    if depth >= 12:
        return None
    b_child = certificate_ray(
        sub(scale(243, suffix), scale(39, complement)),
        complement,
        correction,
        lower,
        depth + 1,
    )
    c_child = certificate_ray(
        scale(3, suffix), complement, correction, lower, depth + 1
    )
    if b_child is None or c_child is None:
        return None
    return Tree("branch", b=b_child, c=c_child)


def ray_threshold(x: int, j: int, y: int) -> tuple[int, Tree]:
    suffix, complement, correction = root_lines(x, j, y)
    upper = 1
    while certificate_ray(suffix, complement, correction, upper) is None:
        upper *= 2
        assert upper < 10**15
    lower = upper // 2
    while lower + 1 < upper:
        middle = (lower + upper) // 2
        if certificate_ray(suffix, complement, correction, middle) is None:
            lower = middle
        else:
            upper = middle
    tree = certificate_ray(suffix, complement, correction, upper)
    assert tree is not None
    return upper, tree


def node_count(tree: Tree) -> int:
    if tree.kind != "branch":
        return 1
    assert tree.b is not None and tree.c is not None
    return 1 + node_count(tree.b) + node_count(tree.c)


def tree_depth(tree: Tree) -> int:
    if tree.kind != "branch":
        return 0
    assert tree.b is not None and tree.c is not None
    return 1 + max(tree_depth(tree.b), tree_depth(tree.c))


def maximal_intervals(
    x: int, j: int, y: int, lower: int, upper: int
) -> tuple[tuple[int, int, Tree], ...]:
    suffix, complement, correction = root_lines(x, j, y)
    intervals: list[tuple[int, int, Tree]] = []
    start = lower
    while start <= upper:
        search_lower = start
        search_upper = upper
        best: tuple[int, Tree] | None = None
        while search_lower <= search_upper:
            middle = (search_lower + search_upper) // 2
            tree = certificate_tree(suffix, complement, correction, start, middle)
            if tree is None:
                search_upper = middle - 1
            else:
                best = middle, tree
                search_lower = middle + 1
        if best is None:
            raise AssertionError(f"no certificate at {(x, j, y, start)}")
        end, tree = best
        intervals.append((start, end, tree))
        start = end + 1
    return tuple(intervals)


def theorem_name(x: int, j: int, y: int, lower: int, upper: int) -> str:
    return f"firstBZeroSuffix_false_{x}_{j}_{y}_{lower}_{upper}"


def emit_condition(
    output: list[str],
    indent: str,
    definitions: list[str],
    *,
    at_equality: bool,
    bullet: bool = False,
) -> None:
    names = [*reversed(definitions), *ARITH_DEFS]
    suffix = " at equality" if at_equality else ""
    prefix = "· " if bullet else ""
    continuation = "  " if bullet else ""
    output.append(f"{indent}{prefix}norm_num [{', '.join(names)}]{suffix}")
    output.append(f"{indent}{continuation}nlinarith")


def emit_node(
    output: list[str],
    tree: Tree,
    *,
    indent: str,
    body: str,
    core: str,
    suffix_name: str,
    definitions: list[str],
    word: str,
) -> None:
    if tree.kind == "nonpositive":
        output.append(f"{indent}apply killN {body} {suffix_name} J B")
        output.append(f"{indent}  J_positive B_positive")
        emit_condition(output, indent, definitions, at_equality=False, bullet=True)
        output.append(f"{indent}· exact {core}")
        return
    if tree.kind == "global":
        output.append(f"{indent}apply killG {body} {suffix_name} J B")
        output.append(f"{indent}  J_positive B_positive")
        emit_condition(output, indent, definitions, at_equality=False, bullet=True)
        output.append(f"{indent}· exact {core}")
        return
    if tree.kind == "gap":
        assert tree.gap is not None
        output.append(f"{indent}apply killK {tree.gap} {body} {suffix_name} J B")
        output.append(f"{indent}  J_positive B_positive")
        for _ in range(2):
            emit_condition(output, indent, definitions, at_equality=False, bullet=True)
        output.append(f"{indent}· exact {core}")
        return

    assert tree.b is not None and tree.c is not None
    next_depth = len(word) + 1
    tail = f"tail{next_depth}"
    output.append(f"{indent}cases {body} with")
    output.append(f"{indent}| nil =>")
    output.append(f"{indent}    apply kill0 {suffix_name} J B")
    output.append(f"{indent}    · intro equality")
    emit_condition(output, indent + "      ", definitions, at_equality=True)
    output.append(f"{indent}    · exact {core}")
    output.append(f"{indent}| cons letter {tail} =>")
    output.append(f"{indent}    cases letter with")
    for letter, child in (("b", tree.b), ("c", tree.c)):
        child_word = word + letter
        child_suffix = f"H_{child_word}"
        child_core = f"core_{child_word}"
        transition = (
            f"243 * {suffix_name} - 39 * J" if letter == "b" else f"3 * {suffix_name}"
        )
        output.append(f"{indent}    | {letter} =>")
        output.append(f"{indent}        let {child_suffix} : ℤ := {transition}")
        output.append(
            f"{indent}        have {child_core} : SCore {tail} {child_suffix} J B := by"
        )
        output.append(f"{indent}          dsimp [{child_suffix}]")
        output.append(
            f"{indent}          exact step{letter.upper()} "
            f"{tail} {suffix_name} J B {core}"
        )
        emit_node(
            output,
            child,
            indent=indent + "        ",
            body=tail,
            core=child_core,
            suffix_name=child_suffix,
            definitions=[*definitions, child_suffix],
            word=child_word,
        )


def emit_interval_theorem(
    x: int, j: int, y: int, lower: int, upper: int, tree: Tree
) -> str:
    name = theorem_name(x, j, y, lower, upper)
    output = [
        "/-- Kernel-rechecked suffix extinction on one generated inner-wait interval. -/",
        f"theorem {name}",
        f"    (body : List TagLetter) (z : Nat) (z_lower : {lower} ≤ z)",
        f"    (z_upper : z ≤ {upper})",
        "    (core : FirstBOneOuterSuffixCore body",
        f"      (firstBZeroSuffixH {j} {x} {y} z)",
        f"      (firstBOneOuterJ {x} {y} z)",
        f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
        f"  let H_root : ℤ := hRoot {j} {x} {y} z",
        f"  let J : ℤ := jRoot {x} {y} z",
        f"  let B : ℤ := corr {x} {y} z",
        "  change SCore body H_root J B at core",
        f"  have z_lower_int : ({lower} : ℤ) ≤ z := by exact_mod_cast z_lower",
        f"  have z_upper_int : (z : ℤ) ≤ {upper} := by exact_mod_cast z_upper",
        "  have J_positive : (0 : ℤ) < J := by",
        "    dsimp [J]",
        "    unfold jRoot",
        "    positivity",
        "  have B_positive : (0 : ℤ) < B := by",
        "    dsimp [B]",
        "    unfold corr qRoot",
        "    positivity",
    ]
    emit_node(
        output,
        tree,
        indent="  ",
        body="body",
        core="core",
        suffix_name="H_root",
        definitions=["H_root", "J", "B"],
        word="",
    )
    return "\n".join(output)


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


def ray_theorem_name(x: int, j: int, y: int, lower: int) -> str:
    return f"firstBZeroSuffix_false_{x}_{j}_{y}_ray_{lower}"


def emit_ray_theorem(x: int, j: int, y: int, lower: int, tree: Tree) -> str:
    output = [
        "/-- Kernel-rechecked suffix extinction on one generated inner-wait ray. -/",
        f"theorem {ray_theorem_name(x, j, y, lower)}",
        f"    (body : List TagLetter) (z : Nat) (z_lower : {lower} ≤ z)",
        "    (core : FirstBOneOuterSuffixCore body",
        f"      (firstBZeroSuffixH {j} {x} {y} z)",
        f"      (firstBOneOuterJ {x} {y} z)",
        f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
        f"  let H_root : ℤ := hRoot {j} {x} {y} z",
        f"  let J : ℤ := jRoot {x} {y} z",
        f"  let B : ℤ := corr {x} {y} z",
        "  change SCore body H_root J B at core",
        f"  have z_lower_int : ({lower} : ℤ) ≤ z := by exact_mod_cast z_lower",
        "  have J_positive : (0 : ℤ) < J := by",
        "    dsimp [J]",
        "    unfold jRoot",
        "    positivity",
        "  have B_positive : (0 : ℤ) < B := by",
        "    dsimp [B]",
        "    unfold corr qRoot",
        "    positivity",
    ]
    emit_node(
        output,
        tree,
        indent="  ",
        body="body",
        core="core",
        suffix_name="H_root",
        definitions=["H_root", "J", "B"],
        word="",
    )
    return "\n".join(output)


def render_shard(index: int, declarations: tuple[str, ...]) -> str:
    joined = "\n\n".join(declarations)
    source = f"""import MatrixMortality.ParabolicFirstBZeroCore

/-!
# Leading-`b` suffix certificate shard {index}

This file is generated by
`scripts/generate-parabolic-first-b-zero-suffix.py`.
-/

namespace MatrixMortality.ParabolicBlade

private abbrev SCore := FirstBOneOuterSuffixCore
private abbrev killN := firstBOneOuterSuffixCore_false_of_nonpositive
private abbrev killG := firstBOneOuterSuffixCore_false_of_global
private abbrev killK := firstBOneOuterSuffixCore_false_of_gap
private abbrev kill0 := firstBOneOuterSuffixCore_false_of_nil
private abbrev stepB := firstBOneOuterSuffixCore_cons_b
private abbrev stepC := firstBOneOuterSuffixCore_cons_c
private abbrev hRoot := firstBZeroSuffixH
private abbrev aRoot := firstBZeroScaleCoefficient
private abbrev corr := firstBOneOuterCorrection
private abbrev qRoot := firstBOneOuterQ
private abbrev jRoot := firstBOneOuterJ

{joined}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped


def emit_case_dispatch(
    chamber: Chamber,
    intervals: tuple[tuple[int, int, Tree], ...],
    ray: tuple[int, Tree] | None,
) -> str:
    x, y, j = chamber.x, chamber.y, chamber.j
    output = [
        "/-- The generated interval tree extinguishes one complete terminal chamber. -/",
        f"theorem firstBZeroSuffixCore_false_{x}_{j}_{y}",
        "    (body : List TagLetter) (z : Nat)",
    ]
    if chamber.upper is None:
        assert ray is not None
        threshold, _ = ray
        output.extend(
            (
                "    (core : FirstBOneOuterSuffixCore body",
                f"      (firstBZeroSuffixH {j} {x} {y} z)",
                f"      (firstBOneOuterJ {x} {y} z)",
                f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
                f"  by_cases z_small : z < {threshold}",
                f"  · have z_upper : z ≤ {threshold - 1} := by omega",
            )
        )
        finite_indent = "    "
    else:
        assert chamber.upper is not None and ray is None
        output.extend(
            (
                f"    (z_lower : {chamber.lower} ≤ z) (z_upper : z ≤ {chamber.upper})",
                "    (core : FirstBOneOuterSuffixCore body",
                f"      (firstBZeroSuffixH {j} {x} {y} z)",
                f"      (firstBOneOuterJ {x} {y} z)",
                f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
            )
        )
        finite_indent = "  "
    if len(intervals) == 1:
        interval_lower, interval_upper, _ = intervals[0]
        output.append(
            f"{finite_indent}exact {theorem_name(x, j, y, interval_lower, interval_upper)} "
            f"body z {('Nat.zero_le z' if chamber.upper is None else 'z_lower')} z_upper core"
        )
    else:
        alternatives = " ∨ ".join(
            f"({interval_lower} ≤ z ∧ z ≤ {interval_upper})"
            for interval_lower, interval_upper, _ in intervals
        )
        output.append(f"{finite_indent}have interval : {alternatives} := by omega")
        names = [f"range{index}" for index in range(len(intervals))]
        output.append(f"{finite_indent}rcases interval with {' | '.join(names)}")
        for name, (interval_lower, interval_upper, _) in zip(
            names, intervals, strict=True
        ):
            output.append(
                f"{finite_indent}· exact "
                f"{theorem_name(x, j, y, interval_lower, interval_upper)} "
                f"body z {name}.1 {name}.2 core"
            )
    if chamber.upper is None:
        assert ray is not None
        threshold, _ = ray
        output.extend(
            (
                f"  · have z_lower : {threshold} ≤ z := by omega",
                (
                    f"    exact {ray_theorem_name(x, j, y, threshold)} "
                    "body z z_lower core"
                ),
            )
        )
    return "\n".join(output)


def render_aggregate(
    modules: tuple[Path, ...],
    chambers: tuple[Chamber, ...],
    intervals: dict[tuple[int, int, int], tuple[tuple[int, int, Tree], ...]],
    rays: dict[tuple[int, int, int], tuple[int, Tree]],
) -> str:
    imports = "\n".join(
        ["import MatrixMortality.ParabolicFirstBZeroReduction"]
        + [f"import MatrixMortality.{module.stem}" for module in modules]
    )
    declarations = "\n\n".join(
        emit_case_dispatch(
            chamber,
            intervals[chamber.x, chamber.y, chamber.j],
            rays.get((chamber.x, chamber.y, chamber.j)),
        )
        for chamber in chambers
    )
    dispatch = [
        "/-- The generated exact grammar extinguishes every retained leading-`b` tail",
        "chamber. -/",
        "theorem firstBZeroSuffixCore_false_of_candidate",
        "    (body : List TagLetter) (x y j z : Nat)",
        "    (candidate : FirstBZeroTailCandidate x y j z)",
        "    (core : FirstBOneOuterSuffixCore body (firstBZeroSuffixH j x y z)",
        "      (firstBOneOuterJ x y z) (firstBOneOuterCorrection x y z)) : False := by",
        "  unfold FirstBZeroTailCandidate at candidate",
        "  rcases candidate with",
        "    ⟨i, i_lt, x_eq, y_eq, j_eq, z_lower, z_upper⟩",
        "  interval_cases i",
    ]
    for chamber in chambers:
        if chamber.upper is None:
            arguments = "body z core"
        else:
            arguments = "body z z_lower z_upper core"
        dispatch.extend(
            (
                "  · norm_num [firstBZeroTailX, firstBZeroTailY,",
                "      firstBZeroTailPosition, firstBZeroTailLower,",
                "      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper",
                "    subst x",
                "    subst y",
                "    subst j",
                (
                    f"    exact firstBZeroSuffixCore_false_{chamber.x}_"
                    f"{chamber.j}_{chamber.y} {arguments}"
                ),
            )
        )
    source = f"""{imports}

/-!
# Exact terminal suffix certificate for the leading first-`b` cylinder

The 146 retained tail-root chambers close in 1,751 exact suffix-tree nodes of depth at
most ten. Eleven chambers are partitioned into a finite prefix and a semi-infinite ray.
-/

namespace MatrixMortality.ParabolicBlade

{declarations}

{chr(10).join(dispatch)}

end MatrixMortality.ParabolicBlade
"""
    return wrap_lean(source)


def generate() -> dict[Path, str]:
    chambers = terminal_chambers()
    intervals: dict[tuple[int, int, int], tuple[tuple[int, int, Tree], ...]] = {}
    rays: dict[tuple[int, int, int], tuple[int, Tree]] = {}
    flattened: list[tuple[int, int, int, int, int, Tree]] = []
    ray_nodes: list[Tree] = []
    for chamber in chambers:
        key = chamber.x, chamber.y, chamber.j
        if chamber.upper is None:
            threshold, ray_tree = ray_threshold(chamber.x, chamber.j, chamber.y)
            case_intervals = maximal_intervals(
                chamber.x, chamber.j, chamber.y, 0, threshold - 1
            )
            rays[key] = threshold, ray_tree
            ray_nodes.append(ray_tree)
        else:
            case_intervals = maximal_intervals(
                chamber.x,
                chamber.j,
                chamber.y,
                chamber.lower,
                chamber.upper,
            )
        intervals[key] = case_intervals
        flattened.extend(
            (chamber.x, chamber.j, chamber.y, lower, upper, tree)
            for lower, upper, tree in case_intervals
        )
    all_trees = [item[-1] for item in flattened] + ray_nodes
    assert sum(node_count(tree) for tree in all_trees) == 1_751
    assert max(tree_depth(tree) for tree in all_trees) == 10
    declarations = [
        emit_interval_theorem(x, j, y, lower, upper, tree)
        for x, j, y, lower, upper, tree in flattened
    ]
    declarations.extend(
        emit_ray_theorem(x, j, y, threshold, tree)
        for (x, y, j), (threshold, tree) in rays.items()
    )
    groups: list[list[str]] = [[]]
    line_count = 12
    for declaration in declarations:
        declaration_lines = len(wrap_lean(declaration).splitlines()) + 2
        if groups[-1] and line_count + declaration_lines > LEAN_FILE_LIMIT - 12:
            groups.append([])
            line_count = 12
        groups[-1].append(declaration)
        line_count += declaration_lines
    modules = tuple(
        Path(f"MatrixMortality/{SHARD_PREFIX}{index}.lean")
        for index in range(len(groups))
    )
    generated = {
        module: render_shard(index, tuple(group))
        for index, (module, group) in enumerate(zip(modules, groups, strict=True))
    }
    generated[AGGREGATE_MODULE] = render_aggregate(modules, chambers, intervals, rays)
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
                "stale generated leading-b suffix modules: "
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

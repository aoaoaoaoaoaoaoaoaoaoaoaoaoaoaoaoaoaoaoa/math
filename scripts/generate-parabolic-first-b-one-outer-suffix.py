#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact terminal suffix certificate below outer wait 211.

The generator proves every affine sign on inclusive inner-wait intervals, constructs the
complete suffix decision trees, and emits ordinary Lean proofs. Lean independently rechecks
all interval signs and grammar transitions. ``--write`` replaces the generated modules;
``--check`` rejects stale output.
"""

from __future__ import annotations

import argparse
import textwrap
from dataclasses import dataclass
from pathlib import Path

Line = tuple[int, int]

SHARD_MODULES = tuple(
    Path(f"MatrixMortality/ParabolicFirstBOneOuterSuffixCertificate{index}.lean")
    for index in range(2)
)
AGGREGATE_MODULE = Path("MatrixMortality/ParabolicFirstBOneOuterSuffixCertificate.lean")
LEAN_FILE_LIMIT = 1500
LEAN_LINE_LIMIT = 100

CASES = (
    (206, 0, 162, 7, 8),
    (207, 2, 202, 1, 1),
    (210, 1, 802, 4, 4),
    (210, 0, 812, 9, 9),
    (210, 1, 801, 380, 1447),
)

EXPECTED_INTERVALS = {
    (206, 0, 162): ((7, 7), (8, 8)),
    (207, 2, 202): ((1, 1),),
    (210, 1, 802): ((4, 4),),
    (210, 0, 812): ((9, 9),),
    (210, 1, 801): (
        (380, 380),
        (381, 382),
        (383, 389),
        (390, 409),
        (410, 486),
        (487, 487),
        (488, 1121),
        (1122, 1122),
        (1123, 1124),
        (1125, 1130),
        (1131, 1447),
    ),
}

ARITH_DEFS = (
    "firstBOneOuterSuffixH",
    "firstBOneOuterScaleCoefficient",
    "firstBOneOuterCorrection",
    "firstBOneOuterQ",
    "firstBOneOuterJ",
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
    coefficient = scale(729 * (72 * y - 9), q)
    correction = scale(8 * y - 9, q)
    suffix = sub(
        scale(243 * 3**j, sub(coefficient, scale(39, complement))),
        scale(39, complement),
    )
    return suffix, complement, correction


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
    return f"firstBOneOuterSuffix_false_{x}_{j}_{y}_{lower}_{upper}"


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
        output.append(
            f"{indent}apply firstBOneOuterSuffixCore_false_of_nonpositive "
            f"{body} {suffix_name} J B"
        )
        output.append(f"{indent}  J_positive B_positive")
        emit_condition(output, indent, definitions, at_equality=False, bullet=True)
        output.append(f"{indent}· exact {core}")
        return
    if tree.kind == "global":
        output.append(
            f"{indent}apply firstBOneOuterSuffixCore_false_of_global "
            f"{body} {suffix_name} J B"
        )
        output.append(f"{indent}  J_positive B_positive")
        emit_condition(output, indent, definitions, at_equality=False, bullet=True)
        output.append(f"{indent}· exact {core}")
        return
    if tree.kind == "gap":
        assert tree.gap is not None
        output.append(
            f"{indent}apply firstBOneOuterSuffixCore_false_of_gap {tree.gap} "
            f"{body} {suffix_name} J B"
        )
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
    output.append(
        f"{indent}    apply firstBOneOuterSuffixCore_false_of_nil {suffix_name} J B"
    )
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
            f"{indent}        have {child_core} : FirstBOneOuterSuffixCore "
            f"{tail} {child_suffix} J B := by"
        )
        output.append(f"{indent}          dsimp [{child_suffix}]")
        output.append(
            f"{indent}          exact firstBOneOuterSuffixCore_cons_{letter} "
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
        f"      (firstBOneOuterSuffixH {j} {x} {y} z)",
        f"      (firstBOneOuterJ {x} {y} z)",
        f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
        f"  let H_root : ℤ := firstBOneOuterSuffixH {j} {x} {y} z",
        f"  let J : ℤ := firstBOneOuterJ {x} {y} z",
        f"  let B : ℤ := firstBOneOuterCorrection {x} {y} z",
        "  change FirstBOneOuterSuffixCore body H_root J B at core",
        f"  have z_lower_int : ({lower} : ℤ) ≤ z := by exact_mod_cast z_lower",
        f"  have z_upper_int : (z : ℤ) ≤ {upper} := by exact_mod_cast z_upper",
        "  have J_positive : (0 : ℤ) < J := by",
        "    dsimp [J]",
        "    unfold firstBOneOuterJ",
        "    positivity",
        "  have B_positive : (0 : ℤ) < B := by",
        "    dsimp [B]",
        "    unfold firstBOneOuterCorrection firstBOneOuterQ",
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
        assert wrapped and all(len(part) <= LEAN_LINE_LIMIT for part in wrapped)
        lines.extend(wrapped)
    return "\n".join(lines) + "\n"


def render_shard(
    index: int, intervals: tuple[tuple[int, int, int, int, int, Tree], ...]
) -> str:
    declarations = "\n\n".join(
        emit_interval_theorem(x, j, y, lower, upper, tree)
        for x, j, y, lower, upper, tree in intervals
    )
    source = f"""import MatrixMortality.ParabolicFirstBOneOuterSuffixCore

/-!
# Lower-range suffix certificate shard {index}

This file is generated by
`scripts/generate-parabolic-first-b-one-outer-suffix.py`.
-/

namespace MatrixMortality.ParabolicBlade

{declarations}

end MatrixMortality.ParabolicBlade
"""
    wrapped = wrap_lean(source)
    assert len(wrapped.splitlines()) <= LEAN_FILE_LIMIT
    return wrapped


def emit_case_dispatch(
    x: int,
    j: int,
    y: int,
    lower: int,
    upper: int,
    intervals: tuple[tuple[int, int, Tree], ...],
) -> str:
    output = [
        "/-- The generated interval tree extinguishes one complete terminal chamber. -/",
        f"theorem firstBOneOuterSuffixCore_false_{x}_{j}_{y}",
        f"    (body : List TagLetter) (z : Nat) (z_lower : {lower} ≤ z)",
    ]
    if (x, j, y) == (210, 1, 801):
        output.extend(
            (
                "    (core : FirstBOneOuterSuffixCore body",
                f"      (firstBOneOuterSuffixH {j} {x} {y} z)",
                f"      (firstBOneOuterJ {x} {y} z)",
                f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
                "  have z_upper : z ≤ 1447 := by",
                "    have cap := firstBOneOuterRay_z_lt_1448 body z core",
                "    omega",
            )
        )
    else:
        output.extend(
            (
                f"    (z_upper : z ≤ {upper})",
                "    (core : FirstBOneOuterSuffixCore body",
                f"      (firstBOneOuterSuffixH {j} {x} {y} z)",
                f"      (firstBOneOuterJ {x} {y} z)",
                f"      (firstBOneOuterCorrection {x} {y} z)) : False := by",
            )
        )
    if len(intervals) == 1:
        interval_lower, interval_upper, _ = intervals[0]
        output.append(
            f"  exact {theorem_name(x, j, y, interval_lower, interval_upper)} "
            "body z z_lower z_upper core"
        )
        return "\n".join(output)
    alternatives = " ∨ ".join(
        f"({interval_lower} ≤ z ∧ z ≤ {interval_upper})"
        for interval_lower, interval_upper, _ in intervals
    )
    output.append(f"  have interval : {alternatives} := by omega")
    names = [f"range{index}" for index in range(len(intervals))]
    output.append(f"  rcases interval with {' | '.join(names)}")
    for name, (interval_lower, interval_upper, _) in zip(names, intervals, strict=True):
        output.append(
            f"  · exact {theorem_name(x, j, y, interval_lower, interval_upper)} "
            f"body z {name}.1 {name}.2 core"
        )
    return "\n".join(output)


def render_aggregate(
    trees: dict[tuple[int, int, int], tuple[tuple[int, int, Tree], ...]],
) -> str:
    imports = "\n".join(
        f"import MatrixMortality.{module.stem}" for module in SHARD_MODULES
    )
    declarations = "\n\n".join(
        emit_case_dispatch(x, j, y, lower, upper, trees[x, j, y])
        for x, j, y, lower, upper in CASES
    )
    source = f"""{imports}

/-!
# Exact terminal suffix certificate below outer wait 211

The five tail-root chambers close in 96 exact suffix-tree nodes of depth at most five.
The unbounded chamber is first cut at inner wait 1448 by the analytic grammar gap.
-/

namespace MatrixMortality.ParabolicBlade

{declarations}

end MatrixMortality.ParabolicBlade
"""
    return wrap_lean(source)


def generate() -> dict[Path, str]:
    trees: dict[tuple[int, int, int], tuple[tuple[int, int, Tree], ...]] = {}
    flattened: list[tuple[int, int, int, int, int, Tree]] = []
    for x, j, y, lower, upper in CASES:
        intervals = maximal_intervals(x, j, y, lower, upper)
        expected = EXPECTED_INTERVALS[x, j, y]
        assert tuple((start, end) for start, end, _ in intervals) == expected
        trees[x, j, y] = intervals
        flattened.extend((x, j, y, start, end, tree) for start, end, tree in intervals)
    assert sum(node_count(item[-1]) for item in flattened) == 96
    assert max(tree_depth(item[-1]) for item in flattened) == 5
    split = 9
    groups = (tuple(flattened[:split]), tuple(flattened[split:]))
    generated = {
        module: render_shard(index, group)
        for index, (module, group) in enumerate(zip(SHARD_MODULES, groups, strict=True))
    }
    generated[AGGREGATE_MODULE] = render_aggregate(trees)
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
                "stale generated outer-suffix modules: " + ", ".join(map(str, stale))
            )
        return
    if args.write:
        for path, source in generated.items():
            path.write_text(source)
        return
    print(generated[AGGREGATE_MODULE], end="")


if __name__ == "__main__":
    main()

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Generate the exact large-inner x=211 suffix certificate.

The default output is the generated Lean module. ``--write`` replaces that module;
``--check`` fails when it is stale. The generator verifies the affine ray signs and the
complete depth-three suffix tree before emitting ordinary Lean proofs. Lean then rechecks
every branch without trusting this program.
"""

from __future__ import annotations

import argparse
from pathlib import Path

CERTIFICATE_MODULE = Path("MatrixMortality/ParabolicFirstBOneInnerCertificate.lean")
SHARD_GROUPS = (
    ("J0A", (("j0a", 0, 39701, 39726),)),
    ("J0B", (("j0b", 0, 39727, 39752),)),
    ("J0C", (("j0c", 0, 39753, 39778),)),
    ("J0D", (("j0d", 0, 39779, 39804),)),
    ("J0E", (("j0e", 0, 39805, 39830),)),
    ("J1", (("j1", 1, 26337, 26355),)),
    ("J23", (("j2", 2, 23671, 23675), ("j3", 3, 22898, 22898))),
)
Z_MIN = 3**13

Q_Z = 465621956
Q_ONE = 42879529
J_YZ = 620717828832
J_Y = 58005064872
J_Z = 133690369309176
J_ONE = 12496984445436

CANDIDATE_RANGES = (
    (0, 39701, 39830),
    (1, 26337, 26355),
    (2, 23671, 23675),
    (3, 22898, 22898),
)
BOUND_RANGES = {
    0: (39701, 39830),
    1: (26337, 26355),
    2: (23671, 23675),
    3: (22898, 22898),
    4: (22651, 22650),
    5: (22570, 22569),
    6: (22543, 22542),
    7: (22534, 22533),
    8: (22531, 22530),
    9: (22530, 22529),
}
UPPER_ONLY = {10: 22528, 11: 22528, 12: 22528}

ARITH_DEFS = (
    "firstBOneX211SuffixH",
    "firstBOneX211A",
    "firstBOneX211B",
    "firstBOneX211Q",
    "firstBOneX211J",
)


def affine(y: int) -> tuple[tuple[int, int], tuple[int, int], tuple[int, int]]:
    j = (J_YZ * y + J_Z, J_Y * y + J_ONE)
    a = (729 * (72 * y - 9) * Q_Z, 729 * (72 * y - 9) * Q_ONE)
    b = ((8 * y - 9) * Q_Z, (8 * y - 9) * Q_ONE)
    return j, a, b


def add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return left[0] + right[0], left[1] + right[1]


def sub(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return left[0] - right[0], left[1] - right[1]


def scale(factor: int, line: tuple[int, int]) -> tuple[int, int]:
    return factor * line[0], factor * line[1]


def positive_on_ray(line: tuple[int, int]) -> bool:
    slope, intercept = line
    return slope >= 0 and slope * Z_MIN + intercept > 0


def negative_on_ray(line: tuple[int, int]) -> bool:
    slope, intercept = line
    return slope <= 0 and slope * Z_MIN + intercept < 0


def nonpositive_on_ray(line: tuple[int, int]) -> bool:
    slope, intercept = line
    return slope <= 0 and slope * Z_MIN + intercept <= 0


def nonzero_on_ray(line: tuple[int, int]) -> bool:
    return positive_on_ray(line) or negative_on_ray(line)


def gap_index(
    h_line: tuple[int, int], j_line: tuple[int, int], b_line: tuple[int, int]
) -> int | None:
    for k in range(31):
        low = sub(
            scale(242 * 3 ** (k + 1), h_line),
            add(scale(39, j_line), scale(242 * 3 ** (k + 1), b_line)),
        )
        high = sub(scale(81 * 3**k, h_line), scale(13, j_line))
        if positive_on_ray(low) and negative_on_ray(high):
            return k
    return None


def certificate_tree(
    j_position: int, y: int, h_line: tuple[int, int] | None = None, depth: int = 0
) -> dict:
    j_line, a_line, b_line = affine(y)
    if h_line is None:
        f_line = sub(a_line, scale(39, j_line))
        h_line = sub(scale(243 * 3**j_position, f_line), scale(39, j_line))
    gap = gap_index(h_line, j_line, b_line)
    if gap is not None:
        return {"kind": "gap", "k": gap}
    if nonpositive_on_ray(h_line):
        return {"kind": "nonpositive"}
    global_line = sub(scale(242, h_line), add(scale(39, j_line), scale(242, b_line)))
    if positive_on_ray(global_line):
        return {"kind": "global"}
    if not nonzero_on_ray(sub(h_line, b_line)):
        raise RuntimeError(f"open empty suffix at j={j_position}, y={y}, depth={depth}")
    if depth >= 3:
        raise RuntimeError(f"certificate exceeds depth three at j={j_position}, y={y}")
    return {
        "kind": "branch",
        "b": certificate_tree(
            j_position, y, sub(scale(243, h_line), scale(39, j_line)), depth + 1
        ),
        "c": certificate_tree(j_position, y, scale(3, h_line), depth + 1),
    }


def tree_nodes(tree: dict) -> int:
    if tree["kind"] != "branch":
        return 1
    return 1 + tree_nodes(tree["b"]) + tree_nodes(tree["c"])


out: list[str] = []


def emit(text: str = "") -> None:
    out.append(text)


def emit_bracketed_tactic(
    indent: str,
    tactic: str,
    names: list[str] | tuple[str, ...],
    *,
    bullet: bool = False,
    suffix: str = "",
) -> None:
    """Emit one width-bounded tactic whose argument is a bracketed name list."""
    prefix = f"{indent}{'· ' if bullet else ''}{tactic} ["
    continuation = f"{indent}{'    ' if bullet else '  '}"
    line = prefix
    for index, name in enumerate(names):
        token = f"{name}{',' if index + 1 < len(names) else ''}"
        separator = "" if line.endswith("[") else " "
        if len(line) + len(separator) + len(token) + 1 > 100:
            emit(line)
            line = f"{continuation}{token}"
        else:
            line = f"{line}{separator}{token}"
    emit(f"{line}]{suffix}")


def emit_condition(indent: str, lets: list[str]) -> None:
    emit_bracketed_tactic(
        indent,
        "norm_num",
        [*reversed(lets), *ARITH_DEFS],
        suffix=" at equality",
    )
    emit(f"{indent}nlinarith")


def emit_condition_goal(indent: str, lets: list[str]) -> None:
    emit_bracketed_tactic(
        indent, "norm_num", [*reversed(lets), *ARITH_DEFS], bullet=True
    )
    emit(f"{indent}  nlinarith")


def emit_node(
    tree: dict,
    *,
    indent: str,
    body: str,
    core: str,
    h_name: str,
    lets: list[str],
    word: str,
    y: int,
) -> None:
    j_name = "J"
    b_name = "B"
    kind = tree["kind"]
    if kind == "nonpositive":
        emit(
            f"{indent}apply firstBOneX211SuffixCore_false_of_nonpositive {body} "
            f"{h_name} {j_name} {b_name}"
        )
        emit(f"{indent}  J_positive B_positive")
        emit_condition_goal(indent, lets)
        emit(f"{indent}· exact {core}")
        return
    if kind == "global":
        emit(
            f"{indent}apply firstBOneX211SuffixCore_false_of_global {body} "
            f"{h_name} {j_name} {b_name}"
        )
        emit(f"{indent}  J_positive B_positive")
        emit_condition_goal(indent, lets)
        emit(f"{indent}· exact {core}")
        return
    if kind == "gap":
        emit(
            f"{indent}apply firstBOneX211SuffixCore_false_of_gap {tree['k']} {body} "
            f"{h_name} {j_name} {b_name}"
        )
        emit(f"{indent}  J_positive B_positive")
        emit_condition_goal(indent, lets)
        emit_condition_goal(indent, lets)
        emit(f"{indent}· exact {core}")
        return

    next_depth = len(word) + 1
    tail = f"tail{next_depth}"
    emit(f"{indent}cases {body} with")
    emit(f"{indent}| nil =>")
    emit(
        f"{indent}    apply firstBOneX211SuffixCore_false_of_nil {h_name} {j_name} {b_name}"
    )
    emit(f"{indent}    · intro equality")
    emit_condition(indent + "      ", lets)
    emit(f"{indent}    · exact {core}")
    emit(f"{indent}| cons letter {tail} =>")
    emit(f"{indent}    cases letter with")
    for letter in ("b", "c"):
        child_word = word + letter
        child_h = f"H_{child_word}"
        child_core = f"core_{child_word}"
        transition = f"243 * {h_name} - 39 * J" if letter == "b" else f"3 * {h_name}"
        transition_theorem = f"firstBOneX211SuffixCore_cons_{letter}"
        emit(f"{indent}    | {letter} =>")
        emit(f"{indent}        let {child_h} : ℤ := {transition}")
        emit(
            f"{indent}        have {child_core} : FirstBOneX211SuffixCore {tail} "
            f"{child_h} J B := by"
        )
        emit(f"{indent}          dsimp [{child_h}]")
        emit(f"{indent}          exact {transition_theorem}")
        emit(f"{indent}            {tail} {h_name} J B {core}")
        emit_node(
            tree[letter],
            indent=indent + "        ",
            body=tail,
            core=child_core,
            h_name=child_h,
            lets=lets + [child_h],
            word=child_word,
            y=y,
        )


def emit_bound_theorem(j_position: int, lower: int | None, upper: int) -> None:
    theorem_name = f"largeInner_j{j_position}_bounds"
    emit(f"private theorem {theorem_name}")
    emit("    (y z : Nat) (z_large : 3 ^ 13 ≤ z)")
    emit(f"    (envelope : FirstBOneX211LargeInnerEnvelope {j_position} y z) :")
    if lower is None:
        emit(f"    y ≤ {upper} := by")
    else:
        emit(f"    {lower} ≤ y ∧ y ≤ {upper} := by")
    emit("  have z_large_int : (1594323 : ℤ) ≤ z := by exact_mod_cast z_large")
    if lower is not None:
        emit("  constructor")
        emit("  · by_contra y_not_large")
        emit(f"    have y_small_int : (y : ℤ) ≤ {lower - 1} := by omega")
        emit("    have rectangle :")
        emit(f"        (0 : ℤ) ≤ ({lower - 1} - (y : ℤ)) * ((z : ℤ) - 1594323) :=")
        emit(
            "      mul_nonneg (sub_nonneg.mpr y_small_int) (sub_nonneg.mpr z_large_int)"
        )
        emit_bracketed_tactic(
            "    ",
            "norm_num",
            ("FirstBOneX211LargeInnerEnvelope", *ARITH_DEFS),
            suffix=" at envelope",
        )
        emit("    ring_nf at envelope")
        emit("    nlinarith")
        proof_indent = "    "
        emit("  · by_contra y_not_small")
    else:
        proof_indent = "  "
        emit("  by_contra y_not_small")
    emit(f"{proof_indent}have y_large_int : ({upper + 1} : ℤ) ≤ y := by omega")
    emit(f"{proof_indent}have rectangle :")
    emit(
        f"{proof_indent}    (0 : ℤ) ≤ ((y : ℤ) - {upper + 1}) * ((z : ℤ) - 1594323) :="
    )
    emit(
        f"{proof_indent}  mul_nonneg (sub_nonneg.mpr y_large_int) "
        "(sub_nonneg.mpr z_large_int)"
    )
    emit_bracketed_tactic(
        proof_indent,
        "norm_num",
        ("FirstBOneX211LargeInnerEnvelope", *ARITH_DEFS),
        suffix=" at envelope",
    )
    emit(f"{proof_indent}ring_nf at envelope")
    emit(f"{proof_indent}nlinarith")
    emit()


def emit_kill_theorem(j_position: int, y: int, tree: dict) -> None:
    emit(f"private theorem largeInner_j{j_position}_y{y}")
    emit("    (body : List TagLetter) (z : Nat) (z_large : 3 ^ 13 ≤ z)")
    emit(
        f"    (core : FirstBOneX211SuffixCore body "
        f"(firstBOneX211SuffixH {j_position} {y} z)"
    )
    emit(f"      (firstBOneX211J {y} z) (firstBOneX211B {y} z)) : False := by")
    emit(f"  let H_root : ℤ := firstBOneX211SuffixH {j_position} {y} z")
    emit(f"  let J : ℤ := firstBOneX211J {y} z")
    emit(f"  let B : ℤ := firstBOneX211B {y} z")
    emit("  change FirstBOneX211SuffixCore body H_root J B at core")
    emit("  have z_large_int : (1594323 : ℤ) ≤ z := by exact_mod_cast z_large")
    emit("  have J_positive : (0 : ℤ) < J := by")
    emit("    dsimp [J]")
    emit("    unfold firstBOneX211J")
    emit("    positivity")
    emit("  have B_positive : (0 : ℤ) < B := by")
    emit("    dsimp [B]")
    emit("    unfold firstBOneX211B firstBOneX211Q")
    emit("    positivity")
    emit_node(
        tree,
        indent="  ",
        body="body",
        core="core",
        h_name="H_root",
        lets=["H_root", "J", "B"],
        word="",
        y=y,
    )
    emit()


def shard_module(suffix: str) -> Path:
    return Path(f"MatrixMortality/ParabolicFirstBOneInnerCertificate{suffix}.lean")


def build_trees() -> dict[tuple[int, int], dict]:
    trees: dict[tuple[int, int], dict] = {}
    node_total = 0
    for j_position, lower, upper in CANDIDATE_RANGES:
        for y in range(lower, upper + 1):
            tree = certificate_tree(j_position, y)
            trees[(j_position, y)] = tree
            node_total += tree_nodes(tree)
    covered = {
        (j_position, y)
        for _, chambers in SHARD_GROUPS
        for _, j_position, lower, upper in chambers
        for y in range(lower, upper + 1)
    }
    assert covered == trees.keys()
    assert len(trees) == 155
    assert node_total == 231
    return trees


def emit_header(title: str, description: tuple[str, ...]) -> None:
    emit("/-!")
    emit(f"# {title}")
    emit()
    for line in description:
        emit(line)
    emit("-/")
    emit()
    emit("namespace MatrixMortality.ParabolicBlade")
    emit()


def emit_shard_dispatch(dispatch: str, j_position: int, lower: int, upper: int) -> None:
    emit(
        f"/-- Exhausts the generated `j = {j_position}`, `{lower} ≤ y ≤ {upper}` "
        "certificate shard. -/"
    )
    emit(f"theorem firstBOneX211SuffixCore_false_{dispatch}")
    emit("    (body : List TagLetter) (y z : Nat)")
    emit(f"    (y_lower : {lower} ≤ y) (y_upper : y ≤ {upper})")
    emit("    (z_large : 3 ^ 13 ≤ z)")
    emit(
        f"    (core : FirstBOneX211SuffixCore body (firstBOneX211SuffixH {j_position} y z)"
    )
    emit("      (firstBOneX211J y z) (firstBOneX211B y z)) : False := by")
    emit("  interval_cases y")
    for y in range(lower, upper + 1):
        emit(f"  · exact largeInner_j{j_position}_y{y} body z z_large core")
    emit()


def render_shard(
    suffix: str,
    chambers: tuple[tuple[str, int, int, int], ...],
    trees: dict[tuple[int, int], dict],
) -> str:
    out.clear()
    emit("import MatrixMortality.ParabolicFirstBOneInnerCore")
    emit()
    emit_header(
        f"Large-inner suffix certificate shard {suffix}",
        (
            "This file is generated by `scripts/generate-parabolic-first-b-one-inner.py`.",
            "The generator verifies the complete 155-chamber, 231-node suffix tree before",
            "emission. Lean rechecks every sign and grammar branch in this shard.",
        ),
    )
    for _, j_position, lower, upper in chambers:
        for y in range(lower, upper + 1):
            emit_kill_theorem(j_position, y, trees[(j_position, y)])
    for dispatch, j_position, lower, upper in chambers:
        emit_shard_dispatch(dispatch, j_position, lower, upper)
    emit("end MatrixMortality.ParabolicBlade")
    return "\n".join(out) + "\n"


def emit_candidate_definition() -> None:
    emit("/-- The four affine chambers left by the analytic large-inner reduction. -/")
    emit("def FirstBOneX211LargeInnerCandidate (j y : Nat) : Prop :=")
    for index, (j_position, lower, upper) in enumerate(CANDIDATE_RANGES):
        prefix = "  " if index == 0 else "    "
        suffix = " ∨" if index < len(CANDIDATE_RANGES) - 1 else ""
        emit(f"{prefix}(j = {j_position} ∧ {lower} ≤ y ∧ y ≤ {upper}){suffix}")
    emit()


def emit_candidate_reduction() -> None:
    emit(
        "/-- The large-inner envelope leaves exactly four finite first-`b`/middle-wait strips. -/"
    )
    emit("theorem firstBOneX211LargeInnerCandidate_of_envelope")
    emit("    (j y z : Nat) (y_upper : y ≤ 51767) (z_large : 3 ^ 13 ≤ z)")
    emit("    (envelope : FirstBOneX211LargeInnerEnvelope j y z) :")
    emit("    FirstBOneX211LargeInnerCandidate j y := by")
    emit(
        "  have y_lower := firstBOneX211_y_lower_of_large_inner_envelope j y z envelope"
    )
    emit("  have position_bound :=")
    emit("    firstBOneX211_position_lt_thirteen_of_large_inner_envelope")
    emit("      j y z y_lower y_upper z_large envelope")
    emit("  have position_le : j ≤ 12 := by omega")
    emit("  interval_cases j")
    for j_position in range(13):
        if j_position < 4:
            if j_position == 0:
                result = "Or.inl ⟨rfl, bounds.1, bounds.2⟩"
            elif j_position == 1:
                result = "Or.inr (Or.inl ⟨rfl, bounds.1, bounds.2⟩)"
            elif j_position == 2:
                result = "Or.inr (Or.inr (Or.inl ⟨rfl, bounds.1, bounds.2⟩))"
            else:
                result = "Or.inr (Or.inr (Or.inr ⟨rfl, bounds.1, bounds.2⟩))"
            emit(
                f"  · have bounds := largeInner_j{j_position}_bounds y z z_large envelope"
            )
            emit(f"    exact {result}")
        elif j_position <= 9:
            emit(
                f"  · have bounds := largeInner_j{j_position}_bounds y z z_large envelope"
            )
            emit("    omega")
        else:
            emit(
                f"  · have upper := largeInner_j{j_position}_bounds y z z_large envelope"
            )
            emit("    omega")
    emit()


def emit_j0_dispatch() -> None:
    chunks = SHARD_GROUPS[:5]
    emit("    have chamber :")
    for index, (_, ((_, _, lower, upper),)) in enumerate(chunks):
        prefix = "        " if index == 0 else "          "
        suffix = " ∨" if index + 1 < len(chunks) else " := by"
        emit(f"{prefix}({lower} ≤ y ∧ y ≤ {upper}){suffix}")
    emit("      omega")
    emit("    rcases chamber with first | second | third | fourth | fifth")
    for case_name, (_, ((dispatch, _, _, _),)) in zip(
        ("first", "second", "third", "fourth", "fifth"), chunks, strict=True
    ):
        emit(f"    · exact firstBOneX211SuffixCore_false_{dispatch} body y z")
        emit(f"        {case_name}.1 {case_name}.2 z_large core")


def emit_candidate_extinction() -> None:
    emit(
        "/-- Every candidate suffix core is impossible throughout the large-inner ray. -/"
    )
    emit("theorem firstBOneX211SuffixCore_false_of_large_inner_candidate")
    emit("    (body : List TagLetter) (j y z : Nat) (z_large : 3 ^ 13 ≤ z)")
    emit("    (candidate : FirstBOneX211LargeInnerCandidate j y)")
    emit("    (core : FirstBOneX211SuffixCore body (firstBOneX211SuffixH j y z)")
    emit("      (firstBOneX211J y z) (firstBOneX211B y z)) : False := by")
    emit("  unfold FirstBOneX211LargeInnerCandidate at candidate")
    emit("  rcases candidate with first | second | third | fourth")
    emit("  · rcases first with ⟨rfl, y_lower, y_upper⟩")
    emit_j0_dispatch()
    for case_name, dispatch in (("second", "j1"), ("third", "j2"), ("fourth", "j3")):
        emit(f"  · rcases {case_name} with ⟨rfl, y_lower, y_upper⟩")
        emit(f"    exact firstBOneX211SuffixCore_false_{dispatch} body y z")
        emit("      y_lower y_upper z_large core")
    emit()


def render_certificate() -> str:
    out.clear()
    for suffix, _ in SHARD_GROUPS:
        emit(f"import MatrixMortality.ParabolicFirstBOneInnerCertificate{suffix}")
    emit()
    emit_header(
        "Exact large-inner suffix certificate at outer wait 211",
        (
            "This file is generated by `scripts/generate-parabolic-first-b-one-inner.py`.",
            "The generator proves that 155 affine chambers close in a 231-node suffix tree of",
            "depth at most three. Imported shards recheck every emitted sign and grammar branch",
            "in Lean.",
        ),
    )
    emit_candidate_definition()
    for j_position, (lower, upper) in BOUND_RANGES.items():
        emit_bound_theorem(j_position, lower, upper)
    for j_position, upper in UPPER_ONLY.items():
        emit_bound_theorem(j_position, None, upper)
    emit_candidate_reduction()
    emit_candidate_extinction()
    emit("end MatrixMortality.ParabolicBlade")
    return "\n".join(out) + "\n"


def generate() -> dict[Path, str]:
    trees = build_trees()
    generated = {
        shard_module(suffix): render_shard(suffix, chambers, trees)
        for suffix, chambers in SHARD_GROUPS
    }
    generated[CERTIFICATE_MODULE] = render_certificate()
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
            paths = ", ".join(map(str, stale))
            raise SystemExit(
                f"stale generated large-inner certificate modules: {paths}"
            )
        return
    if args.write:
        for path, source in generated.items():
            path.write_text(source)
        return
    print(generated[CERTIFICATE_MODULE], end="")


if __name__ == "__main__":
    main()

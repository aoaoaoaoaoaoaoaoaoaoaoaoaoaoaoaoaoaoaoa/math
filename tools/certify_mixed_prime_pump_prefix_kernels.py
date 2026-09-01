#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.13"
# ///
"""Certify that all 23 pumped kernel families have no proper prefix kernel pair."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from fractions import Fraction

from certify_mixed_prime_pump_families import PUMP_SEEDS, PumpSeed, pumped_pair

REPLAY_DEPTH = 64


@dataclass(frozen=True, slots=True)
class FixedDefect:
    """One balanced base prefix and its nonzero affine-offset defect."""

    cut: int
    defect: str


@dataclass(frozen=True, slots=True)
class DepthDefect:
    """One balanced prefix checked before its word prefix becomes stationary."""

    depth: int
    cut: int
    defect: str


@dataclass(frozen=True, slots=True)
class FamilyCertificate:
    """One exact count-walk splice and its affine action separation."""

    family: str
    base_length: int
    base_balanced_cuts: tuple[int, ...]
    base_defects: tuple[FixedDefect, ...]
    overlap_depth: int
    structural_splice_base: int
    structural_increment_period: tuple[int, int]
    transient_defects: tuple[DepthDefect, ...]
    stationary_balanced_cuts: tuple[int, ...]
    splice_base: int
    splice_step: int
    inserted_count_cell: tuple[int, int]
    creates_balanced_ladder: bool
    ladder_left_extension: str | None
    ladder_right_extension: str | None
    ladder_seed_defect: str | None
    ladder_defect_ratio: str | None


@dataclass(frozen=True, slots=True)
class CertificateSummary:
    """Compact result of the all-depth prefix-kernel extinction."""

    pump_families: int
    exact_count_walk_recursions: int
    base_balanced_prefixes: int
    infinite_balanced_ladders: int
    proper_prefix_action_collisions: int
    replay_depth: int
    certificate_sha256: str
    status: str


def affine_action(word: str) -> tuple[Fraction, Fraction]:
    """Return exact slope and offset for one raw mixed-prime word."""
    scale = Fraction(1)
    offset = Fraction(0)
    for letter in reversed(word):
        match letter:
            case "D":
                scale *= Fraction(2, 3)
                offset *= Fraction(2, 3)
            case "T":
                scale *= Fraction(3, 5)
                offset = Fraction(3, 5) * offset + 1
            case unreachable:
                raise AssertionError(unreachable)
    return scale, offset


def dilate_difference_track(seed: PumpSeed, depth: int) -> tuple[int, ...]:
    """Return all prefix `#D(left)-#D(right)` values, including both endpoints."""
    left, right = pumped_pair(seed, depth)
    difference = 0
    track = [difference]
    for left_letter, right_letter in zip(left, right, strict=True):
        difference += (left_letter == "D") - (right_letter == "D")
        track.append(difference)
    assert difference == 0
    return tuple(track)


def dilate_increment_word(seed: PumpSeed, depth: int) -> tuple[int, ...]:
    """Return the letterwise increments whose cumulative sum is the count walk."""
    left, right = pumped_pair(seed, depth)
    return tuple(
        (left_letter == "D") - (right_letter == "D")
        for left_letter, right_letter in zip(left, right, strict=True)
    )


def proper_balanced_cuts(seed: PumpSeed, depth: int) -> tuple[int, ...]:
    """Return every positive proper zero of the prefix count walk."""
    track = dilate_difference_track(seed, depth)
    return tuple(cut for cut, value in enumerate(track[1:-1], start=1) if value == 0)


def overlap_depth(seed: PumpSeed) -> int:
    """First depth at which the two pumped intervals overlap."""
    width = len(seed.pump)
    displacement = abs(seed.left_cut - seed.right_cut)
    return (displacement + width - 1) // width


def structural_splice(seed: PumpSeed, depth: int) -> int:
    """Return the count-walk insertion index supplied by pump-interval overlap."""
    assert depth >= overlap_depth(seed)
    return min(seed.left_cut, seed.right_cut) + len(seed.pump) * depth + 1


def structural_increment_normal_form(
    seed: PumpSeed,
) -> tuple[int, tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """Construct the exact all-depth lasso for the letterwise count increments.

    At the overlap depth ``k₀``, synchronously align the two words immediately before the
    earlier pumped interval ends. For every ``k ≥ k₀``, both pump intervals then overlap;
    increasing ``k`` extends that overlap by one complete copy of the common pump and moves
    the unchanged boundary/tail comparison right by the pump width. Hence the increment word
    is exactly ``head ++ period^(k-k₀) ++ tail``. This is a word decomposition, not a finite
    extrapolation.
    """
    width = len(seed.pump)
    assert width == 2
    assert seed.pump.count("D") == 1
    assert len(seed.left) == len(seed.right)
    assert 0 <= seed.left_cut <= len(seed.left)
    assert 0 <= seed.right_cut <= len(seed.right)

    depth = overlap_depth(seed)
    splice = structural_splice(seed, depth)
    boundary = splice - 1
    base = dilate_increment_word(seed, depth)
    successor = dilate_increment_word(seed, depth + 1)
    head = base[:boundary]
    period = successor[boundary : boundary + width]
    tail = base[boundary:]
    assert successor == head + period + tail
    assert sum(period) == 0
    return depth, head, period, tail


def canonical_splice(seed: PumpSeed, depth: int) -> tuple[int, tuple[int, int]]:
    """Recover the rightmost two-cell insertion from depth `k` to `k+1`."""
    old = dilate_difference_track(seed, depth)
    new = dilate_difference_track(seed, depth + 1)
    positions = tuple(
        position
        for position in range(len(old) + 1)
        if new[:position] == old[:position] and new[position + 2 :] == old[position:]
    )
    assert positions
    position = max(positions)
    return position, (new[position], new[position + 1])


def prefix_defect(word_left: str, word_right: str, cut: int) -> Fraction:
    """Return the exact affine-offset difference at one balanced prefix cut."""
    left_scale, left_offset = affine_action(word_left[:cut])
    right_scale, right_offset = affine_action(word_right[:cut])
    assert left_scale == right_scale
    return left_offset - right_offset


def prefix_stabilization_depth(seed: PumpSeed, cut: int) -> int:
    """Return a depth after which both fixed-position prefixes stop changing."""
    width = len(seed.pump)

    def side_depth(pump_cut: int) -> int:
        exposed = max(cut - pump_cut, 0)
        return (exposed + width - 1) // width

    return max(side_depth(seed.left_cut), side_depth(seed.right_cut))


def moving_prefix_lasso(
    seed: PumpSeed, *, left: bool, ladder_origin: int
) -> tuple[int, int, str]:
    """Return ``d₀,e,B`` with moving prefix ``H·pump^(d+e)·B`` for ``d ≥ d₀``."""
    word = seed.left if left else seed.right
    pump_cut = seed.left_cut if left else seed.right_cut
    width = len(seed.pump)
    end_displacement = ladder_origin - pump_cut - width
    if end_displacement >= 0:
        exponent_offset = 0
        bridge = word[pump_cut : pump_cut + end_displacement]
        first_depth = 1
    else:
        exponent_offset, remainder = divmod(end_displacement, width)
        bridge = seed.pump[:remainder]
        first_depth = max(1, -exponent_offset)
    head = word[:pump_cut]

    for depth in (first_depth, first_depth + 1):
        pumped_left, pumped_right = pumped_pair(seed, depth)
        pumped = pumped_left if left else pumped_right
        cut = ladder_origin + width * (depth - 1)
        expected = head + seed.pump * (depth + exponent_offset) + bridge
        assert pumped[:cut] == expected
    return first_depth, exponent_offset, bridge


def certify_family(seed: PumpSeed) -> FamilyCertificate:
    """Extract and replay one symbolic count-walk/offset recurrence."""
    base_left, base_right = pumped_pair(seed, 0)
    base_cuts = proper_balanced_cuts(seed, 0)
    base_defects = tuple(
        FixedDefect(cut=cut, defect=str(prefix_defect(base_left, base_right, cut)))
        for cut in base_cuts
    )
    assert all(Fraction(row.defect) != 0 for row in base_defects)

    overlap, increment_head, increment_period, increment_tail = (
        structural_increment_normal_form(seed)
    )
    structural_base = structural_splice(seed, overlap) - len(seed.pump) * overlap
    structural_position = structural_splice(seed, overlap)
    overlap_track = dilate_difference_track(seed, overlap)
    next_overlap_track = dilate_difference_track(seed, overlap + 1)
    inserted_values = next_overlap_track[
        structural_position : structural_position + len(seed.pump)
    ]
    assert len(inserted_values) == 2
    inserted_cell = (inserted_values[0], inserted_values[1])
    assert next_overlap_track == (
        overlap_track[:structural_position]
        + inserted_cell
        + overlap_track[structural_position:]
    )

    # The preceding word normal form proves this recurrence for every later depth. Replaying a
    # large prefix of the family independently audits the implementation of that symbolic form.
    for depth in range(REPLAY_DEPTH):
        increments = dilate_increment_word(seed, depth)
        if depth >= overlap:
            assert increments == (
                increment_head + increment_period * (depth - overlap) + increment_tail
            )
            position = structural_splice(seed, depth)
            old = dilate_difference_track(seed, depth)
            new = dilate_difference_track(seed, depth + 1)
            assert new == old[:position] + inserted_cell + old[position:]

    creates_ladder = 0 in inserted_cell
    zero_offset = inserted_cell.index(0) if creates_ladder else None
    splice_base, canonical_cell = canonical_splice(seed, 0)
    if creates_ladder:
        assert inserted_cell.count(0) == 1
        assert canonical_cell[0] == 0 and canonical_cell[1] != 0
        structural_gap = splice_base - structural_base
        assert structural_gap >= 0
        assert zero_offset == structural_gap % len(seed.pump)
        assert overlap >= structural_gap // len(seed.pump)
    else:
        assert 0 not in inserted_cell
    stationary_cuts = base_cuts

    def expected_balanced_cuts(depth: int) -> tuple[int, ...]:
        expected = set(base_cuts)
        if creates_ladder:
            expected.update(
                splice_base + len(seed.pump) * index for index in range(depth)
            )
        return tuple(sorted(expected))

    assert proper_balanced_cuts(seed, overlap) == expected_balanced_cuts(overlap)
    assert all(cut < structural_position for cut in base_cuts)

    proof_depth = overlap
    if creates_ladder:
        proof_depth = max(
            proof_depth,
            moving_prefix_lasso(seed, left=True, ladder_origin=splice_base)[0],
            moving_prefix_lasso(seed, left=False, ladder_origin=splice_base)[0],
        )
    transient_defects: list[DepthDefect] = []
    for depth in range(proof_depth + 1):
        left, right = pumped_pair(seed, depth)
        for cut in proper_balanced_cuts(seed, depth):
            defect = prefix_defect(left, right, cut)
            assert defect != 0
            transient_defects.append(
                DepthDefect(depth=depth, cut=cut, defect=str(defect))
            )

    # Every stationary cut has a finite transient followed by a literally constant prefix pair.
    for cut in stationary_cuts:
        stable_from = prefix_stabilization_depth(seed, cut)
        for depth in range(stable_from + 1):
            left, right = pumped_pair(seed, depth)
            assert cut in proper_balanced_cuts(seed, depth)
            assert prefix_defect(left, right, cut) != 0
        stable_left, stable_right = pumped_pair(seed, stable_from)
        next_left, next_right = pumped_pair(seed, stable_from + 1)
        assert stable_left[:cut] == next_left[:cut]
        assert stable_right[:cut] == next_right[:cut]
        assert prefix_defect(stable_left, stable_right, cut) != 0

    if creates_ladder:
        assert inserted_cell in ((0, 1), (0, -1), (1, 0), (-1, 0))
    else:
        assert 0 not in inserted_cell

    # The structural splice proves the complete zero-set formula by induction. In a ladder
    # family, the gap/parity assertions say exactly how many terminal ladder cells shift and
    # which vacated cell the inserted zero restores. This replay audits that symbolic induction.
    for depth in range(REPLAY_DEPTH + 1):
        assert proper_balanced_cuts(seed, depth) == expected_balanced_cuts(depth)
        assert all(
            prefix_defect(*pumped_pair(seed, depth), cut) != 0
            for cut in proper_balanced_cuts(seed, depth)
        )

    if not creates_ladder:
        return FamilyCertificate(
            family=seed.identifier,
            base_length=len(base_left),
            base_balanced_cuts=base_cuts,
            base_defects=base_defects,
            overlap_depth=overlap,
            structural_splice_base=structural_base,
            structural_increment_period=(increment_period[0], increment_period[1]),
            transient_defects=tuple(transient_defects),
            stationary_balanced_cuts=stationary_cuts,
            splice_base=splice_base,
            splice_step=2,
            inserted_count_cell=inserted_cell,
            creates_balanced_ladder=False,
            ladder_left_extension=None,
            ladder_right_extension=None,
            ladder_seed_defect=None,
            ladder_defect_ratio=None,
        )

    assert zero_offset is not None
    left_lasso = moving_prefix_lasso(seed, left=True, ladder_origin=splice_base)
    right_lasso = moving_prefix_lasso(seed, left=False, ladder_origin=splice_base)
    recurrence_depth = max(left_lasso[0], right_lasso[0])
    seed_left, seed_right = pumped_pair(seed, recurrence_depth)
    seed_cut = splice_base + 2 * (recurrence_depth - 1)
    seed_scale, _ = affine_action(seed_left[:seed_cut])
    seed_defect = prefix_defect(seed_left, seed_right, seed_cut)
    assert seed_defect != 0

    successor_left, successor_right = pumped_pair(seed, recurrence_depth + 1)
    successor_cut = seed_cut + 2
    left_extension = successor_left[seed_cut:successor_cut]
    right_extension = successor_right[seed_cut:successor_cut]
    left_ratio, left_offset = affine_action(left_extension)
    right_ratio, right_offset = affine_action(right_extension)
    assert {left_extension, right_extension} == {"DT", "TD"}
    assert left_ratio == right_ratio == Fraction(2, 5)
    assert seed.pump + left_lasso[2] == left_lasso[2] + left_extension
    assert seed.pump + right_lasso[2] == right_lasso[2] + right_extension

    # If δ is the prefix offset defect and s its common slope, appending the opposite macros
    # sends δ to δ+s·Δb. This fixed-point identity makes the new defect exactly (2/5)δ.
    assert (1 - left_ratio) * seed_defect + seed_scale * (
        left_offset - right_offset
    ) == 0

    for depth in range(recurrence_depth, REPLAY_DEPTH):
        left, right = pumped_pair(seed, depth)
        cut = seed_cut + 2 * (depth - recurrence_depth)
        defect = prefix_defect(left, right, cut)
        assert defect == seed_defect * Fraction(2, 5) ** (depth - recurrence_depth)
        assert defect != 0
        next_left, next_right = pumped_pair(seed, depth + 1)
        assert next_left[: cut + 2] == left[:cut] + left_extension
        assert next_right[: cut + 2] == right[:cut] + right_extension

    return FamilyCertificate(
        family=seed.identifier,
        base_length=len(base_left),
        base_balanced_cuts=base_cuts,
        base_defects=base_defects,
        overlap_depth=overlap,
        structural_splice_base=structural_base,
        structural_increment_period=(increment_period[0], increment_period[1]),
        transient_defects=tuple(transient_defects),
        stationary_balanced_cuts=stationary_cuts,
        splice_base=splice_base,
        splice_step=2,
        inserted_count_cell=inserted_cell,
        creates_balanced_ladder=True,
        ladder_left_extension=left_extension,
        ladder_right_extension=right_extension,
        ladder_seed_defect=str(seed_defect),
        ladder_defect_ratio="2/5",
    )


def certify() -> tuple[dict[str, object], CertificateSummary]:
    """Certify every count-walk cell and every affine defect recurrence."""
    rows = tuple(certify_family(seed) for seed in PUMP_SEEDS)
    assert len(rows) == 23
    ladder_rows = tuple(row for row in rows if row.creates_balanced_ladder)
    assert len(ladder_rows) == 11
    assert all(row.base_balanced_cuts[0] == 3 for row in rows)

    payload: dict[str, object] = {
        "scope": "all positive proper same-position prefixes of the 23 G3-S16 pump schemas",
        "count_walk_induction": (
            "after the recorded overlap depth, the increment word is exactly "
            "head++period^(k-k0)++tail; its zero-sum period inserts the recorded count cell "
            "at structural_splice_base+2k, yielding the audited base-plus-ladder zero set"
        ),
        "offset_induction": (
            "each moving balanced prefix has an exact pump-power lasso; its finite bridge "
            "conjugates the pump to opposite DT/TD extensions, and the affine fixed-point "
            "identity gives defect_(n+1)=(2/5)*defect_n"
        ),
        "replay_boundary": (
            "depths 0..64 audit the symbolic two-cell splice and affine recurrence; they are "
            "not a search cutoff"
        ),
        "families": [asdict(row) for row in rows],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    summary = CertificateSummary(
        pump_families=len(rows),
        exact_count_walk_recursions=len(rows),
        base_balanced_prefixes=sum(len(row.base_balanced_cuts) for row in rows),
        infinite_balanced_ladders=len(ladder_rows),
        proper_prefix_action_collisions=0,
        replay_depth=REPLAY_DEPTH,
        certificate_sha256=hashlib.sha256(canonical).hexdigest(),
        status="all 23 pump families are prefix-kernel-free at every depth",
    )
    return payload, summary


def main() -> None:
    """Print the compact summary or canonical full certificate."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    arguments = parser.parse_args()
    payload, summary = certify()
    output: object = payload if arguments.full else asdict(summary)
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()

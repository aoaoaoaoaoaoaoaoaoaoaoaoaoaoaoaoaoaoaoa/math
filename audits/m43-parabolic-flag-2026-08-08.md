# M₄(3) arbitrary-switching exterior-flag audit

**Date:** 8 August 2026

**Status:** arbitrary regular safe switching is controlled; safe return and defect closure remain
open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** reconstruct the proposed normalized `3`-adic flag, verify it on the actual parabolic
atom family, and determine exactly what it removes from the `M₄(3)` tree

## Verdict

The flag survives formalization and is stronger than the report's stated parameter range. For
every natural `β`, every nonempty encoded body, and every regular safe word, the complete
three-coordinate exterior state remains in a two-sector `3`-adic flag. Each leftmost residue
selects its sector even after arbitrary switching and arbitrarily deep common-power
cancellation.

This does not prove safe return. Both sectors meet the bridge wall `u=0`. The gain is exact
orientation on that wall and a verified linear action exposing the atom-specific wound
functionals. The first one is

```text
(12·3^β−1)(u+w)+2v=0
```

for a regular residue-one `b` atom. The next attack must decide reachability of these oriented
wall equations or consume the flag inside the residue-two defect grammar.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`4d2254811976b81b4390fc7e40c9c3e43dcaf6dd`. Its transient report has SHA-256 digest
`943567670362a20d98706303c51ccbb2ba88f4fd14d70daf217b91b2eedf3c18`.

## Exact Exterior State

The new triangle coordinate change is invertible over `ℚ`. For a safe suffix matrix `M`, define

```text
x(M) = C · adj(M)ᵀ · (22,−31,−36)ᵀ = (u,v,w)ᵀ.
```

Lean checks

```text
x(I)=(0,22,9)ᵀ,
x(AM)=T(A)x(M),
det(bridge(ρ,M))=(9ρ/2)u.
```

The multiplication law uses the adjugate identity and remains valid when an atom is singular.
All four regular safe atom families have explicit normalized action matrices `S`, with the
physical exterior transition equal to `3S`.

## Flag

Zero is treated as valuation infinity by explicit relations rather than by the library's value
at zero. The two sectors are

```text
C₀: ν₃(v) > min(ν₃(u),ν₃(w)),
C₁: ν₃(w) > min(ν₃(u),ν₃(v)).
```

The empty state lies in `C₁`. Lean proves the four transition rules

```text
b0, c0 : C₀ ∪ C₁ → C₀,
b1, c1 : C₀ ∪ C₁ → C₁,
```

where `b1` is regular only for positive wait and the actual `c1` proof requires a nonempty
encoded body. The `c1` case is not a first-digit argument: two exact eliminations carry every
possible deeper cancellation. The formal proof isolates that algebra in the reusable theorem
`cOneElimination_flag`.

Induction proves `exteriorState_safe_word_flag` for an arbitrary regular safe word. A stronger
cons theorem records the leftmost residue, and `exteriorState_safe_word_wall_orientation` says
that on `u=0`:

```text
leftmost residue 0  →  ν₃(w)<ν₃(v),
leftmost residue 1  →  ν₃(v)<ν₃(w).
```

Thus arbitrary switching is no longer an uncontrolled source of valuation cancellation.

## Exact Wound

For the physical residue-one `b` transition with positive wait `j`, Lean computes

```text
u' = −12j((12·3^β−1)(u+w)+2v).
```

It follows, without a side condition on the other coordinates, that `u'=0` exactly when the
displayed linear functional vanishes. Analogous wound extraction for the remaining atom
families is now algebra, while proving that a reachable flagged state avoids or hits a wound is
the mathematical core.

## Adversarial Checks

- The theorem uses the actual Neary values `L` and `M`, not only their residues.
- The `c1` nonempty-body hypothesis is explicit at the public arbitrary-word theorem.
- The singular label `b1,j=0` is excluded by `RegularSafeLabel`; it remains the exceptional atom
  owned by the bridge grammar.
- Common multiplication by `3` is proved sector-invariant rather than silently discarded.
- No finite-cone separation is claimed; the flag's closure may meet the wall, as required by the
  irrational `Q(b,4)` orbit.
- The ambient flag contains wall points. No implication from flag membership to safe return is
  asserted.

## Promotion Boundary

Formalized:

- complete exterior coordinates and exact bridge-wall identity;
- all four physical-to-normalized transition formulas;
- the arbitrary-switching two-sector flag;
- leftmost-residue wall orientation;
- the regular residue-one `b` wound equation.

Not proved:

- open blade contexts realizing the paired Neary coefficient-zero language;
- avoidance or reachability of `u=0` by nonempty safe words;
- either alternating one-defect phase `0|2|1` or `1|2|0`;
- interactions among multiple residue-two defects;
- an arbitrary-word converse or `M₄(3)`.

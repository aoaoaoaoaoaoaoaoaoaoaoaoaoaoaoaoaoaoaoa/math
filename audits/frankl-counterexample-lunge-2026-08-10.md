# Frankl conjecture: counterexample-lunge audit

Date: 2026-08-10

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

The reviewed construction attempt does not produce a Frankl counterexample, improve the
universal abundance constant, or close a previously open class. Its best durable residue is an
exact deletion-blocker normal form. Strengthening the report's local argument gives a sharper
pivot theorem and blocker tax. The proposed rank-three lattice exclusion is correct under the
graded-rank convention, but its statement already appears as a consequence of Tian's finite
height theorem. Colbert's peer-reviewed dimension-two theorem independently corroborates the
reduced low-height case, with a strictness caveat when a bottom member is restored.

The raw shared-chat transcript and report were inspected in `/tmp` and are not repository
artifacts. This audit reconstructs every retained statement independently.

## Normalized Carving

Let `F` be a finite union-closed counterexample on a ground set `U` of size `n`. Adjoining
`∅` preserves every strict inequality `d_i(F)<|F|/2`. No singleton can belong to a
counterexample: if `{i}∈F`, then `A↦A∪{i}` injects the members omitting `i` into those
containing it. The union `U` of all members belongs to `F`.

Thus the normalized family has the form

```text
F = F₀ ∖ R,
F₀ = {∅} ∪ {A⊆U : |A|≥2},
R ⊆ {A⊆U : 2≤|A|≤n−1}.
```

Write `r=|R|` and `r_i=|{A∈R:i∈A}|`. Since

```text
|F₀| = 2ⁿ−n,
d_i(F₀) = 2ⁿ⁻¹−1,
```

exact subtraction gives

```text
2d_i(F)−|F| = n−2−(2r_i−r).
```

Consequently the strict counterexample condition is equivalent, coordinate by coordinate, to

```text
2r_i−r ≥ n−1.                                      (1)
```

Union closure is equivalent to the binary-blocker clauses

```text
C∈R and A,B∈F₀ and A∪B=C  implies  A∈R or B∈R.     (2)
```

Equations (1) and (2), together with the displayed domain of `R`, are an exact Boolean or
integer-programming formulation. They are a reformulation, not a counterexample.

## Pivot Normal Form

The report proves only

```text
|R∩2^C| ≥ 2^(|C|−1)−|C|
```

for a deleted set `C`, by pairing complementary proper subsets. Full union closure gives a
strictly stronger and locally sharp statement.

**Pivot theorem.** Condition (2) holds if and only if, for every `C∈R`, there is a pivot
`x_C∈C` such that

```text
x_C∈A⊆C and |A|≥2  implies  A∈R.                  (3)
```

In particular, if `c=|C|`, then

```text
|R∩2^C| ≥ 2^(c−1)−1.                              (4)
```

To prove necessity, let

```text
G_C = {A∈F₀∖R : A⊆C}.
```

This finite family contains `∅` and is union-closed. Hence `D_C=⋃G_C` belongs to `G_C`.
Because `C` is deleted, `D_C≠C`; choose `x_C∈C∖D_C`. Every retained subset of `C` omits
`x_C`, which is (3). There are `2^(c−1)−1` non-singleton subsets of `C` containing
`x_C`, proving (4).

Conversely, suppose (3) and let retained `A,B` have deleted union `C`. The pivot `x_C`
belongs to `A` or `B`, forcing that retained operand into `R`, a contradiction. This proves
(2). Equality in (4) is locally possible by deleting exactly the non-singleton subsets of `C`
that contain one fixed pivot.

This replaces the report's tax by a bound larger by `c−1` and turns the vague “nonlocal
blocker” into a precise consistency problem for the pivot assignment `C↦x_C`.

## Collision Obstruction

One other report lemma survives unchanged. For distinct `A,B∈F`, put

```text
E(A,B) = {C∈F : A∪C=B∪C}.
```

Choose `x∈B∖A`, exchanging `A` and `B` if necessary. Equality of the two unions forces
`x∈C`, so `E(A,B)⊆F_x`. In a counterexample,

```text
|E(A,B)| < |F|/2.                                  (5)
```

Thus no fixed distinction between two member sets can be erased by half the family. This is
a valid but elementary obstruction to high-collision join constructions.

## Rank-Three Audit

The lattice representation in the report is classical. If `M(L)` is the set of proper
meet-irreducibles of a finite lattice and

```text
Φ(x) = {m∈M(L) : x≰m},
```

then `Φ` is injective, preserves joins as unions, and the frequency of coordinate `m` is
`|L|−|↓m|`. A lattice counterexample would therefore satisfy

```text
2|↓m|>|L|  for every m∈M(L).                       (6)
```

The report's incidence count correctly shows that no graded rank-three lattice satisfies (6):
if there are `v` atoms and `b` coatoms and coatom `c` contains `k_c` atoms, then (6) gives
`2k_c>v+b−2`; every atom must lie below at least two coatoms; and two distinct coatoms share
at most one atom. Hence

```text
Σ_c choose(k_c,2) ≤ choose(v,2)
```

but the first two facts give a strict reverse inequality when `b≥3`; the cases `b≤2` are
immediate. Proper elements that are simultaneously atoms and coatoms already violate (6), so
the same conclusion holds without silently assuming gradedness.

This is not a new class theorem. In set language, remove the bottom member from a rank-three
lattice family. The remaining union-closed family has maximum chain cardinality at most three,
so Tian's 2022 theorem supplies a coordinate in strictly more than half of those remaining
members. Restoring the bottom preserves the half-frequency conclusion because
`2d>|L|−1` implies `2d≥|L|`. Colbert's Theorem 3.17 independently proves non-strict
abundance for the corresponding dimension-two family, even in the infinite setting. That
non-strict statement alone leaves one parity case when the bottom is restored; it corroborates
the low-height geometry but is not a substitute for Tian's strict finite conclusion or the
report's independent incidence count.

## Rejected Inferences

- Deleting all coatoms is an ansatz, not a forced first step. Its exact-half bias does not show
  that a counterexample must be a repair of that seed.
- The permutation-pivot calculation classifies only the minimal blocker generated by a
  fixed-point-free permutation. It does not exclude arbitrary pivot assignments or blockers
  with additional deletions.
- One majority-layer cascade at `n=13` does not prove that every local repair fails.
- The constant-cross-top phase count is correct for its stated disjoint phase model, but does
  not constrain general join semilattices.
- The cyclic seven-block example merely regenerates the singleton-free Boolean threshold
  family; it supplies no compressed join construction.
- “Rank at least four” is a known necessary height condition. An inflated `B₃` shape is a
  heuristic ansatz, not an equivalent form of either the blocker conditions or a general
  counterexample.
- An intermediate message mentioned a seven-point, 29-set “deficit concentrator,” but supplied
  no family, multiplicities, closure proof, or demultiplexing map. It has no evidentiary value.

## Operational Residue

The only live lane opened by this review is to combine the pivot clauses (3) with the global
bias inequalities (1). A successful double count would have to show that every consistent
pivot assignment forces some coordinate below the required deletion bias. Until such an
inequality appears, SAT or MILP search over (1)–(3) is reconnaissance rather than a plausible
counterexample theorem.

## Sources

- [Tian, *Union-closed Sets Conjecture Holds for Height H(F) ≤ 3 and H(F) ≥ n − 1*](../references/tian-2022-height-union-closed.md)
- [Colbert, *Chain Conditions and Optimal Elements in Generalized Union-Closed Families of Sets*](../references/colbert-2026-chain-conditions-union-closed.md)
- [Bruhn and Schaudt, *The Journey of the Union-Closed Sets Conjecture*](../references/bruhn-schaudt-2015-journey-union-closed.md)

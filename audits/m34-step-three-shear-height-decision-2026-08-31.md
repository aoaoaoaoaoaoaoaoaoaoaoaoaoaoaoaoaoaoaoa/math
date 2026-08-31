# Step-Three Shear Height-Decision Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `7d85f85` on `wave3-m34-ucb`

**Salvage record:** `D2-D09`

## Verdict

The orbit of `[1:1]` under the integral step-three shears

```text
A=[[1,3],[0,1]],       B=[[1,0],[3,1]]
```

is decidable by a finite Archimedean search. If a nonidentity reduced word with
`k` alternating nonzero syllables reaches a primitive integral target pair of
height `H`, then

```text
2^k ≤ H,               |eᵢ|≤H for every syllable exponent eᵢ.       (1)
```

The bounds are Lean-checked and apply to projective equality, not only equality
of complete matrices. They decide the explicit `G3-O28` Borel-coset family even
though one displayed no-instance is invisible in every finite quotient of its
natural `S`-arithmetic ambient group.

This is not a decision theorem for general `UCB₂(S)`. The proof uses the equal
step size three, the fixed source `[1:1]`, and the alternating free-product normal
form.

## Integral Euclidean Growth

Write an integral homogeneous point as `(m,n)` and put

```text
h(m,n)=max(|m|,|n|).
```

The two signed syllable actions are

```text
A^e(m,n)=(m+3en,n),    B^e(m,n)=(m,n+3em).              (2)
```

Suppose `|m|≤|n|` and `e≠0`. The reverse triangle inequality gives

```text
|m+3en| ≥ 3|e||n|−|m| ≥ 2|n|.                           (3)
```

Thus `A^e` at least doubles height and leaves the first coordinate strictly
dominant. The transposed statement holds for `B^e` when `|n|≤|m|`. The same
estimate also gives

```text
|e|≤h(A^e(m,n))        or        |e|≤h(B^e(m,n)),        (4)
```

because the unchanged dominant input coordinate is nonzero.

A reduced nonempty word alternates `A`- and `B`-syllables. The source `(1,1)`
accepts either final factor. After that factor acts, strict dominance makes the
opposite factor satisfy the hypothesis of (3); induction propagates this through
the whole word. This proves (1), including the bound on every earlier exponent by
the final height.

Lean formalizes the one-step estimates in `shearPair_doubles_height` and
`shearPair_exponent_natAbs_le_height`, then the alternating induction in
`reducedPairAction_power_le_height` and
`reducedPairAction_exponents_le_height`.

## Projective Normalization

`reducedMatrixProduct_mulVec_pairVector` identifies the recursive pair action
with multiplication by the literal integral shear product. Every such product
has determinant one. Mathlib's `SL₂` coprimality theorem then gives

```text
gcd((w·(1,1))₁,(w·(1,1))₂)=1.                            (5)
```

Two coprime integral pairs on the same projective ray differ only by a sign.
The Lean proof constructs their common scale from a Bézout identity, observes
that the scale divides both coordinates of a coprime pair, and concludes that it
is the integer unit `±1`. Consequently a projective hit on primitive target
`(a,b)` has endpoint height `max(|a|,|b|)`, with no hidden rational scale.

Theorems `reducedMatrixProduct_det`, `reducedPairAction_isCoprime`,
`coprime_pairs_eq_or_neg_of_cross_eq`, and
`finite_search_bounds_of_projective_hit` check this normalization seam.

## Decision Procedure

Given a rational target, compute its coprime integral representative `(a,b)` and
`H=max(|a|,|b|)`. Check the identity word separately. For a nonidentity hit,
enumerate only the alternating reduced words satisfying

```text
2^k≤H,                 0<|eᵢ|≤H.                         (6)
```

There are finitely many choices: two possible first factors, finitely many
syllable counts, and finitely many signed exponents at each position. Evaluate
each word on `(1,1)` and compare with `(a,b)` and `(-a,-b)`. The projective theorem
proves completeness of this enumeration. No complexity claim is made for this
exhaustive algorithm.

For the `G3-O28` target `[7:10]`, `H=10`, so every hypothetical nonidentity hit
has at most three syllables and every exponent has absolute value at most ten.
The earlier ping-pong gap already rejects this target; (6) supplies a complete
algorithm for every rational target in the same fixed orbit problem.

## Relation To Profinite Blindness

`G3-O28` proves that the particular empty coset represented by `[7:10]` meets the
shear group in every finite quotient of `Γ₀(3;ℤ[1/19])`. `D2-D09` does not weaken
that theorem. It uses an infinite Archimedean invariant which no finite quotient
retains. Together the records show:

```text
finite ambient quotients are incomplete; pair height is complete for this family.
```

The profinite ghost therefore cannot serve as a hard instance for general
`UCB₂(S)`. It remains a sharp obstruction to one certificate class.

## Literature Boundary

Chorna, Geller, and Shpilrain prove peak reduction for complete matrices in
`⟨A(k),B(k)⟩`, `k≥2`, and derive a matrix-membership algorithm which recovers the
word. Han, Masuda, Singh, and Thiel give continued-fraction matrix-membership
criteria for the symmetric and asymmetric shear groups. Neither theorem decides
whether some group matrix maps one projective point to another. The present
height proof closes that existential fibre only for the fixed-source step-three
family above; the external papers are prior art, not proof premises.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every reduced syllable doubles height from `[1:1]` | promotion | Lean-checked alternating induction |
| Syllable count and every exponent are bounded by target height | promotion | Lean-checked projective theorem |
| The fixed step-three shear orbit of `[1:1]` is decidable | promotion | finite exhaustive algorithm from the formal bounds |
| The `G3-O28` no-instance is algorithmically hard because finite quotients fail | rejected | height decides the complete fixed orbit |
| The cited matrix-membership algorithms already decide the orbit fibre | rejected | their input is one complete matrix |
| General non-elementary `UCB₂(S)` is decidable | open | no comparable height normal form for arbitrary generators and source |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: the explicit step-three shear family as a candidate hard UCB₂(S) residue.
SHARPENED: G3-O28 is a certificate obstruction, not evidence against decidability;
           its own profinite-blind no-instance has a complete Archimedean decision.
REMAINS: obtain a height/continued-fraction normal form for arbitrary non-elementary
         rational generators, or prove that no effective global descent exists.
```

## Artifacts

- [`ShearEuclidean.lean`](../MatrixMortality/ShearEuclidean.lean)
- [Chorna--Geller--Shpilrain matrix peak reduction](../references/chorna-geller-shpilrain-2017-two-generator-subgroups.md)
- [Han--Masuda--Singh--Thiel continued-fraction membership](../references/han-masuda-singh-thiel-2024-subgroup-membership.md)

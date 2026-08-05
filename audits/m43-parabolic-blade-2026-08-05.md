# M₄(3) parabolic-blade audit

**Date:** 5 August 2026

**Status:** formalized open-root mechanism and atom grammar; no `M₄(3)` theorem

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** replace the paired compiler's toggle and external rank-one separator by one open
generator, while proving that every zero word is an intended scalar witness

## Verdict

The finite-order monomial blade is no longer the live candidate. Its exact projective boundary
has a closed ternary-residue obstruction, although the report's “lawful closed context” grammar
has not been promoted to a repository type. The parabolic replacement is real and substantially
stronger: Lean now checks its toggle action, nonzero rank-one blade, every incomplete-root atom,
the unique singularity, all one-step annihilator guards, and the impossibility of a zero through
only two singular incidences.

Formalization exposed a sharper reduction absent from the external report. Any arbitrary chain

```text
R M₁ R M₂ ⋯ Mₖ R
```

is zero exactly when a corresponding product of `2 × 2` bridge matrices is zero. The unbounded
malformed-word problem is therefore an exact two-dimensional incidence problem, not an opaque
three-dimensional mortality problem.

`M₄(3)` remains open. Two obligations remain coupled: construct open left and right contexts
whose blade boundaries recognize exactly the paired Neary coefficient, and prove that the
resulting bridge word vanishes only through the intended pair of rank-one punctuation factors.

## Reconstructed root

In the basis used by `PairedCompression`, write the common data image as `JFₓ` and put

```text
Sρ = [[0, -1, 0,   0],
      [1, -1, 0,   0],
      [0,  0, 1,   0],
      [x,  y, 2/3, 1]],

x = (114ρ - 11)/96,
y = -(38ρ - 11)/32,
ρ = 3^β.
```

Exact multiplication gives

```text
Sρ³ = I + 2E₃₂,             Sρ³J = TJ.
```

The physical root is `B Sρ B⁻¹`. Lean proves that its cube acts as the paired toggle on both
data generators and that every root power is invertible. This is deliberately weaker than the
false equation `Sρ³=T`: equality is required only after the common image injection `J`.

For the native `b` flank, define `R=F_b Sρ J`. The tuned atom satisfies

```text
R² = (1/32) c v,

c = [18(144ρ+35), 648ρ, 1026ρ+385]ᵀ,
v = [12ρ-1, -3(4ρ-1), 8].
```

Lean proves `rank R=2`, the displayed factorization, both eigenray identities, and that the
physical word `G_b S G_b S G_b` is a nonzero outer product after conjugation. Thus the mixed
word is genuinely rank one; no empty or zero punctuation has slipped through the construction.

## Complete atom grammar

For `x∈{b,c}` and any gap `r≥0`, let

```text
Q(x,r) = Fₓ Sρʳ J.
```

Since `Sρ³=I+2E₃₂` with square-zero drift, each residue class modulo three is affine in
`j=⌊r/3⌋`. Lean checks all six determinant pencils. Their consumed conclusion is the exact
classification

```text
det Q(x,r)=0  ↔  x=b and r=1.
```

This holds for every `β` and every nonempty body, hence throughout the admissible Neary family.
Every other atom is a unit. The unique singular atom `R=Q(b,1)` has rank two; no atom kills its
column `c`, and its row `v` kills no atom. Rank subadditivity then proves

```text
R M R ≠ 0
```

whenever `M` is any product of regular atoms. Consequently a zero atom word needs at least three
occurrences of `R`.

## Bridge contraction

The formalizer factored the exceptional atom as

```text
R = A B,

A = [[36ρ-9/4, 18],
     [9ρ,       0 ],
     [57ρ/4-11/8, 11]],

B = [[1, -1,  0],
     [0, 1/4, 1]].
```

For `ρ≠0`, `A` has a checked left inverse and `B` a checked right inverse. Define the bridge of
an arbitrary `3 × 3` middle matrix by

```text
Kρ(M) = B M A.
```

Associativity gives

```text
R M₁ R ⋯ Mₖ R = A · Kρ(M₁)⋯Kρ(Mₖ) · B.
```

The one-sided inverses make the converse exact:

```text
R M₁ R ⋯ Mₖ R = 0  ↔  Kρ(M₁)⋯Kρ(Mₖ)=0.
```

This is formalized for lists of completely arbitrary middle matrices, not merely atom products.
For the candidate semigroup the `Mᵢ` are maximal regular atom blocks. The first possible
malformed zero, with three exceptional atoms, is therefore exactly a product of two `2 × 2`
bridges. Adjacent exceptional atoms correspond to the singular bridge `Kρ(I)` and produce the
intended rank-one punctuation.

## Hostile audit

The external report was treated as conjectural. A separate exact SymPy reconstruction checked,
over symbolic rational parameters:

- the finite-order and parabolic root powers;
- the generic tuned determinant and second characteristic coefficient;
- the nonzero rank-two minor;
- the native `b` factorization and both eigenrays;
- all six infinite determinant pencils.

For the diagnostic instance `β=3`, body `bb`, exact searches found no boundary alignment through
three atoms with gaps `0≤r≤12`, no singular regular-block bridge through four atoms over the same
bounded gap alphabet, and no zero word in the earlier bounded atom census. These are
falsification probes only and carry no theorem status.

The report's claims were classified as follows.

| Claim | Disposition |
| --- | --- |
| Explicit parabolic root and native tuning | promotion; formalized |
| Rank-one physical blade | promotion; formalized and proved nonzero |
| Unique singular atom for all gaps | promotion; formalized |
| All one-step guards and two-incidence safety | promotion; formalized |
| Arbitrary exceptional chains reduce to `2 × 2` bridge words | new promotion from local formalization |
| Closed-residue obstruction for the monomial blade | audited arithmetic; not formalized because its context grammar is not yet an exact repository object |
| Signed-rational-digit and semisimple-monomial exclusions | bounded in scope; not promoted onto the live parabolic path |
| “The only surviving cube-root lane is parabolic” | rejected as stated: the report excludes one semisimple monomial family, not every semisimple root or mixed macro |
| Open-context boundary realization and arbitrary-word isolation | open |

## Exact wound

```text
MASTER VERDICT: still open
REMOVED: rank-one existence, infinite gap classification, every one-step guard,
         and the opaque three-dimensional formulation of multi-R cancellation
REMAINS: open boundary realization plus mortality/isolation of the induced 2 × 2 bridge language
DISTANCE: construct contexts U,V and prove their bridge zero set equals exactly the paired
          Neary coefficient-zero language; or prove that no such contexts can exist
```

## Checked artifacts

- [`MatrixMortality/ParabolicBlade.lean`](../MatrixMortality/ParabolicBlade.lean)
- [`MatrixMortality/RankOne.lean`](../MatrixMortality/RankOne.lean), whose outer-product laws are
  now dimension-polymorphic rather than duplicated for this blade
- `ParabolicBlade.*` entries in [`AxiomAudit.lean`](../AxiomAudit.lean)

The former monomial audit remains
[`m43-cube-root-incidence-2026-08-05.md`](m43-cube-root-incidence-2026-08-05.md). Raw model
transcripts, symbolic scripts, and the next external prompt remain transient under `/tmp`.

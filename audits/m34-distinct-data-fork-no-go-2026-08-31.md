# M₃(4) Distinct-Data Fork No-Go Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `b46c0b1` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseSeparatedForkNoGo.lean`](../MatrixMortality/TransverseSeparatedForkNoGo.lean)

## Verdict

The `G3-C06` distinct-data candidate cannot represent the paired zero language of the fixed body
`bcbc`, for any rational source parameter and any choice of row and column. The obstruction is
uniform away from source zero and an exact product collision closes the exceptional fibre.

This kills the candidate generator, not every nonprojective rank-two architecture. Its retained
infinite carriers, coefficient section, and local terminal/near-fork separation remain correct.

## Terminal-Fork Quotient

Let `F₀(s)` and `F₁(s)` be the products of the flat and nested four-stroke null blocks. Every
stroke product has zero third column, so its action factors through the first two coordinates.
Lean computes four two-dimensional stroke quotients and their block products

```text
Q₀(s) = Q_bbb Q_cbc Q_bbb Q_cbc,
Q₁(s) = Q_bbb Q_bcb Q_cbb Q_cbc.
```

Both block determinants are

```text
det Q₀(s) = det Q₁(s) = 1296s⁸.
```

The commutator determinant factors as

```text
det(Q₀Q₁−Q₁Q₀) = −144s⁶ c(s)² p(s),

c(s) = 8s³−23s²+11s−2,

p(s) = 5120s⁹+2080s⁸−24796s⁷+50600s⁶−52007s⁵
       +33053s⁴−12661s³+2956s²−400s+24.
```

Neither nonconstant factor has a rational root. The formal proof uses the rational-root theorem
and reduction modulo a prime whose image has no root: `c` modulo `7` and `p` modulo `13`. The
finite residue checks use kernel reduction through `decide`, not an external oracle or
`native_decide`.

Consequently `Q₀,Q₁` have no common rational invariant line for every `s≠0`. Lean proves the
consumed two-dimensional lemma directly: if one row annihilates a nonzero column and both of its
images under `Q₀,Q₁`, then the column would be a common eigenvector, contradicting the nonsingular
commutator.

## Three Terminal Forks

Let `A(s)` be the product of the fixed two-stroke prefix `cbc,bcb`, let `T=diag(1,2,3)`, and fix
arbitrary boundary vectors `r,γ`. Put

```text
ℓ = rA(s)F₀(s),            q = head(Tγ).
```

The three bit histories

```text
[false],       [false,false],       [false,true]
```

are all certified `bcbc` terminal histories. Same-zero recognition would therefore give

```text
head(ℓ)·q = 0,
head(ℓ)·Q₀q = 0,
head(ℓ)·Q₁q = 0.
```

If `q=0`, then the first two coordinates of `γ` vanish. The one-letter control `b` is consequently
a target zero, although its paired source coefficient is nonzero.

If `q≠0`, the nonsingular commutator forces `head(ℓ)=0`. The third coordinate of `ℓ` is already
zero. Moreover the prefix row `rA(s)` has zero third coordinate, and `det Q₀(s)≠0`; hence
`rA(s)=0`. The raw prefix control without the final toggle is then a target zero, although Lean
certifies that its paired source coefficient is nonzero. This proves failure for every `s≠0`.

## Exceptional Source

At `s=0`, Lean multiplies the matrices exactly and obtains

```text
X₀(c t b c b c b b b) = X₀(c t b c b t c b t).
```

The right word is the canonical terminal `bcbc` prefix. The left word has nonzero paired source
coefficient. Product equality transfers any target zero between them, so no row and column can
give the correct zero language at `s=0` either.

## Scope

The formal theorem quantifies over every rational parameter `s` and all rational row-column pairs
for the exact generator of `G3-C06`. It proves failure on the fixed admissible body `bcbc`, which
is sufficient to reject this generator as a uniform arbitrary-body compiler.

It does not prove that `M₃(4)` is decidable, that every distinct rank-two perturbation fails, or
that nonprojective infinite carriers are semantically useless. A survivor may change the second
data map, the toggle, the terminal geometry, or the source embedding. Any repair must break the
three-fork quotient obstruction as well as the zero-source collision while preserving an
infinite carrier section and the complete arbitrary-word converse.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The four stroke quotients give the exact first-two-coordinate actions | promotion | Lean action theorems |
| Both fork-block quotient determinants equal `1296s⁸` | promotion | Lean determinant theorems |
| The commutator determinant has the displayed factorization | promotion | Lean ring normalization |
| `c` and `p` have no rational roots | promotion | rational-root theorem plus mod-`7`/mod-`13` certificates |
| The three terminal forks force the nonzero-source contradiction | promotion | Lean theorem `no_bcbc_sameZero_of_source_ne_zero` |
| The displayed source-zero products are equal with opposite source semantics | promotion | Lean product and paired-coefficient theorems |
| The `G3-C06` generator recognizes arbitrary paired sources | rejected | Lean theorem `no_bcbc_sameZero` |
| Every nonprojective three-state architecture fails | open | the theorem fixes the exact `G3-C06` controls |
| `M₃(4)` follows | rejected | other transverse, common-kernel, and full-rank architectures remain |

## Formal Validation

The formal owner compiles warning-free under the repository toolchain. Publication-facing
declarations are listed in [`AxiomAudit.lean`](../AxiomAudit.lean). Their selected transitive axiom
outputs contain only the reviewed standard axioms. No proof aperture, project axiom, unsafe
declaration, linter suppression, or external certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
KILL: the exact G3-C06 distinct-data generator fails bcbc same-zero for every rational parameter.
NONZERO SEAM: three certified terminal forks force a false zero through an irreducible P¹ action.
ZERO SEAM: ctbcbcbbb and terminal ctbcbtcbt have the same target product.
SURVIVOR: change the controls or terminal geometry; row/column retuning cannot repair G3-C06.
```

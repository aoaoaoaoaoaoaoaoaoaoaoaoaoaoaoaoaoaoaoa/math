# M₅(3) primitive-normalization collapse audit

## Boundary

This audit checks one exact abstract width-six local carrier. It proves that canonical
`(R_c,D_b)` primitive normalization followed by a full-channel singleton `D_c` can contract
Farey height on both steps and across the two-step window. It does not show that the seed is an
`MM-O29` seed, reachable from the encoded entry, or a pole.

## Witness

For canonical body `b c⁴` and block `(R_c,D_b)`, the checked codes are

```text
P=23911928,
V=23911568,
A=19683.
```

The seed is `(1915861521737,27626)`. It lies above `H`, and its inverse canonical adjugate has
content `166177436936869872`. Primitive sign normalization gives `(200420,200417)`. Applying the
existing forward carrier recurrence returns the seed with scale `−10932`; the product of this
scale with the inverse content equals the exact determinant product required by the block.

## Contraction channel

The primitive intermediate carrier satisfies `d<n`, `gcd(n,d)=1`, `h∣n`, `gcd(r,d)=1`, and
`gcd(n−d,3μ)=3`. Its raw singleton-`D_c` pair has gcd `3H`, and division by that complete content
gives `(727,160268)`.

Lean evaluates the Farey heights and proves

```text
F(200420,200417) < F(1915861521737,27626),
F(727,160268) < F(200420,200417),
F(727,160268) < F(1915861521737,27626).
```

Thus neither universal adjacent expansion nor universal two-step expansion survives primitive
normalization under the local hypotheses alone.

## Scope seam

The witness starts from an abstract rational carrier above the terminal ray. No theorem connects
it to the polynomial `MM-O29` seed cores, the encoded-entry orbit, or a target pole. It therefore
does not defeat a target-sensitive theorem using `MM-S92`; it defeats only the broader local
Farey claim.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterNormalizationCollapse.lean`](../MatrixMortality/SwappedSetterNormalizationCollapse.lean).

The source compiles without warnings. Its namespace passes the default linters; the public
theorem is listed in `AxiomAudit.lean`; the reviewed snapshot uses only standard axioms; and the
aperture scan is empty.

## Authorship

GPT-5.6 Sol, elicited by @eternalism_4eva.

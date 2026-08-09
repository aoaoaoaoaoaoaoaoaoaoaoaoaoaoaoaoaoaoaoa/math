# M₄(3) retuned semantic-boundary audit

**Date:** 8 August 2026

**Status:** retuned three-generator boundary formalized; fixed right-annihilator orbit and
arbitrary-word converse open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** realize the four-tile Neary terminal language inside a literal word over three
`4 × 4` generators without importing external boundary selectors

## Verdict

The retuned report survives and is stronger after reconstruction. A fixed rational open root
has exactly one singular reduced atom: the `b` atom at gap two. Complete gaps zero and three
evaluate in order to a sparse ternary side matrix. Factoring the exceptional atom through a
two-dimensional bridge makes its determinant vanish exactly when

```text
spell upper word ++ marker = spell lower word.
```

The bridge is embedded in a literal physical context word over the root and two data generators.
One fixed `2 × 2` minor of that `4 × 4` product is a nonzero scalar multiple of the bridge
determinant. Fixed retractions recover the bridge from the physical product, so the context is
never zero. On a terminal match it is a nonzero outer product with fixed right row

```text
(-1, (15·3^β+3)/2, 28, 24).
```

Consequently, completing the forward mortality reduction is exactly a right-annihilator orbit
for this row. A continuation composed only of complete gaps preserves its first coordinate
`-1`; any annihilator must use an incomplete root gap. This does not prove `M₄(3)`: existence of
such a fixed continuation and soundness for every malformed generator word remain open.

## Source Lock

The four parallel reports read branch `m43-cube-root-incidence` at
`55d633deb47faf334d31debb517dbd8e77c74dec`. Their transient final-report SHA-256 digests were:

```text
arbitrary defect grammar  7aad42d88042917c489e2d005cee962a0372b4c3ca01990640e8d3cdf67d26af
deletion scanners         9b8ededb7e46866f9f35bc7084fa30ceacd38e39b0c840eed152957312086393
retuned boundary          f9df5deddbbf280c248d43e8c80b8ec6e4485a17cfca22eb02d3f0f270290ece
safe-wall attempt         7ac8fe6d8192c3502e514dacd09a468c24a109356adc056d6c550fc38d176c96
```

The first two reports were formalized in the preceding commits. The fourth produced no
mathematical result because its solver was unavailable; it changes no durable claim.

## Checked Construction

The sparse digit map is `true ↦ 0`, `false ↦ 1`. Its ordinary integer value is not injective
across lengths, but the affine fraction

```text
(19·sparseCode(z)+1)/3^|z|
```

is injective on words ending in `false`: the numerator is `2 mod 3`, so cross multiplication
first forces equal lengths and then equal base-three digits. Every lower spelling and every
positive-width marker has this suffix.

The fixed root satisfies `S³ = drift(1)` and the required restricted identity `S³J = TJ`.
Lean proves all six determinant pencils for `FₓSʳJ`; under positive deletion width and nonempty
body their unique zero is `(x,r)=(b,2)`. No global equality `S³=T` is used.

For each complete Neary tile, gap zero encodes erasure and gap three encodes a rule. Their
reduced products are exactly

```text
[[1, sparseCode(U), 2·sparseCode(V)],
 [0, 3^|U|,        0],
 [0, 0,             3^|V|]].
```

The exceptional atom factors as `AB`; `K(M)=BMA`. Lean proves the determinant identity and its
terminal-match converse, including the empty word. The literal context

```text
G_b S² (complete tile word) G_b S² G_b
```

equals `J A K(M) B F_b`. Its rows 2–3 and columns 1,4 have determinant
`-2052·3^β·det K(M)`. Explicit left and right inverses recover `K(M)` from the context, excluding
premature zero. The paired-control corollary identifies the same minor zero set with
`pairedCoefficient`.

## Independent Checks

Exact symbolic recomputation verified the root cube, both exceptional factorizations, all six
determinant pencils, the bridge determinant, the fixed minor, and the fixed terminal row.
Bounded exact searches found no right annihilator through depth fourteen, covering approximately
7.17 million projective states. These searches are falsifiers only and are not theorem evidence.

The report's uniform denominator clearing by `24` is algebraically valid but was not retained as
new Lean machinery: the repository already owns generator-scaling transports, and no mortality
witness yet consumes the integralized family.

## Remaining Enemy

The retuned lane has two independent obligations:

1. find a word `Z` over the same three generators, independent of the unknown terminal history,
   with `terminalRow β ᵥ* Z = 0`; complete-gap words are formally excluded;
2. classify every arbitrary word in the retuned generator semigroup and prove that any zero
   product contains a genuine terminal context followed by a lawful annihilator, or exhibit a
   malformed zero and retire the lane.

The original parabolic family remains live: its arbitrary-defect grammar reduces zeros to one
oriented wall incidence, but it has not acquired this sparse semantic realization. The overlap-
queue scanners are independent of both matrix families.

## Artifacts

- `MatrixMortality/ParabolicRetuned.lean`
- `MatrixMortality/ParabolicRetunedBoundary.lean`
- `audits/m43-arbitrary-defect-2026-08-08.md`
- `audits/m43-deletion-scanner-2026-08-08.md`

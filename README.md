# Fixed-Boundary Correspondence and Matrix Compression

This repository proves that binary-target `GPCP(4)` is undecidable and derives undecidability
of mortality for at most five `3 × 3` integer matrices. Four matrix generators may be
nonsingular and upper triangular; the fifth may be nonzero of rank one over `ℚ`.

Paired-role compression then proves structured scalar zero reachability undecidable for three
`4 × 4` integer matrices and mortality undecidable for four `4 × 4` integer matrices. The
three scalar generators share first column `e₁`; one is a permutation matrix. The fourth
mortality generator is nonzero of rank one over `ℚ`.

Two binary compilers sharpen the two-generator frontier. Paired-channel packing gives scalar
zero reachability for two `6 × 6` integer matrices sharing first column `e₁`. A complete prefix
decoder followed by a common-image restriction gives mortality for two `10 × 10` integer
matrices.

Singular return compression lowers the mortality dimension to nine. An injective
tilted separator preserves the paired scalar zero language, a `3+3+2+1` return realization carries
its returns, and primitive-recursive denominator clearing constructs two `9 × 9` integer matrices.
Zero-block padding preserves mortality in every dimension at least nine.

The complete undecidability chain, from an explicit universal machine through the restricted
tag source and matrix compilers, is machine-checked in Lean 4.

**Author:** GPT-5.6 Sol, elicited by
[@eternalism_4eva](https://x.com/eternalism_4eva).

## Publications

- [Mathematics index](math.html)
- [Matrix mortality landing page](matrix_mortality.html)
- [Matrix mortality glossary](matrix_mortality_glossary.html): canonical definitions and notation
- [Fixed-Boundary Correspondence](m3_5.html): `GPCP(4)` and `M₃(5)`
- [Paired-Role Compression](m4_4.html): `Z₄(3)` and `M₄(4)`
- [Binary Compilers](binary_compilers.html): `Z₆(2)` and `M₁₀(2)`
- [Singular Return Compression](m9_2.html): `M₉(2)`
- [`M₃(5)` technical manuscript](paper/main.pdf)

## Supporting Material

- [Formal verification](FORMALIZATION.md): theorem map, axioms, trust base, and external seam
- [Salvage theorem registry](SALVAGE.md): reusable statements, evidence status, scope guards,
  operational uses, and promotion work
- [`M₃(5)` novelty record](NOVELTY.md): prior art and qualified priority claim
- [`M₄(4)` prior-art investigation](audits/m44-prior-art-2026-07-22.md): convention audit,
  claim ledger, version histories, and search coverage
- [`M₄(4)` adversarial audit](audits/m44-adversarial-audit-2026-07-22.md): correctness verdict,
  applied repairs, formal scope, and external dependency seam
- [Frontier campaign](FRONTIER.md): subsequent research targets
- [Local bibliography](references/README.md): preserved papers and source-specific audit notes

## Verification

The repository pins Lean and mathlib to `v4.33.1`. Run:

```sh
./scripts/check.sh
```

Use `./scripts/check.sh m92` for only the M₉(2) proof closure, or
`./scripts/check.sh publication` for the release gate. Compiled artifacts and successful
verification receipts are cached across worktrees. See [Verification Targets](BUILDING.md)
for target names, cache placement, invalidation, and independent reproduction.

Required host commands are `lake`, `uv`/`uvx`, `rustc`, `rustfmt`, `tectonic`, `xmllint`, `rg`,
`diff`, and GNU `sha256sum`. The script checks the reference corpus; builds and lints Lean;
compares the exact transitive-axiom snapshot; rejects proof escapes and linter suppressions; runs
the auxiliary finite certificates; validates the HTML expositions; and reproduces the
committed PDF byte-for-byte. PDF reproduction requires Tectonic 0.17.0, bundle v33, and
`SOURCE_DATE_EPOCH=1784606400`; the script fixes the latter two and rejects another Tectonic
version.

The audited theorem dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
There are no project axioms or admitted proofs.

## Publication

After committing changes to the exposition or its supporting artifacts, run:

```sh
./scripts/publish.sh
```

This repository then verifies and pushes itself, builds through Eternalist's
site contract, deploys, waits for CloudFront, and compares the live article
with the release build. A normal Git push does not update `eternalist.moe`.

## Priority

Neary's 2013 preprint claimed the same numerical `M₃(5)` bound through a four-pair PCP theorem
not retained in its refereed successor. No accepted prior proof was found.

To our knowledge, after a public-literature search through 22 July 2026, no prior proof
establishes `M₄(4)` or scalar zero reachability for three common-first-column `4 × 4` integer
matrices. The anti-diagonal quotient is standard linear algebra, and the rank-one
scalar-to-mortality separator is prior art. See [NOVELTY.md](NOVELTY.md) and the
[`M₄(4)` investigation](audits/m44-prior-art-2026-07-22.md) for the qualified claims.

To our knowledge, after searches through 24 July 2026, no prior proof establishes `Z₆(2)`,
`R₇(2)`, or `M₁₀(2)`. Generic binary coding, alphabet reduction, and scalar-to-corner transport
are prior art; the qualified technique claims are stated in [Binary Compilers](binary_compilers.html).
The changed-separator compiler strengthens the last bound to `M₉(2)`; any earlier `M₉(2)` result
would also have implied `M₁₀(2)` by zero-block padding.

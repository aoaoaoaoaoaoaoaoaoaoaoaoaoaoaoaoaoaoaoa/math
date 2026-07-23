# Four-Generator GPCP and Small Matrix Mortality

This repository proves that binary-target `GPCP(4)` is undecidable and derives undecidability
of mortality for at most five `3 × 3` integer matrices. Four matrix generators may be
nonsingular and upper triangular; the fifth may be nonzero of rank one over `ℚ`.

Paired-role compression then proves structured scalar zero reachability undecidable for three
`4 × 4` integer matrices and mortality undecidable for four `4 × 4` integer matrices. The
three scalar generators share first column `e₁`; one is a permutation matrix. The fourth
mortality generator is nonzero of rank one over `ℚ`.

The instance-level reductions are machine-checked in Lean 4. Neary's peer-reviewed
restricted-tag universality theorem remains an external dependency of the final undecidability
statements.

**Author:** GPT-5.6 Sol, elicited by
[@eternalism_4eva](https://x.com/eternalism_4eva).

## Publications

- [Mathematics index](math.html)
- [Part I: undecidability of `M₃(5)`](index.html)
- [Part II: undecidability of `M₄(4)`](m4_4.html)
- [Part I technical manuscript](paper/main.pdf)

## Supporting Material

- [Formal verification](FORMALIZATION.md): theorem map, axioms, trust base, and external seam
- [Part I novelty record](NOVELTY.md): prior art and qualified priority claim
- [Part II prior-art investigation](audits/m44-prior-art-2026-07-22.md): convention audit,
  claim ledger, version histories, and search coverage
- [Part II adversarial audit](audits/m44-adversarial-audit-2026-07-22.md): correctness verdict,
  applied repairs, formal scope, and external dependency seam
- [Frontier campaign](FRONTIER.md): subsequent research targets
- [Local bibliography](references/README.md): preserved papers and source-specific audit notes

## Verification

The repository pins Lean and mathlib to `v4.12.0`. Run:

```sh
./scripts/check.sh
```

Required host commands are `lake`, `uv`/`uvx`, `tectonic`, `xmllint`, `rg`, `diff`, and GNU
`sha256sum`. The script checks the reference corpus; builds and lints Lean; compares the exact
transitive-axiom snapshot; rejects proof escapes and linter suppressions; runs the independent
finite falsifier; validates both HTML expositions; and reproduces the committed PDF
byte-for-byte.

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
[Part II investigation](audits/m44-prior-art-2026-07-22.md) for the qualified claims.

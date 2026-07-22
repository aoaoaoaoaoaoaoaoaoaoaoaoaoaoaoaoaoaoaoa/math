# Four-Generator GPCP and Five-Matrix Mortality

This repository proves that binary-target `GPCP(4)` is undecidable and derives undecidability
of mortality for at most five `3 × 3` integer matrices. Four matrix generators may be
nonsingular and upper triangular; the fifth may be nonzero of rank one over `ℚ`.

The new reduction is machine-checked in Lean 4. Neary's peer-reviewed restricted-tag
universality theorem remains an external dependency of the final undecidability statement.

**Author:** GPT-5.6 Sol, elicited by
[@eternalism_4eva](https://x.com/eternalism_4eva).

## Publications

- [Standalone exposition](index.html)
- [Technical manuscript](paper/main.pdf)

## Supporting Material

- [Formal verification](FORMALIZATION.md): theorem map, axioms, trust base, and external seam
- [Novelty record](NOVELTY.md): prior art and qualified priority claim
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
finite falsifier; validates the HTML; and reproduces the committed PDF byte-for-byte.

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
not retained in its refereed successor. No accepted prior proof was found. See
[NOVELTY.md](NOVELTY.md) for the precise historical claim.

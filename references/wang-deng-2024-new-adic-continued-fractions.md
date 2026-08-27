# Wang and Deng (2024): New Algorithms of P-Adic Continued Fractions

**Citation.** Zhaonan Wang and Yingpu Deng, “Convergence, Finiteness and Periodicity of
Several New Algorithms of p-Adic Continued Fractions,” arXiv:2309.05601v2 (2024).
https://arxiv.org/abs/2309.05601.

- Work identity: arXiv:2309.05601
- Canonical source: https://arxiv.org/abs/2309.05601
- Local artifact: `wang-deng-2024-new-adic-continued-fractions.pdf`
- Version and status: arXiv v2, 3 March 2024; preprint
- Retrieved: 2026-08-06
- SHA-256: `9536b387fa14337bfbcc2cfa557e8116c6b7fe589d1c768977763c578bc37e6d`
- Access and retention: arXiv manuscript; no explicit artifact license was located
- Synopsis basis: full-text inspection of Algorithms 4–6 and Theorems 1–3

## Synopsis

The paper defines several p-adic continued-fraction algorithms whose partial-quotient selector
combines Browkin-style p-adic truncation with a finite phase schedule and, for algebraic input,
trace-based real rounding. It proves p-adic convergence and termination on rational inputs.
The rational proofs establish strict numerator-denominator contraction across bounded blocks;
for Algorithm 6, three successive denominator estimates combine to an eightfold decrease.

For quadratic irrational inputs, Algorithms 4 and 5 are proved ultimately periodic for
`p=2,3`, while Algorithm 6 reaches `p≤7`. The proposed extensions to larger primes are partly
conditional and computational. The results therefore demonstrate that a finite phase selector
can reconcile local p-adic legality with Archimedean block descent, but do not furnish a
universal floor rule for an unrelated rational dynamical system.

## Source Assessment

This is a recent preprint; no peer-reviewed publication was located. The qualitative rational
termination proof is explicit. The precise logarithmic step count should not be imported
without a separate audit: the theorem statements use `⌈ln Q⌉+2`, while the proofs present
block contractions and one concluding asymptotic line whose variables are not fully consistent.

## Project Use

Provides a second bounded-state model for the guard: isolate the maximal Smith branch as one
phase, force the next phase to be nonmaximal, and seek a denominator or height contraction over
the resulting fixed macro. Only the block inequalities, not the stated numerical step bound,
are candidates for reuse.

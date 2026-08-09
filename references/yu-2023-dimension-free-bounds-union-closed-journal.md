# Yu (2023)

**Citation.** Lei Yu, “Dimension-Free Bounds for the Union-Closed Sets
Conjecture,” *Entropy* 25(5), article 767, 2023.

- DOI: https://doi.org/10.3390/e25050767
- Canonical source: https://www.mdpi.com/1099-4300/25/5/767
- Local PDF: `yu-2023-dimension-free-bounds-union-closed-journal.pdf`
  (final journal version)
- Retrieved: 2026-08-08
- SHA-256: `7d5b114fb6ba59dda335f44784105d6cd41579816d00885c582699d4265a51e9`
- License: CC BY 4.0

## Results used

Yu formulates a general coupling optimization `Γ(t)` and proves a finite support reduction
`Γ̂(t)` sufficient for a universal abundance bound. This makes Sawin’s dependent-coupling
improvement finite-dimensional. For `α=0.035` and `t=0.38234`, the paper reports a numerical
value `Γ̂(t) ≥ 1.00000889`, with an optimizer supported on two elementary couplings.

## Audit notes

The implication `Γ̂(t)>1 ⇒ abundance ≥t` is analytic. The proof of Proposition 1 has a
repairable concavity defect: it says that the independent entropy functional is globally concave
and cites Alweiss–Huang–Sellke, Lemma 5, but that lemma proves concavity only among measures of
one fixed mean. Global concavity is false. Before applying the lemma, a coupling of mean `s<t`
can be mixed with `δ_(1,1)` in proportion `(t−s)/(1−s)`. This raises the mean to exactly `t`,
multiplies the marginal and dependent entropy terms by `1−γ`, and multiplies the independent
term by `(1−γ)²`; the objective ratio therefore cannot increase. The extreme-point argument is
then valid on the exact-mean slice. The repair is proved in
[`audits/frankl-yu-reduction-2026-08-08.md`](../audits/frankl-yu-reduction-2026-08-08.md#repairing-the-exact-mean-reduction).

The displayed `0.38234` evaluation is numerical, with no outward-rounded certificate or
exhaustive global-optimization proof supplied. The author’s current publication page likewise
describes the paper as numerically evaluating Sawin’s bound. We therefore do not treat the
source's numerical claim as a rigorously established constant on its own.

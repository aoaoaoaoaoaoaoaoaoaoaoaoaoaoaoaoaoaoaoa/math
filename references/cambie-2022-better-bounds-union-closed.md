# Cambie (2025 revision)

**Citation.** Stijn Cambie, “Better Bounds for the Union-Closed Sets Conjecture
Using the Entropy Approach,” arXiv:2212.12500v2, revised 2025.

- DOI: https://doi.org/10.48550/arXiv.2212.12500
- Canonical source: https://arxiv.org/abs/2212.12500
- Local PDF: `cambie-2022-better-bounds-union-closed.pdf` (arXiv v2)
- Retrieved: 2026-08-08
- SHA-256: `a2fa9302e498b34228091569fb4cdd053a541fcea2b01c70c8110224ac434f85`
- License: CC BY 4.0

## Results used

Cambie reduces Sawin’s mixed-coupling inequality to extremal marginal laws of support at most
three, then combines that reduction with Yu’s coupling decomposition to leave two two-variable
cases. The candidate sharp constants are
`c*=0.3823455333667034` and `α*=0.03560698066…`; the obstruction is the two-point
marginal on `{b,1}` with `b=0.329454738503037…`.

## Audit notes

The paper explicitly calls its computer verification “slightly less rigorous.” Its final claim of a
global minimum rests on Maple local minimization and plots; even v2’s two-variable reduction is
closed by graphical confirmation, not an exact certificate. The source repository’s worksheets
were inspected on 2026-08-08 and exhibit the same methodology. Thus `c*` is a compelling target
and a ceiling for this precise coupling scheme, but not yet the investigation’s rigorous KPI.

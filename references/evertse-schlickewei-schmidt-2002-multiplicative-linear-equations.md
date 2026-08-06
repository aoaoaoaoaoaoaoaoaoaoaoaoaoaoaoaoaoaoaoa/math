# Evertse, Schlickewei, and Schmidt (2002): Linear Equations in a Multiplicative Group

**Citation.** J.-H. Evertse, H. P. Schlickewei, and W. M. Schmidt, “Linear Equations
in Variables Which Lie in a Multiplicative Group,” *Annals of Mathematics* 155, no. 3 (2002),
807–836. https://doi.org/10.2307/3062133.

- Work identity: DOI 10.2307/3062133; arXiv:math/0409604
- Canonical source: https://annals.math.princeton.edu/2002/155-3/p04
- Local artifact: `evertse-schlickewei-schmidt-2002-multiplicative-linear-equations.pdf`
- Version and status: arXiv v1, 30 September 2004; peer-reviewed publication in 2002
- Retrieved: 2026-08-06
- SHA-256: `3c809fcadaddbc08f57045e4f55562c8a379b5fa33d7e83046b63a9c14766e8f`
- Access and retention: postpublication author-distributed arXiv manuscript; no explicit artifact license was located
- Synopsis basis: full-text inspection of the main theorem, definitions, examples, and reduction structure

## Synopsis

Let `Γ` be a subgroup of `(K×)ⁿ` of finite rank `r` over a characteristic-zero field. The paper
gives the uniform explicit bound

```text
exp((6n)^(3n)(r+1))
```

for the number of solutions in `Γ` to `a₁x₁+⋯+aₙxₙ=1` for which no proper subsum vanishes. The
bound depends only on the number of terms and the group rank, not on the coefficients or field.
Degenerate solutions are excluded because vanishing subsums reduce the equation to lower-term
relations and may occur in families.

The theorem is quantitative as a counting statement but does not itself enumerate solutions
from arbitrary input data. Its force requires a uniformly bounded number of additive terms and
a single finite-rank multiplicative group. Allowing the rank to grow with word length destroys
the uniform conclusion.

## Source Assessment

The arXiv posting is a postpublication copy of the Annals article. No correction, withdrawal,
or source-level defect was found.

## Project Use

Can bound nondegenerate terminal equations only after the guard word is compressed into a
bounded-term equation in a fixed-rank multiplicative group; the raw variable-length expansion
does not meet that criterion.

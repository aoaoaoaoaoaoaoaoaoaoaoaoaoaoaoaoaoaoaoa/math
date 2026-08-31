# M₉(2) moving-tail transfer-Hankel audit

Date: 2026-08-31
Record: `MM-O25`
Evidence: formalized

## Hypotheses

Let two matrix-valued sequences over a field have independent exact linear realizations

```text
Sᵣ=VAʳU,       Qᵣ=V_qCʳU_q,
```

of dimensions `n` and `h`. Assume `Sᵣ=Qᵣ` for every `r>m`. At time `m`, assume the difference
`S_m−Q_m` has a nonsingular `3 × 3` minor. The comparison sequence `Q` may be nonconstant and
need not be rank one.

Then

```text
3(m+1) ≤ n+h.
```

The theorem assumes exact equality of matrix moments and an independently exact linear tail.
It does not apply to a tail specified only by zero equivalence, an infinite-Hankel-rank tail, or
nonlinear boundary behavior.

## Full reversed-time section

Subtract the comparison sequence, `Dᵣ=Sᵣ−Qᵣ`. For every `0≤p,q≤m`, select the three certified
coordinates of

```text
K_(p,i),(q,j) = D_(p+m-q)(i,j).
```

Natural subtraction is defined because `q≤m`. When `q<p`, the time index exceeds `m`, so
`D_(p+m-q)=0`. Every diagonal block is the same nonsingular minor of `D_m`. The
`3(m+1) × 3(m+1)` section `K` is therefore block triangular and nonsingular.

The two moment factorizations give

```text
K = L_S R_S - L_Q R_Q
  = [L_S  -L_Q] [R_S; R_Q].
```

The intermediate space has dimension `n+h`, proving the inequality. Unlike the rank-one
restoration in `MM-O24`, no coordinate estimate is inferred from the pointwise ranks of `Qᵣ`;
the exact linear realization dimension `h` is the relevant tax.

## Paired-role consequences

Suppose `m≥3`, `h≤2`, and `Q_m=P′`. If `S_m` is any nonzero rescaling of the paired benchmark
toggle, data-`b`, or data-`c` role, the deviation minors checked in `MM-O24` have rank three.
Thus

```text
12 ≤ 3(m+1) ≤ n+h ≤ n+2,
```

and `n≥10`. Lean checks all three role-specific corollaries.

More generally, a nine-state realization with a last rank-three exception at time `m` requires

```text
h ≥ 3(m+1)-9.
```

Spacing a role farther out therefore increases the required tail complexity. This does not
exclude a sufficiently large independently realized tail, nor does it address the consecutive
positions `0,1,2` with a moving tail.

## Formal boundary

`MatrixMortality/MovingTailHankel.lean` checks:

- block triangularity and nonsingularity for all `m+1` reversed time blocks;
- exact factorization of the difference section through the sum of the two state spaces;
- the generic cardinal inequality `3(m+1)≤n+h`;
- the cut `m≥3`, `h≤2` implies `n≥10`;
- the specialized toggle, data-`b`, and data-`c` conclusions when `Q_m=P′`.

No finite scan or determinant search is used beyond the already formalized benchmark deviation
minors. The surviving transfer seam requires a tail with sufficient exact realization dimension,
changed nonzero moment values, or nonlinear same-zero semantics.

# M₉(2) changed-separator transfer audit

Date: 2026-08-31
Record: `MM-C05`
Evidence: formalized semantic core; audited symbolic realization

## Result

The moving-tail seam left by `MM-O25` is real. Write

```text
r = 3^β,
V = ternaryCode(nearyLower β body (rule c)),
K = 3^|nearyLower β body (rule c)|.
```

Set

```text
D = 9K²r² + 2K²r − K² − 18KVr² + 2KV
    − 9Kr² − 6Kr − 47K + 48V + 96,
a = 2K(K−3)/D,
z = 2K(K−3V)/D,
s = K(3r−1)(K−2V−1)/D,
x = (a,z,z,z).
```

For the paired controls `T,D_b,D_c`, trailing-toggle column `u`, and changed separator
`R=ux`, consider

```text
M₀=T,  M₁=D_b,  M₂=D_c,  Mₙ=s^(n−3)R  for n≥3.
```

On the nondegenerate locus used by the displayed chain coordinates, this series has an exact
nine-state realization. The transition is similar to

```text
J₃(0) ⊕ J₃(0) ⊕ J₂(0) ⊕ [s].
```

The retained checker constructs input and output matrices symbolically. It subtracts the
one-state geometric mode, factors the final residual through two length-three chains, isolates
one length-two remainder, and verifies the remaining time-zero factorization. The decisive exact
identities are

```text
det Q = −2Kr(K+3V−6)/((3r−1)(K−2V−1)),
E₂₃ = 216(K−V−2)/(K(K+3V−6)).
```

The exceptional locus `K−V−2=0` changes the nilpotent chain partition; the Hankel rank still
does not exceed nine, but the displayed `3+3+2+1` coordinates are not a total parameterization
there. A uniform emitted compiler must either prove the universal Neary bodies avoid this locus
or branch to another rational basis.

## Same-zero theorem

The ratio of the three uniform row coordinates to the affine coordinate is

```text
q = z/a = (K−3V)/(K−3).
```

For any binary word `w`, define

```text
F_q(w)=ternaryCode(w)+q·3^|w|.
```

When `q<−3/2`, longer words lie in strictly lower value bands, so `F_q` is injective. Lean proves
this for arbitrary finite binary words. It also proves from Neary's lower-`c` syntax that

```text
5K−9 < 6V,
```

hence `q<−3/2` for every `β` and body. A paired phase vector has coordinates
`(h,ℓ,u,0)` or `(h,0,u,ℓ)`. Therefore the uniform row `(1,q,q,q)` evaluates both phases as

```text
F_q(upper)−F_q(lower).
```

Its scalar is zero exactly when the canonical affine-head scalar is zero. Lean proves this
pointwise for every paired control word and after trailing-toggle absorption, then lifts it to
existential nonempty zero reachability. This is a total arbitrary-word same-zero theorem, not a
finite search.

## Exact benchmark

At `β=3`, body `bb`, the parameters reduce to

```text
a = −21552885/62516483831,
z = 1109707857/1750461547268,
s = 5386449780/437615386817,
q = −18793/10220.
```

The checker reconstructs the canonical nine-state realization exactly. Its transition ranks are
`6,3,1` at powers `1,2,3`, its input and output both have rank four, and a finite block-Hankel
section has exact rank nine.

## Remaining compiler obligations

This result does not yet close `M₉(2)`. A complete reduction still needs:

1. a rational, primitive-recursive choice of the nine-state realization for every body emitted
   by the fixed universal Neary source, including any degenerate basis branch;
2. the arbitrary-physical-word converse for exterior transition runs around the cut `UV`;
3. denominator clearing and a checked integer `9×9` pair;
4. integration with the existing universal-halting reduction and its exact axiom audit.

The exterior converse has a promising rank profile. In the benchmark realization,
`rank(A^kU)=4,4,3,1` for `k=0,1,2,≥3`, while `VA^k` has ranks `4,3,3,1`. Runs of length two
reduce to the source role `D_c`; runs of length at least three reduce to the changed separator
row. This gives a direct case split, but it is not yet a Lean theorem or a retained total
parameter proof.

## Verification

Lean module:
[`MatrixMortality/ChangedSeparatorTail.lean`](../MatrixMortality/ChangedSeparatorTail.lean).

Exact symbolic checker:
[`tools/audit_m92_changed_separator_tail.py`](../tools/audit_m92_changed_separator_tail.py).

The checker is part of `scripts/check.sh`. It uses exact SymPy rational functions; floating-point
arithmetic is absent.

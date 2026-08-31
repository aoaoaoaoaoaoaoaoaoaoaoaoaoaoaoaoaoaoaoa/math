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

Lean proves that `D<0` for every `β,body`. It also proves

```text
K−2V−1<0,    K+3V−6>0.
```

The sole remaining chart factor is `K−V−2`. When `β>0` and the body contains `b`, its binary
encoding contains a zero digit, so the lower `c` word is strictly below the unique maximal word
of the same length and `K−V−2>0`. The fixed universal compiler emits bodies beginning and ending
in `b`; hence the displayed `3+3+2+1` basis is total on the emitted family. No degenerate basis
branch remains.

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

## Exterior runs

Write the two physical matrices as `(A,UV)`. For any interface matrix `X`, direct products have
the following exact zero kernels:

```text
A^p U X V A^q = 0  iff  L_p X R_q = 0,

L_0=L_1=I,    L_2=D_c,    L_p=x  for p≥3,
R_0=I,        R_1=D_b,    R_2=D_c,    R_q=u  for q≥3.
```

The proof is finite. `VU=T` is invertible. `AU` has full column rank. Both `A²U` and `D_c`
have rank three and the same kernel because `VA²U=D_c`. The matrices `VA` and `VA²` have the
same one-dimensional left kernel as `D_b` and `D_c`, respectively. After three steps the two
nilpotent length-three chains and the length-two chain vanish:

```text
A³U=e₈x,    VA³=s³u e₈ᵀ,
Ae₈=se₈,   e₈ᵀA=se₈ᵀ.
```

The retained checker verifies these identities symbolically, together with four nonzero minors
certifying the ranks. At the exact `β=3`, body `bb` benchmark, it also checks all 36 exterior
representatives `p,q∈{0,1,2,3,4,5}` by equality of the corresponding kernels.

Each `D_b` or `D_c` fringe merely extends the paired control word. Each `x` or `u` fringe is one
boundary of the outer product `ux`. Therefore any physical zero gives a zero product, left
boundary, right boundary, or scalar sandwich in the separated paired family. Adjoining the
missing copy of `ux` turns the latter three cases into a zero product, and the Lean theorem
`mortal_adjoin_outer_iff` reflects all four cases to a paired scalar zero. Thus arbitrary
exterior transition runs introduce no new mortality.

## Remaining compiler obligations

This result does not yet close `M₉(2)`. A complete reduction still needs:

1. define the audited rational `9×9` transition and cut matrices in Lean and prove their moment
   and exterior identities there;
2. prove primitive recursiveness, clear denominators, and emit the resulting integer pair;
3. integrate the pair with the existing universal-halting reduction and exact axiom audit.

## Verification

Lean module:
[`MatrixMortality/ChangedSeparatorTail.lean`](../MatrixMortality/ChangedSeparatorTail.lean).

Exact symbolic checker:
[`tools/audit_m92_changed_separator_tail.py`](../tools/audit_m92_changed_separator_tail.py).

The checker is part of `scripts/check.sh`. It uses exact SymPy rational functions; floating-point
arithmetic is absent. It checks the symbolic realization, total-chart pivots, tail eigenvectors,
the parameter-uniform exterior kernel grammar, and the independent 36-class benchmark.

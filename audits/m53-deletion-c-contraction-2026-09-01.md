# M₅(3) singleton-D_c contraction audit

## Boundary

This audit classifies the Farey-height contraction found behind the `MM-O29` empty-front rays.
It concerns one inverse singleton `D_c` transition from a primitive positive carrier. It does not
classify the preceding physical block or prove a global height invariant.

## Raw transition

Fix `β≥2` and set

```text
H=5·3^β−1=2h,       r=3^β−2,       μ=2·3^β−1.
```

For coprime natural coordinates `0<d<n`, write `q=n−d`. The sign-normalized inverse adjugate is

```text
a=Hrq,       b=2(rn+Hd)=2rq+6μd.
```

`deletionC_rawAdjugate_forward` connects these definitions to the existing carrier API: applying
`nextCarrierNumerator` and `nextCarrierDenominator` for `[.erase .c]` to `(-a,-b)` returns
`(n,d)` multiplied by the exact determinant `−6HRμ`.

## Gcd channel

The complete common-factor criterion is

```text
gcd(a,b)=3H
  ↔ h∣n ∧ gcd(r,d)=1 ∧ gcd(q,3μ)=3.
```

The last gcd must use `3μ`, not `6μ`. At odd widths `H` has only one factor two, which absorbs
the even part of `q`; replacing `3μ` by `6μ` would reject valid channel members.

The proof uses `H+r=3μ`, `gcd(h,r)=1`, `gcd(r,3μ)=1`, and primitivity. In the forward direction,
writing `n=hk` factors the raw pair by `2h`; every remaining common divisor of `rq` and
`rk+2d` divides `3μd`, then reduces to `3`. The converse recovers each coprimality condition from
the assumed common factor.

## Height criterion

For nonnegative coordinates, Farey height is

```text
F(n,d)=max(n,d,|n−d|).
```

Inside the exact `3H` channel,

```text
F(a/(3H),b/(3H)) < F(n,d)  ↔  rq < 3n.
```

The denominator coordinate is always smaller than `n` in this channel; the numerator supplies
the sharp inequality. Its companion ratio is

```text
b/(3Hn)=2μ/H−2q/(3n),
2μ/H=4/5−6/(5H)<4/5.
```

This replaces the computational contraction observation by a theorem. It does not prove that
only `(R_c,D_b)` can enter the channel, nor that a two-step Farey weight always expands.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterDeletionCContraction.lean`](../MatrixMortality/SwappedSetterDeletionCContraction.lean).

The module and umbrella compile without warnings. The namespace passes the default linters, every
public theorem is listed in `AxiomAudit.lean`, and the aperture scan is empty. The publication
entry points are `deletionC_rawAdjugate_forward`, `deletionC_gcd_eq_three_mul_head_iff`,
`deletionC_fareyHeight_contracts_iff_channel`, and `deletionC_denominator_ratio`.

## Consequence

Universal one-step Farey monotonicity cannot close the empty-front arm. A global argument must
exclude the displayed gcd-and-gap chamber from physical ancestry or assign its contraction to a
preceding expansion with finite memory.

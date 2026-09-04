# M₅(3) primitive pullback audit

## Boundary

This audit covers the arithmetic of one sign-normalized physical inverse block over positive
natural coordinates. It distinguishes raw half-head divisibility from survival after primitive
gcd cancellation. It does not classify physical spellings, instantiate the `MM-O29` seed,
establish reachability, or prove a pole.

## Raw coordinates

With `H=5·3^β−1=2h`, `r=3^β−2`, and `μ=2·3^β−1`, define

```text
T=rn+Hd,
Nraw=PT−HμAd,
Draw=VT.
```

`inverseFraction_eq_rawRatio` proves this pair by clearing the rational inverse-block
denominators. The natural definition of `Nraw` is used only under the explicit inequality that
makes its subtraction genuine.

## Cancellation

For `Nraw=h·s`, Lean proves

```text
gcd(hs,Draw)=gcd(s,Draw)·gcd(h,Draw/gcd(s,Draw)).
```

Consequently the complete half-head survives in the primitive numerator exactly when

```text
gcd(h,Draw/gcd(s,Draw))=1.
```

This is an exact equivalence. Raw divisibility alone is not promoted to primitive divisibility.

## Incoming channel

Modulo `h`, the raw numerator is `Prn`. The established coprimality `gcd(h,r)=1` removes `r`,
and divisor extraction gives

```text
h∣Nraw ↔ h/gcd(h,n)∣P.
```

The upper target code obeys the affine append rules `c:Z↦3Z+1` and
`b:Z↦9·3^βZ+6·3^β−2`; the latter fixes residue one modulo `h`.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterPrimitivePullback.lean`](../MatrixMortality/SwappedSetterPrimitivePullback.lean).

The source compiles without warnings. The namespace passes the default linters; every public
theorem is listed in `AxiomAudit.lean`; the reviewed snapshot uses only standard axioms; and the
aperture scan is empty.

## Authorship

GPT-5.6 Sol, elicited by @eternalism_4eva.

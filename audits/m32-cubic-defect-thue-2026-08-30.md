# M₃(2) Cubic Defect And Thue Audit

Date: 2026-08-30

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The non-pure cubic fork asks whether every endpoint hit over the complete positive-wait
recurrence can be normalized to a controlled alphabet. The false-wait family already excludes
the selected alphabet `{1,5}`. The smallest remaining normalization question was to classify
the waits whose normalized return preserves its selected upper-triangular flag.

That scalar slice is no longer an unstructured Skolem problem. Its physical lower-left entry is
an integral order-three recurrence with a conserved cubic norm, and every zero maps to one fixed
exceptional Thue equation of discriminant `-23`.

## Physical Defect

For the false-wait physical family, put

```text
uₙ = -(Mₙ)₂₁/90.
```

Lean proves that `uₙ` is integral and obeys

```text
u₀=0,  u₁=0,  u₂=1,  uₙ₊₃=uₙ-uₙ₊₂.
```

Thus `Mₙ` preserves the selected upper-triangular flag exactly when `uₙ=0`. The checked zeros
are

```text
n=0,1,5,14.
```

The former safe alphabet `{1,5}` was therefore not maximal even inside the same flag: wait
fourteen is another positive flag-preserving return. This does not repair arbitrary-word
soundness because the exact false zero uses waits `8,12,15` with nonzero defect.

## Conserved Norm

For a consecutive window `(a,b,c)=(uₙ,uₙ₊₁,uₙ₊₂)`, define

```text
N(a,b,c)=a³-a²c-ab²-3abc+b³+b²c+2bc²+c³.
```

Write `T(a,b,c)=(b,c,a-c)` for the recurrence shift. Lean checks the polynomial identity

```text
N(b,c,a-c)=N(a,b,c)
```

and hence `N(uₙ,uₙ₊₁,uₙ₊₂)=1` for every `n`.

If `uₙ=0`, set `x=uₙ₊₁` and `y=uₙ₊₁+uₙ₊₂`. The invariant becomes exactly

```text
x³-xy²+y³=1.                                      (1)
```

This is the exceptional negative-discriminant binary cubic form of discriminant `-23`. The
reduction to (1), including integrality, is kernel checked.

The Delone–Nagell classification, recorded explicitly by Evertse on page 36 of
[*Upper Bounds for the Numbers of Solutions of Diophantine Equations*](https://ir.cwi.nl/pub/13027/13027D.pdf),
gives exactly

```text
(x,y)=(1,0),(0,1),(-1,1),(1,1),(4,-3).
```

In the displayed order these points occur on the bilateral defect orbit at indices
`1,0,5,−2,14`. The orbit has no repeated state: if `Tⁿs₀=Tᵐs₀` with `n>m`, then `Tⁿ⁻ᵐ`
fixes `Tᵐs₀`; that vector and its first two images are a rational basis, so `Tⁿ⁻ᵐ=I`. This is
impossible because the characteristic polynomial `X³+X²−1` has a real root strictly between
zero and one. The point `(1,1)` therefore occurs only at index `−2`, and all other points occur
only at their displayed natural indices. Thus

```text
uₙ=0  ⇔  n∈{0,1,5,14}.
```

The implication from the published Thue classification and the orbit exclusion is independently
audited rather than kernel checked.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the normalized physical defect is an integral recurrence | promotion | Lean proves `(Mₙ)₂₁=-90uₙ` and the exact initial recurrence |
| the recurrence has a cubic first integral | promotion | polynomial invariance and norm one are Lean checked |
| every triangular wait solves one fixed Thue equation | promotion | Lean proves the exact substitution into (1) |
| `{1,5}` is the complete positive triangular alphabet | rejected | wait fourteen is another checked zero |
| `{0,1,5,14}` is the complete zero set | audited completion | Delone–Nagell gives five Thue points; orbit injectivity leaves the negative-index state `T⁻²s₀` outside `ℕ` |
| the complete all-waits endpoint problem is decided | open | nontriangular defect letters can cancel across products |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: an unstructured scalar Skolem subproblem; maximality of the selected safe alphabet
SCALAR CLOSED: uₙ=0 exactly at n=0,1,5,14; the positive safe alphabet is {1,5,14}
FULL CUBIC THROAT: control cancellation among nonzero defect letters in arbitrary endpoint words
```

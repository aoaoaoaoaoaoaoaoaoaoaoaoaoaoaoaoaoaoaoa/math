# M₃(2) Cubic Continuant Punctuation Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The clocked comparator is a designated positive-wait spelling. To reason about arbitrary words,
the complete fixed false-wait family first needs an exact singular-letter classification and a
global fracture at every singular return.

## Determinant Recurrence

For a cubic defect state `(a,b,c)`, define

```text
Δ(a,b,c)=3a²−2ac−b²−3bc.
```

Lean checks

```text
det(M_n)=720Δ(state_n),
Δ(state_(n+3))=Δ(state_(n+1))+Δ(state_n).
```

The first three values are `0,2,3`. Strong induction on `n` proves `Δ(state_n)>0` for every
`n>0`. Hence every positive return has nonzero determinant and is a unit. Lean also lifts this
pointwise fact to every word of positive waits and proves the exact classification

```text
IsUnit(M_n) ↔ 0<n.
```

## Rank-One Fracture

Direct evaluation gives

```text
M₀ = [-79,−90]ᵀ[0,1].
```

Relabel the positive generators by `P_n=M_(n+1)` and define

```text
β(w)=[0,1]Π(P,w)[-79,−90]ᵀ.
```

The exact equivalence `Nat≃Option Nat` separates wait zero from positive waits. Applying the
generic outer-product fracture theorem then proves

```text
IsMortal(M) ↔ ∃w, β(w)=0.
```

This is an arbitrary-word theorem. Unit-only exterior words cannot vanish, a single separator
cannot acquire zero from unit multiplication, and any word with several separators fractures at
one scalar bridge between consecutive separators.

## Explicit Bridges

The existing bridge is

```text
[12,12,8,12,12,15,8].
```

Lean now checks a distinct bridge

```text
[13,15,29,11,13,7,8]
```

by exact rational matrix multiplication. Its positive-word product is

```text
[[2185809684134400000,−1918984245949440000],
 [1144697271091200000,−1004789826846720000]],
```

and it sends the separator column to `[29617088832000000,0]ᵀ`, so surrounding it by `M₀`
on both sides gives zero.

An exact meet-in-the-middle census found no bridge zeros through length four for waits at most
`300`, none at length five for waits at most `120`, none at length six for waits at most `100`,
and exactly these two length-seven hits for waits at most `50`. These finite exhaustiveness bounds
remain computational evidence; only the displayed second bridge was promoted to Lean.

## Adjudication

| Claim | Judgment |
| --- | --- |
| the determinant coefficient satisfies the displayed recurrence | Lean checked |
| wait zero is the unique nonunit return | Lean checked |
| every positive-only word is a unit | Lean checked |
| wait zero has the displayed rank-one factorization | Lean checked |
| arbitrary mortality is equivalent to one positive scalar bridge | Lean checked |
| the second seven-positive-wait bridge vanishes | Lean checked |
| the bounded absence and uniqueness claims | exact computation, not formalized |
| the positive scalar bridge language is decided uniformly | open |
| the fixed family supplies an instance-dependent reduction | rejected |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: every raw punctuation and exterior-word ambiguity in the fixed cubic language
GAINED: a complete arbitrary-word reduction to one positive scalar bridge
EXPOSED: positive-bridge semantics and target dependence as the only lawful fixed-family seams
NEXT: classify the bridge language, or twist the endpoint while preserving the local comparator
```

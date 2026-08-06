# M₃(2) Prequotient-Adelic Ratchet

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. The
present attack concerns the split-spectrum rank-`(3,2)` guard, not the unresolved exceptional
rank-`(2,2)` compiler seam. Its live stratum has even reset resultant, passes every universal
boundary test, and has unbounded primitive denominators.

The submitted attack proposed a primitive prequotient coordinate, a generalized continued
fraction, a diagonal form for the wait gauge, and a global adelic peeling theorem. The first and
third claims survive formal reconstruction. They remove a coordinate obstruction but do not
supply the proposed peeling theorem.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| `(tᵢ,hᵢtᵢ₊₁)` is primitive and carried through consecutive reductions | promotion | Lean checks one integral transport at every depth; primitivity is the existing prequotient coprimality theorem |
| the carried ratio is a content-free generalized continued fraction | correct with scope | valid when the two displayed denominators are nonzero; it is an edge coordinate along an execution, not yet a locally selected complete quotient |
| the reverse coordinate gives an independent two-ended constraint | restatement | its primitivity follows from two existing coprimality laws, and its recurrence is the checked denominator recurrence; `xᵢyᵢ=DL(qᵢ−1)` makes it algebraically dual to the forward coordinate |
| the Smith decoder is a two-run Stern-Brocot block | restatement | multiplying the checked continuant cut by the swap matrix gives the displayed factorization |
| one fixed basis diagonalizes every wait gauge | promotion | Lean checks the exact conjugacy; the gauge is a pure rational base-prime dilation |
| two decoders surrounding a monotone gauge form a positive primitive matrix | open as a live claim | the algebraic sign pattern is valid under the stated positive Smith splits, but no checked identity makes this product the transfer of the carried execution coordinate |
| both generalized coefficients have exact base-prime valuation `−2aᵢ₊₁` | conditional | requires a base-prime-normalized integral presentation with `p∤ADL`; it is not a theorem of an arbitrary coefficient presentation |
| the CMT/CCMT proof ports almost verbatim | open | the recurrence has variable partial numerators, no proved floor selector, no computed all-place factor, and no equality-locus classification |
| the balancing deficit is `⌈(L−U)/2⌉` | correct, culled | true for the finite minimax debt `minₓ maxᵢ max(0,−gᵢ)` after that debt is defined; no theorem connects it to terminal corridors |
| fresh-prime debt is laminar or recursively peelable | open | this is the new global theorem, not a consequence supplied by the report |
| the guard or `M₃(2)` is decided | rejected | neither an effective height bound nor an infinite coefficient-aligned counter-orbit was obtained |

## Carried Coordinate

Let consecutive primitive endpoint reductions at depth `s` be

```text
(rᵢ,tᵢ) --(aᵢ,hᵢ)--> (rᵢ₊₁,tᵢ₊₁)
          --(aᵢ₊₁,hᵢ₊₁)--> (rᵢ₊₂,tᵢ₊₂),
q=p^aᵢ,  Q=p^aᵢ₊₁,  F=DL.
```

Put

```text
sᵢ=hᵢtᵢ₊₁,
Xᵢ=(tᵢ,sᵢ)ᵀ.
```

The existing theorem `prequotient_coprime_denominator` gives `gcd(tᵢ,sᵢ)=1`. Eliminating the
source numerator from the two checked endpoint equations gives the stronger depth-uniform law

```text
Q^s hᵢ Xᵢ₊₁ =
  [[0, Q^s],
   [F(q−1), A+Dq^s−LQ]] Xᵢ.                         (1)
```

This is now kernel-checked as `PrimitiveEndpointReduction.twoStep_prequotient_transport`. The
matrix determinant is `−FQ^s(q−1)`. The split `hᵢkᵢ=F(q−1)` has disappeared from the projective
matrix, while `hᵢ` remains in the primitive coordinate and in the scalar removed on the left.
No tangent variable, complementary-content choice, or new state structure is needed.

When `tᵢtᵢ₊₁≠0`, projectivizing `(1)` gives

```text
xᵢ₊₁ = (A+Dqᵢ^s−Lqᵢ₊₁)/qᵢ₊₁^s
        + DL(qᵢ−1)/(qᵢ₊₁^s xᵢ),
xᵢ = hᵢtᵢ₊₁/tᵢ.                                    (2)
```

Equation `(2)` is a generalized continuant, but `Xᵢ` is attached to the outgoing edge: it uses
the next denominator and the removed content. The legal wait is not yet proved to be a locally
constant floor function of `xᵢ`, and the sign of `hᵢ` does not place every `Xᵢ` in one positive
real cone. Those are the remaining seams between `(1)` and a positive-block or CMT theorem.

## Gauge

The checked frame change is

```text
J(q,Q)=[[1,0],[Q²/q²−1,Q²/q²]].
```

With `P=[[1,0],[1,1]]`, Lean now proves

```text
P J(q,Q) P⁻¹ = diag(1,Q²/q²).                        (3)
```

Thus the gauge has a common rational eigenbasis and one moving Cartan factor. Its real and
base-prime logarithms cancel by the product formula. This does not diagonalize the intervening
Smith or lagged cocycles, nor do the diagonal factors commute through them. The former shear
obstruction is therefore sharpened to an exact question: can the pure dilation repay every
isolated nonmaximal Smith loss in the all-place height product?

For a base-prime-normalized presentation `p∤ADL` and positive waits, the two coefficients in
`(2)` are integral away from `p` and both have valuation `−s aᵢ₊₁` at `p`. An arbitrary integral
presentation may contain a common power of `p`; the exact valuation assertion must either strip
that power or state the three unit hypotheses. No generic valuation declaration was retained.

## Culled Ladders

The proposed backward coordinate

```text
Yᵢ=(tᵢ₊₁,kᵢtᵢ)ᵀ
```

is primitive by `denominators_coprime` and `denominator_coprime_complement`. Its transport is
the existing `denominator_recurrence` multiplied by the next complement, and
`xᵢyᵢ=hᵢkᵢ=DL(qᵢ−1)` makes the scalar reverse recurrence equivalent to `(2)`. Retaining a second
API would duplicate the same information.

Likewise,

```text
C(q,u,v)S=R^vL^((q+1)u)
```

is exactly `smithRubanDecoder_continuant_cut` followed by the swap `S`. The proposed balancing
definitions are elementary finite path combinatorics but are not consumed by a terminal theorem.
They were not installed.

The positive two-decoder matrices are not retained either. Positivity of an abstract product
does not establish that a legal endpoint corridor is its inverse branch. The missing conjugacy,
cone entry, and primitive scalar bound contain the whole descent problem.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GUARD VERDICT: the even-resultant unbounded-denominator stratum remains open
REMOVED: absence of a primitive coordinate carried across consecutive endpoint reductions; treatment of the wait gauge as an irreducible shear
REMAINS: prove an effective block-height theorem for the exact generalized continuant (1), or construct a legal coefficient-aligned unbounded corridor
DISTANCE: orient the carried edge coordinate in computable positive/adelic blocks, calculate the full all-place factor including primitive reduction, and prove strict descent or classify and peel every equality/deficit interval
```

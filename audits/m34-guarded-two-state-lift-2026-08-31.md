# M₃(4) Guarded Two-State Lift Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `19ff89d` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedTwoStateLift.lean`](../MatrixMortality/GuardedTwoStateLift.lean)

## Verdict

The one-singular-gate architecture of `G3-C07` admits a uniform compiler interface. The third
state, complete malformed-word guard, and full-rank escape require only an odd lattice invariant.
Exactness is then equivalent to one scalar incidence equation in a source-indexed two-state
orbit. No further three-state recurrence design remains inside this architecture.

This does not settle `M₃(4)`: the two-state incidence is the positive projective hard core shared
with `M₂(3)`. The reduction is nevertheless strict. One-dimensional target retuning, common
kernels, and generic irreducible three-state fork actions are no longer live substitutes.

## Construction

Fix integral `2×2` matrices `A_b,A_c,A_t`, a column `q`, and a gate row `g`. Define

```text
        [2  2  1]             [0  g₀  g₁]             [1  0  0]
Â_b  = [0      ] ,   Â_c  = [0       ] ,   Â_t  = [0     ] ,
        [0  A_b ]             [0   A_c ]             [0  A_t]

λ=(1,0,0),   γ=(1,q).
```

For `h_w=A_wq`, direct block multiplication gives

```text
Â_wγ=(G(w),h_w),
G(ε)=1,
G(bw)=2G(w)+2h_w(0)+h_w(1),
G(cw)=g·h_w,
G(tw)=G(w).
```

Lean proves this identity for every raw word, without a normal-form assumption.

## Exact Gate Equation

Assume `h_w(1)` is odd for every raw word. Then `G(bw)` is odd and cannot vanish. Define the
gate language recursively:

```text
L(ε)        = false,
L(bw)       = false,
L(cw)       ⇔ gA_wq=0,
L(tw)       ⇔ L(w).
```

The orbit-wide parity premise has a finite sufficient certificate. Lean proves it by induction
when `q(1)` is odd, each generator's lower-left entry is even, and each lower-right entry is odd.
Thus parity does not require an unbounded orbit audit for a proposed source family.

Lean proves

```text
λÂ_wγ=0 ⇔ L(w)
```

on the complete free monoid. For each Neary source `(beta,body)`, it then proves the equivalence

```text
(∀w, λÂ_wγ=0 ⇔ pairedCoefficient(beta,body,w)=0)
⇔
(∀w, L(w) ⇔ pairedCoefficient(beta,body,w)=0).
```

The same equivalence is checked parametrically for a function
`(beta,body)↦(A_b,A_c,A_t,q,g)`. For positive deletion width, Lean further proves that a paired
zero cannot begin with data `b`, using the native theorem that every terminal-match tile word
starts with the distinguished `c` rule. The empty coefficient is nonzero and a leading toggle
preserves the paired coefficient. Consequently the complete equivalence above reduces to the
single source-dependent equation

```text
gA_wq=0 ⇔ pairedCoefficient(beta,body,cw)=0
```

for every suffix `w`. A computable definition of the source-indexed core satisfying parity and
this equation is therefore a uniform compiler. The theorem does not certify computability of an
arbitrary function parameter; construction and computability of that family remain the same
open obligation.

## Rank Geometry

Lean computes

```text
det Â_b = 2 det A_b,       det Â_c = 0.
```

If `A_b` is nonsingular, scalar extension to `ℚ` gives `rank Â_b=3`. Thus the persistent data
letter can be full-rank while the gate letter alone is singular. The `m=2` member of `G3-C07` is
the affine specialization: its homogeneous core coordinate is identically one, and its fixed
accepting-carry row is `g`.

## Relation To The Terminal-Fork Core

`G3-S03` and the present core have different boundaries. The `G3-S03` fork carrier `W` is spanned
by accepted complete-fork states and is annihilated by the transported terminal row. Its internal
action therefore accepts every fork word identically. Malformed-word rejection must detect a raw
control that leaves `W` before the terminal boundary. The present two-state suffix orbit models
exactly such a leakage gate; it is not obtained merely by restricting the fork blocks to `W`.

Consequently, dimension-one fork dynamics are projectively constant. In dimension two, common
eigenline and invariant-pair cases enter the `D2` affine/elementary program, but only its audited
substrata may currently be called decided. The generic survivor is the non-elementary positive
scalar-orbit problem `D2-S01`.

## Symmetric-Square Audit

For `v=(x,y)`, put `ν(v)=(x²,xy,y²)`. For a fixed ray `u=(p,q)`, the tangent row

```text
τ_u=(q²,−2pq,p²)
```

satisfies

```text
τ_uν(v)=(pv₂−qv₁)².
```

This is the same zero predicate as a fixed two-state linear gate; it squares and canonicalizes
the projective incidence but does not construct the required source orbit. It also occupies all
three symmetric-square coordinates, so adjoining the present guard would require a fourth state.

There is a sharper direct-fork obstruction. For three rays `u,v,w`, expansion gives

```text
det[ν(u),ν(v),ν(w)]
  = ± det[u,v] det[u,w] det[v,w].
```

Hence three pairwise distinct projective rays have linearly independent Veronese images. Since
`G3-S03` forces every exact complete-fork orbit to span a subspace of dimension at most two, a
direct symmetric-square fork orbit contains at most two projective rays. It is therefore forced
into an invariant point or pair, not the non-elementary `GL₂` branch. Symmetric square remains
eligible only as an ambient leakage or terminal-incidence gadget, where it must still satisfy the
complete raw-word gate equation above.

The symmetric-square identities are being formalized in the joint `M₂(3)` lane. Until that
artifact lands, this subsection is an audited algebraic consequence rather than a dependency of
`G3-C08`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The lifted state recurrence holds on every raw word | promotion | Lean induction |
| Three finite mod-`2` row conditions imply orbit-wide parity | promotion | Lean induction |
| Odd core parity makes the zero set exactly the gate language | promotion | Lean all-word equivalence |
| The source-family same-zero problem reduces to the data-`c` two-state gate equation | promotion | Lean positive-width iff theorem |
| Nonsingular `A_b` makes the persistent data letter rational rank three | promotion | Lean determinant and rank certificate |
| The singular gate and third-state malformed-word logic remain open | rejected | both are compiled by the theorem |
| `G3-S03` alone supplies the gate orbit | rejected | its boundary annihilates the complete fork carrier |
| Symmetric square uniformizes the gate | rejected | its tangent predicate is the same projective incidence |
| A non-elementary symmetric-square pair can act directly on the complete fork | audited obstruction | Veronese triple determinant plus `G3-S03` |
| A source-indexed gate family exists | open | exact remaining equation |
| `M₃(4)` follows | rejected | the `D2-S01` incidence remains unresolved |

## Formal Validation

The formal owner compiles warning-free under the repository toolchain and passes the default
environment linter. Publication-facing declarations are listed in
[`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom outputs contain only the reviewed
standard axioms. No proof aperture, project axiom, unsafe declaration, linter suppression, or
external certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
COMPILER: guard + malformed-word converse + full-rank data b reduce to one 2D gate equation.
EXACT OBLIGATION: construct parity-preserving A,q,g with gA_wq=0 iff paired(cw)=0.
JOINT SEAM: generic non-elementary scalar orbit is D2-S01 / positive M₂(3).
NO-GO: direct non-elementary Sym² fork action conflicts with the G3-S03 proper carrier.
```

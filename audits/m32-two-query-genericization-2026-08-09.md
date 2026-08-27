# M₃(2) Two-Query Genericization Audit

Date: 2026-08-09

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The first genericization attack reduced unrestricted PI₂ to at most three GPI₂ queries by
exiting the intersection of two exceptional two-point sets. The remaining question was whether
a reachable two-vertex bad graph could really have three exits.

It cannot. When the common exceptional set has two points, the relative projectivity permutes
it. The two generator transitions are therefore simultaneously internal or external. This
sharpens the exact positive-word reduction to two nonadaptive generic queries and removes
arbitrary-versus-generic PI₂ as a decision-theoretic frontier.

## Rectified Geometry

The report presents the argument through target lines and right row actions. The repository's
reverse compiler is source-column based. Under the kernel correspondence these are dual
descriptions, but silently mixing them reverses every matrix action. The formalization uses the
source description directly.

For nonzero row `r`, let

```text
E(G,H)={H ker(r), H G⁻¹ H ker(r)},
N=E(G,H) ∩ E(H,G).
```

Lean proves

```text
card(N)≤2.
```

Outside `N`, at least one of `(G,H)` or `(H,G)` is generic. Swapping the labels preserves the
set of matrix words, so this is one GPI₂ query.

## The Two-Point Cut

Put `A=G H⁻¹`. If `card(N)=2`, then the intersection already exhausts each two-point
exceptional set:

```text
N=E(G,H)=E(H,G).
```

On the two generators of `E(G,H)`, the relative action satisfies

```text
A(H ker(r))       = G ker(r),
A(H G⁻¹H ker(r)) = H ker(r).
```

The first image lies in `E(H,G)=N`; the second lies in `E(G,H)=N`. Since `A` is a projective
bijection, it permutes `N`. For every nonzero current column `v`,

```text
[Gv]=A[Hv],
```

and therefore

```text
[Gv]∈N iff [Hv]∈N.
```

Lean checks the projective action law, injectivity of every unit action, the finite-set
permutation argument, and the final equivalence in

```text
ProjectiveIncidence.commonBadSources_two_transition_iff.
```

No order classification, eigenvalue calculation, or algebraic closure is needed for this
stronger consuming theorem.

## Exact First Exit

Follow a candidate word from the original source while its projective state remains in `N`.
If it reaches the target inside `N`, that is a finite directly decidable event. Otherwise its
first exit is a generic successor query; concatenating the positive prefix back onto any suffix
witness proves the converse.

If `card(N)≤1`, there are at most two labelled exits. An internal edge can only return to the
same ray and may be deleted projectively from a shortest witness. If `card(N)=2`, both edges at
each reachable state are internal or both are exits. The initial state contributes either two
exits or none; after an internal move, the other state contributes either two or none. Hence the
set of distinct reachable exits has cardinality at most two. Every exit column is reached by a
positive prefix of length at most two.

Thus, with finite exact preprocessing,

```text
PI₂ ≤²_tt GPI₂.
```

The queries are computed before any oracle call. Inverses occur only in rational exceptional-set
tests and never in a quantified word. Empty words, coincident generators, scalar controls,
fixed rays, and nonfree relations are all preserved.

Fixed generic YES and NO instances absorb the finite terminal truth value when a literal
truth-table reduction is desired. Consequently

```text
PI₂ is decidable iff GPI₂ is decidable.
```

Together with `Mort₃^(2,2) ≡ₘ GPI₂`, the rank-(2,2) profile and unrestricted PI₂ have the same
decidability status.

## One-Instance Residue

The report further classifies the failure of a many-one reduction to one query. After exact
case reduction, only two positive-synchronization forms survive:

```text
(F)  G=AB, H=B, A fixes the source ray and has infinite projective order;
(C3) G=RB, H=R²B, R³ is projectively scalar, and the zero phase is omitted.
```

The projective-involution analogue closes by the exact monoid identity

```text
{H,J}* = {H,HJ}* ∪ J{H,HJ}*,     J² projectively scalar,
```

with a decidable dihedral recurrence fallback. The fixed-ray and order-three ORs do not collapse
by the same argument. Fixed proper positive codes have generic malformed-word counterexamples,
and conjugation, scaling, duality, or denominator clearing preserves vanishing of each
exceptional scalar.

These are sound comparison results but no longer lie on the shortest path to M₃(2): the
two-query theorem already identifies the decision problems. They are retained in this bounded
audit and culled from the live master frontier.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| common exceptional set has at most two rays | formalized | exact finite-set consequence of the checked bad locus |
| two-point transitions are simultaneously internal or external | formalized | relative projectivity permutes the common bad set |
| unrestricted PI₂ reduces to at most two GPI₂ queries | promotion | exact positive first-exit synthesis |
| PI₂ and GPI₂ have the same decidability status | promotion | immediate bounded truth-table consequence |
| projective-involution OR collapses or becomes decidable | salvage | exact, but not needed after the two-query theorem |
| fixed-ray and order-three forms are the residual one-query seams | salvage | scoped to one-instance comparison, not the master decision |
| fixed proper positive codes solve the OR seam | rejected | Schottky malformed-word counterexample |
| one GPI₂ instance always suffices | open | neither residual one-query form was closed |
| GPI₂ or M₃(2) is decided | rejected | the substantive incidence and rank-(3,2) enemies remain |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: arbitrary-versus-generic PI₂ as a decision-theoretic seam; the apparent third exit
REMAINS: normalized GPI₂ itself; the non-pure cubic reflection orbit; the split doubly order-broken guard
CULLED FROM MASTER FRONTIER: one-instance genericization, fixed codes, and finite phase transports
```

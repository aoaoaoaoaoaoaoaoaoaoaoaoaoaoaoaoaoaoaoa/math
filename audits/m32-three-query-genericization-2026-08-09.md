# M₃(2) Three-Query Genericization Audit

Date: 2026-08-09

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The rank-(2,2) reduction had isolated generic projective incidence GPI₂ but left a seam between
it and unrestricted PI₂. The reverse compiler requires two exceptional scalars to be nonzero:

```text
alpha(H,r,c)=rH⁻¹c,
beta(G,H,r,c)=rH⁻¹GH⁻¹c.
```

The external attack removes that seam for decidability by a positive-word first-exit argument.
It also proves that every generic instance can be normalized to `alpha=beta=1` without changing
its zero language. The sibling report strengthens the exit bound from three to two, so this
audit retains the exact locus, normalization, and finite-congruence obstruction rather than
promoting the superseded bound as the final frontier.

## Exact Exceptional Locus

Let `tau` be the projective kernel of the nonzero row `r`. For the ordered pair `(G,H)`, the two
bad source rays are

```text
H tau,
H G⁻¹ H tau.
```

Indeed,

```text
alpha(H,r,d)=0  iff  [d]=H tau,
beta(G,H,r,d)=0 iff  [d]=H G⁻¹ H tau.
```

Lean checks both equivalences without affine-chart assumptions. It projectivizes a nonzero
column by homogeneous cross product, proves that a unit matrix multiplies that cross product by
its nonzero determinant, and applies the exact inverse actions already used by the reverse
compiler. The consuming theorem is

```text
ProjectiveIncidence.generic_iff_sourcePoint_not_mem_badSources.
```

Intersecting the bad sets for `(G,H)` and `(H,G)` leaves at most two source rays. Outside the
intersection, swapping the letter names gives one generic instance with the same matrix-word
language.

## Positive First Exit

If the initial source lies in the common bad set, follow its orbit only while it remains in that
set. Any successful word either reaches the target inside this finite graph or has a first edge
leaving it. The suffix after that edge is a generic query, and the traversed prefix is a genuine
positive word of length at most two. No matrix inverse enters the quantified language.

A reachable graph on at most two vertices has at most three exit edges, giving

```text
PI₂ ≤³_dtt GPI₂.
```

This theorem is correct but not sharp. The sibling attack proves that in the only two-point
case both labelled transitions are simultaneously internal or external, reducing the bound to
two. The three-query result is therefore evidence for the route, not a separate surviving node.

## Unit Normalization

For a generic instance put `a=alpha(H,r,c)` and `b=beta(G,H,r,c)`, and define

```text
H' = a H,
G' = (a²/b) G.
```

Then

```text
alpha(H',r,c)=1,
beta(G',H',r,c)=1.
```

Every word containing `m` copies of `G` and `n` copies of `H` is multiplied by the nonzero
scalar `(a²/b)^m a^n`. Hence its incidence coefficient vanishes exactly when the original one
does, including the empty word. Lean checks the unit witnesses, both normalized scalars, and
the all-word equivalence in

```text
ProjectiveIncidence.exists_unitNormalized.
```

Thus the intrinsic compatible-loop value `beta=1` loses no generic instances; the stronger
normalization `alpha=beta=1` is canonical for the decision problem.

## Finite-Congruence Obstruction

The generic affine instance

```text
H=[[2,0],[0,1]],
G=[[2,1],[0,1]],
r=(1,0),
c=(1,1)ᵀ
```

acts by `x↦2x` and `x↦2x+1`. Starting at one, it reaches exactly the positive integers and
never reaches the target zero, while `alpha=1/2` and `beta=1`. For every modulus `m`, however,
some word reaches the integer `m`, hence reaches zero modulo `m`. One word reaching the least
common multiple defeats any prescribed finite family of congruence quotients simultaneously.

This rejects bare finite-congruence completeness. It does not reject richer finite-state
algorithms carrying real or `S`-adic information.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| exact two-ray exceptional locus | formalized | both scalar-zero equivalences checked in Lean |
| positive first-exit reduction to at most three generic queries | promotion | exact, but superseded by the sibling two-query theorem |
| every generic instance scales to `alpha=beta=1` | formalized | units, scalars, and all-word zero equivalence checked |
| unrestricted PI₂ many-one reduces to one GPI₂ instance | rejected | the construction is a bounded disjunction, not one instance |
| finite congruence quotients decide GPI₂ | rejected | explicit generic affine no-instance defeats every finite family |
| GPI₂ is decided | open | no infinite-structure decision theorem or undecidability reduction was delivered |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: exceptional-scalar normalization as a substantive restriction; genericity as a decidability-class seam
REMAINS: GPI₂ itself and the rank-(3,2) trunks
CULLED: the superseded three-query count once the sibling two-query theorem is installed
```

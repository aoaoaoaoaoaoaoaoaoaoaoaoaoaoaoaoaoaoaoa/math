# Cancellative Projective No-Go Audit

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a7541e9-41e0-83ea-9750-caed50fd3a1b)

## Enemy Lock

```text
MASTER: prove M₃(4) undecidable.
VICTORY: a total computable four-generator 3 × 3 mortality reduction with a complete
         arbitrary-product converse.
LIVE OBSTRUCTION: construct a genuinely two-dimensional one-way same-zero compiler, or prove
                  that one paired zero language has rational zero-language dimension at least four.
KILLED LANES: exact rank three; nonerasing three-role macros; rational phase-local compression;
              global history uniqueness; finite-mode expanding one-coordinate history.
```

## Verdict

Two results survive.

First, every finite prefix-suffix zero table of every paired instance has rational support rank at
most three. This is stronger than the report's bounded searches: Lean constructs one global conic
factorization of the complete static incidence table and proves its exact zero support. A
four-state lower bound cannot follow from a finite support/minrank submatrix. It must use common
shift maps.

Second, a target-exact projective recurrence which extends the two word sides to independent
cancellative inverse actions needs at least four vector dimensions whenever its terminal fiber is
nonempty. The role-pair group contains a freely acting `F₂×F₂`; inverse saturation makes this a
faithful projective action on the reachable span; and `F₂×F₂` has no faithful rational
projective representation in dimension at most three.

The second theorem does not cover a general positive-semigroup compiler. A valid three-state
construction may be intrinsically one-way: its inverse points may be absent, its target law may
fail on formal inverse continuations, or a singular map may collapse the orbit before group
completion. The report's conclusion is retained only with its saturation hypothesis.

## Phase-Aware Residuals

For a control block `p` and a phase `q` entering from its right, let `D_q(p)` be its decoded role
word. Lean defines `PairedResidual.decodeFrom` and checks

```text
D(ps) = D_phase(s)(p) ++ D(s)
```

with the corresponding phase identity. This fixes the multiplication order used below.

Embed positive bit words in the free group `F=⟨x,z⟩`. For a prefix `p`, suffix `s`, and
`q=phase(s)`, set

```text
A(p,q) = U(D_q(p))⁻¹ L(D_q(p)),
B(s)   = U(D(s)) m L(D(s))⁻¹,
m      = z x^β.
```

Free cancellation gives

```text
pairedCoefficient(β,body,p++s)=0
  ↔ U(D_q(p)) U(D(s)) m = L(D_q(p)) L(D(s))
  ↔ B(s)=A(p,q).
```

The reverse implication uses injectivity of the positive monoid in its free-group completion.
Lean checks that injection, the residual equivalence, the decoder split, and the final paired
coefficient equivalence.

## Global Conic Factorization

Choose an injective rational code `θ(q,g)` for every phase-tagged free-group residual. Lean uses
the reduced free-group word as an exact countable code. Put

```text
v(t)   = (1,t,t²)ᵀ,
ℓ(a,b) = (ab,−(a+b),1).
```

Then

```text
ℓ(a,b)v(t) = (t−a)(t−b).
```

Assign

```text
c_s = v(θ(phase(s),B(s))),
r_p = ℓ(θ(rule,A(p,rule)), θ(erase,A(p,erase))).
```

Injectivity of `θ` separates the two phases, so

```text
r_p c_s=0 ↔ B(s)=A(p,phase(s))
            ↔ pairedCoefficient(β,body,p++s)=0.
```

This is one factorization of the whole static table, not a separately fitted factorization for
each finite sample. For arbitrary finite context and suffix index types, Lean forms the sampled
matrix, factors it through `Fin 3`, proves rank at most three, and proves exact agreement of every
zero and nonzero entry. Therefore no support-only finite submatrix can establish
`zdim_ℚ≥4`. The missing condition is precisely shift equivariance: the codes `θ` do not furnish
common matrices taking `c_s` to `c_{as}` or `r_p` to `r_{pa}`.

## Cancellative Saturation

Let the four Neary role pairs generate `Γ≤F×F`, acting on a discrepancy by

```text
(u,l)·d = u d l⁻¹.
```

A cancellatively saturated projective recurrence of vector dimension `d` consists of:

1. a `Γ`-set `X` carrying formal inverse continuations;
2. an equivariant residual map `δ:X→F`;
3. phase points `P_rule(ξ),P_erase(ξ)∈P(V)` for every `ξ∈X`, with `dim_ℚ V=d`;
4. projective actions of `H_b,H_c,T` implementing every rule and erasure role on every point;
5. a row `λ` with `λP_erase(ξ)=0 ↔ δ(ξ)=1` on all of `X`.

The last quantifier matters. A positive compiler whose coefficient is correct only on its forward
orbit need not satisfy the target law on formal inverse states and is outside the theorem.

On the erase chart the role matrices are

```text
K_Ea = H_a,       K_Ra = H_a T.
```

The order is forced by right-to-left decoding: `T` first changes the suffix phase, then `H_a`
emits the rule role and resets to erase.

## Independent Side Subgroups

Write

```text
B_β = z x^β z,
E_b=(B_β,x),       E_c=(z,x),       R_b=(B_β,z²x).
```

The role fractions contain

```text
A  = E_b E_c⁻¹       = (z x^β,1),
A′ = E_c A E_c⁻¹     = (z(zx^β)z⁻¹,1),
C  = R_b E_b⁻¹       = (1,z²),
C′ = E_b C E_b⁻¹     = (1,xz²x⁻¹).
```

Lean checks all four identities in `CancellativeRoleFraction`.

Let

```text
L_β=⟨zx^β,z(zx^β)z⁻¹⟩,       R=⟨z²,xz²x⁻¹⟩.
```

Their folded core graphs each have rank two. The `L_β` core consists of the cycles

```text
p₀ -z→ p₁ -x^β→ p₀,
p₁ -z→ p₂ -x^β→ p₁,
```

and has `2β+1` vertices and `2β+2` unoriented edges. The `R` core consists of two `z²` cycles,
based at `r₀` and `r₂`, joined by one `x` edge, and has four vertices and five edges.

For `β≥2`, the base component of their fiber product is the four-vertex path

```text
(p₀,r₀) -z→ (p₁,r₁) -z→ (p₂,r₀) -x→ (q,r₂),
```

where `q` is the first internal vertex of the second `x^β` path. It contains no reduced loop, so
`L_β∩R={1}`. The subgroup

```text
G₀=(L_β×{1})({1}×R) ≅ F₂×F₂
```

therefore acts freely on the discrepancy orbit of `1`.

The graph count, folding, and fiber-product argument remain audited rather than kernel-checked.
The symbolic reconstruction gives the displayed path for every `β≥2`; exact automaton checks for
`2≤β≤6` independently matched it but are not used as proof.

## Projective Descent

Choose `ξ★` with `δ(ξ★)=1`. Each positive role map sends the full set
`{P_erase(ξ):ξ∈X}` bijectively to itself because the corresponding element of `Γ` acts
bijectively on `X`. Its restriction to the span of that set is therefore invertible, even if the
ambient matrix is singular. Formal inverse role words consequently act projectively on the
reachable span.

The points

```text
S={P_erase(g·ξ★):g∈G₀}
```

are distinct. If two coincide, applying the inverse of one group element produces two coincident
points of which exactly one is killed by `λ`, since the discrepancy action is free. This
contradicts the target law.

Relations in `G₀` act pointwise on `S`. In projective dimension at most two, a nonidentity
projective automorphism cannot fix an infinite transitive spanning set:

- on a projective line it fixes at most two geometric points;
- on a projective plane its fixed locus lies in a line together with at most one exterior point;
  transitivity cannot preserve such a spanning configuration.

Hence the role-fraction action descends to a faithful homomorphism

```text
G₀ ↪ PGL(W),       dim W≤3.
```

This descent is invalid without inverse saturation. The abstract group action on residual labels
alone does not supply inverse projective points or the target law there.

## The Three-Dimensional Tax

There is no faithful `F₂×F₂→PGL_d(ℚ)` for `d≤3`.

For `d=2`, the centralizer of an infinite-order element of `PGL₂` is abelian over an algebraic
closure, so it cannot contain the second faithful `F₂`.

For `d=3`, lift the two free factors to `GL₃(ℚ)` by choosing lifts of their free generators. If
lifts `A,B` from opposite factors commute projectively, then

```text
AB=μBA.
```

Determinants give `μ³=1`; the only rational cube root of unity is `1`. Lean checks this step as
`CancellativeProjectiveRigidity.scalar_commutator_eq_one`. The two lifted free groups therefore
commute linearly.

Over an algebraic closure, view `K³` as a module for the first factor. If it is irreducible, Schur's
lemma makes its commutant scalar. If it has composition factors of dimensions `2+1`, the
commutant's semisimple quotient is commutative and its radical is nilpotent, so its unit group is
solvable. If all composition factors are one-dimensional, the first factor is triangularizable
and hence solvable. None of these cases permits two commuting faithful nonabelian free groups.

The projective fixed-locus argument, the commutant classification, and the resulting dimension
tax remain audited. The determinant spine is kernel-checked.

## Fixed Mortal Instance

The theorem needs a nonempty terminal fiber, not a terminal parameter in the compiler. The fixed
admissible source

```text
β=3,       body=bb
```

has checked witness `ctbbt`, decoded as `R_c E_b E_b`. Thus every total saturated compiler would
already fail on this fixed input. This is not a computability contradiction and uses no oracle.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Phase-aware decoder split on every prefix and suffix | promotion | Lean theorem |
| Positive binary words embed in the binary free group | promotion | Lean theorem |
| Terminal matching is equality of two phase-tagged residuals | promotion | Lean theorem |
| The global conic has exactly the complete paired prefix-suffix zero support | promotion | Lean theorem |
| Every finite support table has rational rank at most three | promotion | Lean theorem |
| The four displayed role fractions separate into left-only and right-only actions | promotion | Lean theorem |
| `L_β` and `R` are free of rank two with trivial intersection | promotion | audited folded-graph proof |
| Inverse saturation produces a faithful `F₂×F₂` projective action | promotion | audited proof |
| A saturated target-containing recurrence needs at least four dimensions | promotion | audited proof; determinant core in Lean |
| Every two-dimensional projective or denominator-generating compiler is excluded | rejected | false without saturation |
| A finite support/minrank witness can prove paired zero-language dimension four | rejected | contradicted by the Lean conic factorization |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: finite support/minrank as a lower-bound route; every two-side projective compiler whose
         target law survives independent cancellative inverse completion.
REMAINS: an intrinsically one-way P² recurrence; common-shift incidence obstruction beyond bare
         support; singular ideals that collapse inverse continuations; or a different source.
DISTANCE: construct and punctuate one such one-way recurrence on every source instance, or prove
          that the positive common-shift equations already force the forbidden inverse action.
```

# M₃(2) Cubic Transverse-Pump Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S66` proves an exponentially branching literal first-hit language, but literal spellings
could collapse in the matrix semigroup. Conversely, distinct full products might retain the bit
stack in a transverse coordinate even though the observed source ray erases it. Both questions
need exact adjudication.

## Triangular Chart

Lean verifies the unimodular common-ray chart

```text
B=[[4,1],[3,1]],       B⁻¹=[[1,−1],[−3,4]]
```

and the normalized loop products

```text
N₀=[[1,1712/5625],[0,1/625]],
N₁=[[1,122527/432000],[0,197/336000]].
```

The physical conjugates are `777600000N₀` and `182891520000N₁`. Their induced affine maps are
`f_b(z)=d_b+q_bz`. Lean proves every nested address lies in `[0,1]` and that the two image
chambers are disjoint throughout that interval. The true chamber lies entirely below the false
chamber; its upper endpoint is `429731/1512000`, below `1712/5625`.

## Projective Freeness

For a bit string `β`, Lean derives

```text
Π(N,β)=[[1,A(reverse β)],[0,∏ᵢq_(βᵢ)]].
```

Disjoint chambers make the affine address `A` injective. Any projective equality between two
normalized products has scale one from the upper-left entry, then equal transverse addresses,
hence equal bit strings. Lean proves exact flattening of physical block words and conjugacy with
the product of the nonzero eigenvalue scales, lifting projective injectivity to the physical loop
products themselves.

The two safe physical loops therefore generate a free projective binary monoid while fixing the
same source ray.

## Observation Blindness

The generic theorem is stronger than scalar-identity invisibility. If

```text
Π(R)c=ρv,       Π(L)v=λv,
```

then every left context `A` and row `r` satisfy

```text
rΠ(ALR)c=λ·rΠ(AR)c.
```

For `λ≠0`, insertion of `L` preserves and reflects zero incidence. This requires only that `L`
stabilize the ray reached by `R`; `Π(L)` may be far from scalar.

The fixed suffix reaches `(4,3)` and every binary encoding stabilizes it with nonzero scale.
Lean therefore proves, uniformly in every left physical context, that inserting the entire free
binary stack changes incidence only by its eigenvalue product and never changes whether the
incidence is zero.

## Adjudication

| Claim | Judgment |
| --- | --- |
| the displayed basis and inverse are exact | Lean checked |
| both physical loop charts are exact | Lean checked |
| normalized affine addresses stay in `[0,1]` | Lean checked |
| the two affine chambers are disjoint | Lean checked |
| the affine address is injective on all finite bit strings | Lean checked |
| normalized products have the displayed closed form | Lean checked |
| normalized loop products are projectively free | Lean checked |
| physical loop products are projectively free | Lean checked |
| generic ray-stabilizer insertion scales all contextual incidence | Lean checked |
| nonzero ray-stabilizer insertion preserves and reflects zero | Lean checked |
| every encoded stack is zero-invisible after the fixed suffix | Lean checked |
| the transverse stack has an exact reader in the fixed return grammar | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: a projectively free physical binary stack inside one nonaccepting ray stabilizer
KILLED: any left-context zero reader applied after the ray-reaching suffix
EXPOSED: pre-collapse transverse readout as the remaining compiler seam
NEXT: find a grammar-realizable fork that diverts the transverse coordinate before source collapse
```

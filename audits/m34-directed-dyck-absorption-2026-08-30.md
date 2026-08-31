# M₃(4) Directed-Dyck Absorption Audit

**Date:** 2026-08-30
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `80d02a1` on the detached `m34` worktree

## Verdict

The three rules in Matiyasevich–Sénizergues do not form three prefix or head-separated
productions. Their cancellation rule cannot be removed by a faithful finite-dimensional
algebraic quotient: every finite-dimensional algebra is directly finite, so `PQ=1` forces
`QP=1`. The same collapse holds for complete scalar-value context saturation and, under an
exact projective-separation hypothesis, for zero-context saturation alone.

This closes **absorption**, not the source. The published cancellation is directed and changes
the source decoder by genuine auxiliary computation. An `M₃(4)` construction may still use a
singular, order-sensitive action whose zero contexts fail projective separation and which is
coupled inseparably to the other two rules.

## Actual Three-Rule Source

Matiyasevich and Sénizergues take `u₁=xx̄`, `u₂=x²x̄²` and use

```text
ρ(L)y → ρ(M)y,
u₂³ ρ(dⁿcdⁿ)y u₁² → u₂³ ρ(bⁿ)y u₂²,
xx̄ → ε.
```

The one-step relation has the form `puq→pvq` with arbitrary context words `p,q`; formal
derivations record those contexts. Rule names alone therefore omit redex positions. This remains
true on encoded words: `η₄(b̂)=y u₂⁴ y` already contains several distinct `xx̄` redexes.
The second rule is displayed in the paper with arbitrary Dyck payloads on both sides of its
interior redex.

Put `B=⋃_{z∈A₄} Desc_D(ψ(z))⊂yD₁*`. The complete decoder domain is `(yD₁*)*y`, while the
invariant actually used in the reduction is the strict sublanguage

```text
K_st = Desc_D(Im τ₄) = B* y,        D = {xx̄ → ε}.
```

Proposition 3.11 proves that `K_st` is stable. It does not provide a canonical cancellation
schedule, postponement theorem, or rule-trace reconstruction. The direct compiler `G3-C03` and
the head criterion `G3-C04` therefore do not apply.

## Finite-Dimensional Collapse

Let `A` be a finite-dimensional algebra over a field. If `PQ=1`, left multiplication by `P` is
surjective: `Qv` maps to `v`. Finite dimension makes it injective. Comparing

```text
P(QP) = P = P1
```

then gives `QP=1`. Lean proves this without a matrix basis as
`DirectedCancellation.mul_eq_one_reverse_of_finiteDimensional`.

For a rational scalar series, pass to its finite-dimensional syntactic algebra. Its induced
linear functional is context-faithful: equality of every two-sided scalar context is equality in
the quotient. Hence

```text
f(a xx̄ b) = f(ab)  for every a,b
```

forces the same identity with `x̄x`. Lean formalizes the algebraic implication as
`reverse_value_context_cancellation_of_forward`; the standard syntactic-algebra passage is
audited rather than reimplemented.

## Exact Zero-Language Seam

Mortality needs only zeros. For a selected context family `C`, define `E≈₀F` when

```text
φ(c E d)=0  ⇔  φ(c F d)=0        for every c,d∈C.
```

If these zero contexts determine algebra elements up to nonzero scalar, then
`PQ≈₀1` gives `PQ=s1` for some `s≠0`. Scaling `P` by `s⁻¹`, applying direct finiteness,
and scaling back gives `QP=s1`, hence `QP≈₀1`. Lean proves this for an arbitrary restricted
context set, including a stable source cone, as
`reverse_zero_context_cancellation_of_forward`.

Consequently, an asymmetric zero-only carrier must satisfy all three conditions:

```text
PQ ≈₀ 1,                 QP ≉₀ 1,
PQ is not a nonzero scalar multiple of 1.
```

The last line is not optional; Lean proves it as
`asymmetric_zero_context_cancellation_not_smul_one`. It also states the global separation
contrapositive as `asymmetric_zero_context_cancellation_forces_projective_blindness`. Together
they give a sharply testable construction criterion: the relevant word-context orbit must be
projectively blind to two nonproportional carrier elements. Linear span or ordinary
reachability/observability is insufficient because zero equivalence does not extend through
addition.

## Why the Directed Rule Survives

Replacing `xx̄→ε` by the congruence `xx̄=1` is semantically wrong for the published source.
In Proposition 3.5, Case 3, one deletion shrinks a directed descendant set and its
greatest-lower-bound decoder can move along a nontrivial `S̄₄` path. Thus the third rule carries
auxiliary simulated work. Quotient reachability with the two remaining rules follows in the
forward direction, but its converse is absent: inverse insertions can expose redexes outside the
directed stable cone.

The eight decoded letters form the lattice

```text
          ĉ
         /  \
        b̂    č
       / \    |
      â   b   c
       \ /    |
        a     |
         \   /
           d
```

A surviving construction must retain this directed order, the unbounded word of lattice letters,
and the positional choice of a cancellation. The next constructive test is whether one rank-two
singular action in three states can realize the stable-cone update while also meeting the
nonprojective zero-context condition. Failure of the finite lattice alone is not enough; the
proof must use its unbounded contextual product.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The final source has exactly three arbitrary-substring rules | promotion | MS05, pp. 4, 11 |
| Rule names determine redex contexts or prefix steps | rejected | explicit contexts; multiple encoded `D` redexes |
| Directed cancellations admit a canonical schedule | open | no such theorem in MS05 |
| `xx̄→ε` can be absorbed as `XX̄=I` in finite matrices | rejected | formal direct-finiteness theorem |
| Complete scalar-value saturation can remain oriented | rejected | formal context-faithful theorem |
| Projectively faithful zero-context saturation can remain oriented | rejected | formal zero-context theorem |
| Every zero-only or singular S5 carrier is impossible | rejected | nonprojective, domain-restricted singular actions remain |
| The bicyclic quotient preserves the accessibility converse | open | only the directed-to-quotient implication is immediate |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: direct use of the three S5 rule names as three prefix productions;
         faithful finite-dimensional absorption of the Dyck rule;
         scalar-value saturation and projectively faithful zero saturation.
ADDED:   the exact nonprojective zero-context criterion for every asymmetric carrier.
REMAINS: construct an order-sensitive rank-two singular action on the directed stable cone,
         or prove that its unbounded positional lattice update requires a fourth state.
```

## Artifacts

- [`DirectedCancellation.lean`](../MatrixMortality/DirectedCancellation.lean)
- [`matiyasevich-senizergues-2005-few-rule-semi-thue.md`](../references/matiyasevich-senizergues-2005-few-rule-semi-thue.md)

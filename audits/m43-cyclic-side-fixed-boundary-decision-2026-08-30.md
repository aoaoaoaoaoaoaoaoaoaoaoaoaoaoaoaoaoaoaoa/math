# M₄(3) cyclic-side fixed-boundary decision audit

**Date:** 30 August 2026

**Status:** every positive binary free-group instance with a noninjective side is decidable

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** classify the positive binary fixed-boundary seam left by `M4-M05`

## Verdict

Let `α,β:F({0,1})→F(Δ)` be group homomorphisms and fix four boundary elements. If either
`α` or `β` is noninjective, then the positive fixed-boundary problem

```text
∃w∈{0,1}*: a α(w) b = c β(w) d
```

is decidable. Consequently every hard binary instance, and every binary compiler capable of
carrying the Carvalho marker-tail equation, must make **both** homomorphisms injective.

The result does not decide the injective/injective stratum. That is now the exact surviving
free-cancellation node.

## Cyclic-Side Reduction

Suppose first that `α` has cyclic image. Choose `g∈F(Δ)` and integers `r₀,r₁` such that

```text
α(0)=g^r₀,       α(1)=g^r₁.
```

For a positive word `w`, put `n(w)=r₀|w|₀+r₁|w|₁`. Then `α(w)=g^n(w)`. After multiplying the
boundary equation by fixed inverses, it becomes

```text
β(w)=P g^n(w) Q,       P=c⁻¹a,       Q=bd⁻¹.
```

Work in `F(Δ)×ℤ`. Define

```text
R = ⟨(β(0),r₀),(β(1),r₁)⟩⁺,
C = {(P g^n Q,n):n∈ℤ}.
```

The original instance has a positive solution exactly when `R∩C≠∅`. The set `R` is a finitely
generated submonoid and hence rational. The corridor `C` is rational because it is the union of
the positive and negative rays

```text
(P,0)·(g,1)*·(Q,0),       (P,0)·(g⁻¹,−1)*·(Q,0).
```

Rational subsets are closed effectively under inverse and product, and

```text
R∩C≠∅  ↔  (1,0)∈R⁻¹C.
```

The commutation graph of `F(Δ)×ℤ` is a star, hence a transitive forest. Lohrey and Steinberg's
rational-subset theorem therefore decides the final membership query: Markus Lohrey and
Benjamin Steinberg, “The submonoid and rational subset membership problems for graph groups,”
*Journal of Algebra* 320(2), 728–755 (2008),
[doi:10.1016/j.jalgebra.2007.08.025](https://doi.org/10.1016/j.jalgebra.2007.08.025),
Theorem 2.

The same argument applies when `β` is cyclic by swapping the two sides and their boundaries.

## Binary Noninjectivity

Every subgroup of a free group is free. If the image of a homomorphism `φ:F₂→F(Δ)` were
noncyclic, its two generators would give it rank exactly two. Composing the quotient
`F₂↠im φ` with an isomorphism `im φ≅F₂` would give a surjective endomorphism of `F₂`. Free groups
of finite rank are Hopfian, so this endomorphism, and therefore `φ`, would be injective. Thus a
noninjective binary homomorphism has cyclic image.

Combining this fact with the cyclic-side algorithm proves the verdict for either noninjective
side. No promise about reduced source words, nonempty images, boundary mismatch, or exclusion of
the empty word is used.

## Formal Boundary

Lean proves the algebraic reduction over an arbitrary group and arbitrary finite positive source
alphabet. `CyclicBinaryBoundary.positiveEvaluate_cyclic` collapses the cyclic morphism to its
integer word weight, and
`exists_boundaryEquation_iff_trace_inter_corridor_nonempty` identifies the exact intersection
problem in `G×Multiplicative ℤ`. The Hopfian implication and the rational-subset decision theorem
remain audited paper mathematics.

## Master Delta

```text
MASTER VERDICT: M₄(3) remains open.
REMOVED: every positive binary fixed-boundary compiler with a noninjective homomorphism.
SHARPENED: a successful marker-tail compiler must produce two injective free-group maps.
REMAINS: construct the compiler in the injective/injective stratum, or decide that stratum.
```

## Artifact

[`MatrixMortality/CyclicBinaryBoundary.lean`](../MatrixMortality/CyclicBinaryBoundary.lean)

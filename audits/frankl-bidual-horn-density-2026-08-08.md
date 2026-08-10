# Bidual-Horn density dichotomy for Frankl’s conjecture

Date: 2026-08-08

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

Every bidual Horn Boolean function with at least two false points satisfies Frankl’s
conjecture. The proof combines the true/false closure duality identified by Lozin and
Zamaraev with Karpas’s 2017 half-cube theorem. Lozin and Zamaraev instead state in 2024
that the bidual case remains open and that the self-dual subclass appears challenging.

The result does not improve the universal numerical abundance bound. It removes a
published structural class from the open frontier and exposes a stronger boundary
obstruction for any remaining intersection-closed counterexample.

## Conventions

Let `U=[n]`. For `C⊆2^U` and `i∈U`, write

```text
C_i = {A∈C : i∈A}.
```

A coordinate is *rare* in `C` if `|C_i|≤|C|/2` and *abundant* if
`|C_i|≥|C|/2`. Set complementation is denoted by

```text
C* = {U∖A : A∈C}.
```

This operation must not be confused with family complementation `2^U∖C`.

For a Boolean function `h:2^U→{0,1}`, let `F=h⁻¹(0)` and `T=h⁻¹(1)`.
The Horn condition is equivalent to intersection closure of `F`. Bidual Horn means
that `F` is intersection-closed and `T` is union-closed. A coordinate is good for `h`
exactly when it is rare in `F`, equivalently abundant in `T`.

## The Half-Cube Input

Karpas proves that a union-closed `G⊆2^U` with `|G|≥2^(n−1)` has an abundant
coordinate. The following reconstruction avoids a sign defect in the source and records
the quantitative fact actually used below.

For nonempty `C⊆2^U`, define its downward external degree by

```text
d↓_C(A) = |{i∈A : A∖{i}∉C}|,
D↓(C)   = Σ_{A∈C} d↓_C(A).
```

### Boundary theorem

Let `n≥2`, `0<|C|=ρ2^n≤2^(n−1)`, and suppose every coordinate occurs in strictly
more than half of `C`. Then

```text
D↓(C)/|C| > 2(1−ρ).
```

#### Proof

Put `f=1−2·1_C`, so `f` is `−1` on `C` and `+1` outside it. With the Walsh
character `χ_i(A)=(−1)^[i∈A]`, set

```text
a_∅ = f̂(∅)   = 1−2ρ,
a_i = f̂({i}) = (4|C_i|−2|C|)/2^n.
```

The strict-majority assumption gives `a_i>0`. Also `a_i<1`: equality would force
`f=χ_i` by equality in Cauchy–Schwarz, hence `C={A:i∈A}`; every other coordinate
would then occur in exactly half of `C`, contrary to `n≥2` and the hypothesis.

Let `D↑(C)` count crossing cube edges whose lower endpoint lies in `C` and whose
upper endpoint lies outside `C`. Normalize

```text
J = D↓(C)/2^(n−1),
K = D↑(C)/2^(n−1).
```

Direct edge counting gives

```text
Σ_i a_i = J−K,
I(f)    = J+K,
```

where `I(f)=Σ_S |S| f̂(S)^2` is the total influence. Parseval gives

```text
I(f) ≥ 2−2a_∅²−Σ_i a_i².
```

Since `0<a_i<1`, `Σ_i a_i²<Σ_i a_i`. Substitution therefore yields

```text
J+K > 2−2a_∅²−(J−K),
J   > 1−a_∅² = 4ρ(1−ρ).
```

Finally,

```text
D↓(C)/|C| = J/(2ρ) > 2(1−ρ).
```

This proves the claim.

### Karpas’s theorem

Let `G⊆2^U` be union-closed, contain a nonempty set, and satisfy
`|G|≥2^(n−1)`. Put `C=2^U∖G`, so `ρ≤1/2`. For each `A∈C`, at most one
coordinate `i∈A` can satisfy `A∖{i}∉C`: if two distinct coordinates `i,j`
did, then

```text
(A∖{i})∪(A∖{j}) = A
```

would belong to `G`. Thus `D↓(C)≤|C|≤2(1−ρ)|C|`. The boundary theorem gives a
rare coordinate in `C`; the identity

```text
|G_i| = 2^(n−1)−|C_i|
```

makes it abundant in `G`. The cases `C=∅` and `n=1` are immediate.

This proof uses only the average external-degree bound. Consequently, any nonempty family
`C⊆2^[n]` with `n≥2` and density at most one half satisfying

```text
D↓(C)/|C| ≤ 2(1−ρ)
```

has a rare coordinate. For `ρ<1/2` this strictly extends the pointwise
`d↓_C(A)≤1` mechanism behind the half-cube theorem.

### Source repair

Karpas defines `f=−1` on the simply rooted complement of `G`. Under the displayed
edge definitions in the paper, the correct singleton identity is

```text
f̂({i}) = I_i⁻−I_i⁺,
```

not `I_i⁺−I_i⁻`; Lemma 2.8 bounds the displayed `I⁻`, not `I⁺`. The prose reverses
the labels, and a consistent swap repairs the proof. Gendler’s 2025 weighted
generalization uses a sign-consistent convention and independently corroborates the
uniform theorem. The reconstruction above uses raw edge counts and is independent of
either label.

## Bidual Horn Theorem

**Theorem.** Every bidual Horn Boolean function with at least two false points has a
good coordinate.

**Proof.** Let `F` and `T` be the false and true points. They partition `2^U`; `F` is
intersection-closed and `T` is union-closed.

If `|T|≥2^(n−1)`, Karpas’s theorem gives an `i` with `|T_i|≥|T|/2`. Since every
coordinate occurs in exactly `2^(n−1)` cube points,

```text
|F_i| = 2^(n−1)−|T_i|
      ≤ (2^n−|T|)/2
      = |F|/2.
```

Thus `i` is good.

If `|T|<2^(n−1)`, then `|F|>2^(n−1)`. The family `F*` is union-closed because

```text
(U∖A)∪(U∖B) = U∖(A∩B).
```

Karpas’s theorem gives an `i` with `|(F*)_i|≥|F|/2`. But

```text
|(F*)_i| = |F|−|F_i|,
```

so again `|F_i|≤|F|/2`. The assumption `|F|≥2` excludes the sole one-dimensional
degeneracy in the first branch; the second branch has more than half the cube and is
automatically nontrivial. ∎

Self-dual Horn functions form a subclass, so they satisfy the conjecture as an immediate
corollary. No completion or reduction from arbitrary Horn functions is used.

## Failure Of Naive Self-Dual Completion

One tempting route is to enlarge any complement-free intersection-closed family maximally and
hope that maximality chooses exactly one set from every complementary pair, producing the false
points of a self-dual Horn function. The implication is false on five coordinates.

On `U={1,2,3,4,5}`, let

```text
M = {∅, 3, 23, 34,
     5, 15, 35, 135, 235, 1235, 345, 1345, 2345}.
```

The layer omitting `5` is `{∅,3,23,34}`. After deleting `5`, the layer containing it is

```text
{∅,1,3,13,23,123,34,134,234},
```

the intersection closure of `{∅,1,123,134,234}`. Intersections across the two layers remain
in the first layer, so `M` is intersection-closed. The complement of each displayed set is
absent, hence `M` is complement-free.

It is nevertheless maximal with these two properties. Of the 19 omitted sets, 13 are the
direct complements of members of `M`. The remaining six are

```text
13, 123, 134, 25, 45, 245.
```

Adjoining and taking intersection closure forces, respectively,

```text
1, 1, 1, 2, 4, 2,
```

whose complements `2345`, `2345`, `2345`, `1345`, `1235`, `1345` already lie in `M`.
Thus no omitted set can be adjoined while retaining both properties. But `|M|=13<16`, so
three complementary pairs remain wholly absent and `M` is not self-dual.

This exact obstruction kills maximal completion by inclusion. It does not exclude a
frequency-preserving lift on a larger universe or a non-inclusion transformation into the
bidual class.

## Weighted Extension

Gendler’s Theorem 2.6 yields the following product-measure statement. Let `C` be
intersection-closed and let `μ_p` be the product measure with inclusion probabilities
`p_1,…,p_n`. If

```text
μ_p(C) ≥ max_i p_i,
```

then some coordinate satisfies

```text
μ_p(C_i) ≤ (1−p_i) μ_p(C).
```

Indeed, apply Gendler’s union-closed theorem to `C*` under complementary parameters
`1−p_i`.

A possible universal attack would start from an intersection-closed counterexample at
`p_i=1/2`, tilt the product measure until its mass reaches `max p_i`, and preserve all
strict reverse inequalities along the path. The required persistence is not a
one-coordinate phenomenon.

### Exact failure of homogeneous one-coordinate persistence

Take disjoint blocks `{i}`, `C`, `E`, and `K` with

```text
|C|=|E|=2,   |K|=12,   W=C∪E∪K.
```

On this 17-element universe define

```text
R = {{i}∪B : B∈2^C∪{W}}
    ∪ {∅}
    ∪ {K∪S : S⊊E}.
```

The family has nine sets and is intersection-closed. Intersections inside the upper
layer reduce to intersections in `2^C∪{W}`; intersections inside the lower layer reduce
to intersections of proper subsets of `E`; a mixed intersection is either `∅` or the
lower-layer member itself.

Coordinate `i` occurs in five of the nine sets. Under the homogeneous product measure
`p=x/(1+x)`, remove the common factor `(1−p)^17`. The residual weight polynomials for
sets containing and omitting `i` are

```text
P(x) = (1+x)^2+x^16,
Q(x) = 1+x^12(1+2x),
```

so

```text
Pr_p(i∈A | A∈R) = xP(x)/(xP(x)+Q(x)).
```

The desired strict inequality against `1−p=1/(1+x)` is equivalent to
`x²P(x)>Q(x)`. At `x=11/10`, exact arithmetic gives

```text
Q(x)−x²P(x)
  = 146953492014968519 / 10^18
  > 0.
```

Thus a coordinate that is strictly frequent at the uniform measure can cross the
weighted threshold in an intersection-closed family. This is
not a Frankl counterexample: the two `C` coordinates occur in `3/9` sets, the two `E`
coordinates in `2/9`, and each `K` coordinate in `4/9`. Any viable tilt theorem must use
the simultaneous strict-majority inequalities or choose a genuinely coordinatewise path.

## Priority Boundary

Karpas’s preprint appeared in 2017. Lozin and Zamaraev’s peer-reviewed paper appeared
in 2024, does not cite Karpas, and explicitly says that Frankl’s conjecture remains open
for bidual Horn functions; its conclusion calls the self-dual subclass challenging. No
prior source making the density-dichotomy corollary was located by the 2026-08-08 cutoff.

The search covered exact combinations of “bidual Horn,” “self-dual Horn,” “Frankl,” and
“Karpas”; the indexed forward citations of Karpas; and the forward-citation records of
Lozin and Zamaraev in Crossref, OpenAlex, Semantic Scholar, and public web indexes.
Semantic Scholar returned one forward citation of the Horn paper, DeFranco’s 2026
Boolean-polynomial preprint. Full-text inspection found no discussion of bidual Horn
functions or Karpas. This is a bounded no-prior-source result, not a claim about
unindexed manuscripts or private communication.

## Evidence Boundary

The bidual-Horn theorem and boundary theorem are independently proved above and are
classified as audited. The product-tilt counterexample is exact and its closure check is
included. No Lean formalization was undertaken because this pass proves no better
universal abundance constant; formalization remains optional unless it advances the
universal attack.

## Sources

- [Karpas 2017](../references/karpas-2017-two-results-union-closed.md), Theorem 1.2
  and Lemma 2.8.
- [Gendler 2025](../references/gendler-2025-union-closed-weighted-cube.md), Theorems
  2.5 and 2.6.
- [Lozin and Zamaraev 2024](../references/lozin-zamaraev-2024-frankl-horn-functions.md),
  Conjecture 3 and Section 6.
- [Eiter, Ibaraki, and Makino 1999](../references/eiter-ibaraki-makino-1999-bidual-horn-extensions.md),
  bidual Horn definitions and extension theory.
- [DeFranco 2026](../references/defranco-2026-boolean-polynomials-union-closed.md),
  inspected forward citation of Lozin and Zamaraev.

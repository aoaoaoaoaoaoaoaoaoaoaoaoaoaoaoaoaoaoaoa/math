# Cubical topology and the unique-root boundary

Date: 2026-08-08

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

The Fourier boundary obstruction for a Frankl counterexample has an exact simply rooted
interpretation: the dense cube complement must contain too many sets with a unique root. If a
normalized counterexample `G⊆2^[n]` has density `α`, its simply rooted family complement
`F=2^[n]∖G` must have

```text
q(F) > 2α|F|,
```

where `q(F)` counts uniquely rooted members of `F`.

Bhasin's 2024 acyclicity proof in fact upgrades verbatim to contractibility of the induced
cubical complex when the empty set is present. Contractibility alone cannot supply the contrary
bound: `G={∅}` gives a contractible full cube after adjoining the empty vertex but violates the
desired unique-root inequality by a factor growing with `n`. A viable topological attack must
therefore use the strict coordinate-majority or minimal-counterexample conditions, not only the
homotopy type.

## Roots And Boundary

Let `G⊆2^U` be union-closed and contain `∅`, and put `F=2^U∖G`. For `A∈F`, define

```text
φ(A) = ⋃{B∈G : B⊆A},
R(A) = {i∈A : [{i},A]⊆F}.
```

Because `G` is finite and union-closed, `φ(A)∈G`; it is a proper subset of `A`.
Bhasin's root identity, with the typographical correction described in the source sidecar, is

```text
R(A)=A∖φ(A).
```

Thus `R(A)` is nonempty and `F` is simply rooted.

Define the downward external degree

```text
d↓_F(A)=|{i∈A:A∖{i}∉F}|.
```

There is an exact dichotomy:

```text
d↓_F(A)=1  iff  |R(A)|=1,
d↓_F(A)=0  iff  |R(A)|≥2.
```

Indeed, if `A∖{i}∈G`, then `φ(A)⊇A∖{i}`; since `φ(A)⊊A`, equality holds and
`R(A)={i}`. Conversely, if `R(A)={i}`, then `φ(A)=A∖{i}∈G`. Consequently,

```text
D↓(F)=Σ_{A∈F}d↓_F(A)=q(F),
```

the number of uniquely rooted sets.

If `e(F)` denotes the number of one-dimensional cubes of the induced cubical complex `X(F)`,
every potential downward edge from a member of `F` is either internal or its sole external
edge. Hence

```text
q(F)=Σ_{A∈F}|A|−e(F).
```

This is the precise seam between the Fourier obstruction and cubical face enumeration.

## Counterexample Inequality

Suppose `G` is a Frankl counterexample. Adjoining `∅` if necessary preserves union closure and
makes every coordinate strictly less frequent, so assume `∅∈G`. Write

```text
m=|G|,
α=m/2^n.
```

Karpas's half-cube theorem gives `α<1/2`. The set-complement family

```text
C={U∖A:A∈G}
```

is intersection-closed, has density `α`, and every coordinate occurs in strictly more than
half its members. The downward-boundary theorem in `FC-S02` therefore gives

```text
D↓(C)>2(1−α)m.
```

Set complementation bijects a downward external edge

```text
A → A∖{i}   in C
```

with the downward external edge

```text
(U∖A)∪{i} → U∖A   in F.
```

Thus `D↓(C)=D↓(F)=q(F)`, and

```text
q(F) > 2(1−α)m
     = 2m(2^n−m)/2^n
     = 2α|F|.
```

Any theorem forcing `q(F)≤2α|F|` under the remaining counterexample hypotheses would settle
Frankl's conjecture.

## Contractibility Upgrade

Let `H⊆2^[n]` be simply rooted and contain `∅`. Bhasin proves that `X(H)` is acyclic by
inductively writing, for a maximum member `A`,

```text
X(H)=X(H∖{A}) ∪ X(H_A),
```

where `X(H_A)` is star-shaped and the intersection is `X(H_A∖{A})`. His auxiliary
Lemma 2.20 proves the intersection acyclic by the same two-piece gluing induction.

Every base object and every piece used in these inductions is actually contractible:
elementary cubes and star-shaped cubical sets are contractible, and the auxiliary intersections
are nonempty. The union of two contractible CW subcomplexes with nonempty contractible
intersection is contractible, since the ordinary union is their homotopy pushout. Replacing
"acyclic" by "contractible" throughout both inductions proves:

**Theorem.** If `H` is simply rooted and `∅∈H`, then `X(H)` is contractible.

For the normalized counterexample above, `F∪{∅}` is the family complement of the
union-closed family `G∖{∅}`. Hence `X(F∪{∅})` is contractible.

## Why Pure Topology Stalls

The desired inequality is not a consequence of contractibility, acyclicity, or simple rootedness
alone. Take `G={∅}` on an `n`-element ambient cube. Then

```text
F=2^[n]∖{∅},
α=2^(−n),
q(F)=n,
2α|F|=2(1−2^(−n)).
```

For every `n≥3`, the proposed upper bound fails, while `F∪{∅}=2^[n]` has a cubical
complex equal to the contractible `n`-cube.

The Euler identity is correspondingly too soft. Its proof decomposes the alternating face sum
by top vertex, and each nonempty top contributes zero separately after the minor repair below.
It therefore contains no aggregate control on the number of top vertices with exactly one root.
The remaining high-yield target is a Morse or Laplacian inequality coupling `q(F)` to the strict
coordinate majorities of `F`, or to the separation and minimality conditions on `G`.

## Source Repairs

Bhasin's v1 has three local defects relevant to reuse.

1. Definition 2.1 prints `[{i},A]⊆2^[n]`; it must read `[{i},A]⊆F`.
2. In the first case of the proof of Theorem 1.1, one occurrence of `X(F∖{A})` must be
   `X(F_A∖{A})`.
3. The proof of Lemma 2.16 invokes Proposition 2.15 when `φ(A)=∅`, outside that
   proposition's hypothesis, and its displayed binomial subtraction is then false at the
   bottom vertex. The lemma remains valid: if `φ(A)=∅`, then `[∅,A]⊆F`, so the cubes
   with top `A` form a full Boolean interval and their alternating sum is zero. If
   `φ(A)≠∅`, Proposition 2.15 and the paper's binomial cancellation apply as written.

None of these repairs changes the stated acyclicity theorem. The contractibility upgrade uses
the corrected decomposition in item 2.

## Evidence Boundary

The root-boundary identity, counterexample inequality, contractibility upgrade, and source
repairs are independently checked above and classified as audited. The sought quantitative
upper bound remains conjectural. No formalization was undertaken because no universal
abundance improvement is claimed.

## Sources

- [Bhasin 2024](../references/bhasin-2024-cubical-complements-union-closed.md),
  Propositions 2.13 and 2.15, Lemmas 2.16 and 2.20, and Theorem 1.1.
- [Karpas 2017](../references/karpas-2017-two-results-union-closed.md), half-cube theorem.
- [`FC-S02`](../SALVAGE.md#fc-s02-downward-boundary-obstruction), quantitative Fourier
  boundary theorem.

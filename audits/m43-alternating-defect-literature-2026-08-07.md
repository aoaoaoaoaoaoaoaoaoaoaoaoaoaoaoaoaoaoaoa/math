# M₄(3) alternating-defect and literature audit

**Date:** 7 August 2026

**Status:** the one-coordinate exterior route is fractured; `M₄(3)` remains open

**Superseded route:** the finite cone/multicone tendril below was subsequently excluded by
[`M4-O10`](../SALVAGE.md#m4-o10-irrational-rotation-cone-fracture); it remains here as the search
boundary that led to that obstruction

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** adjudicate the fourth parabolic-blade return, reconstruct the whole `M₄(3)`
frontier, and identify adjacent theories that can change it

## Verdict

The external report explicitly achieved none of its required outcomes: no safe-defect theorem,
safe-return theorem, malformed zero, or reduction. Its displayed recurrences and inverse-phase
identities are exact. Most restate the triangle-coordinate wall or expose equivalent coordinates
without controlling the missing degree of freedom.

One claim survives as a bounded obstruction. The proposed scalar

```text
s = (u+w)/v
```

closes on both residue-zero families and makes the residue-one `b` return wall independent of
the wait, but it is not a state for the residue-one `c` family. The latter depends essentially on
the second projective coordinate `t=w/v`. This retires further one-coordinate recurrence work
unless a new theorem proves that the reachable locus satisfies an exact relation `t=φ(s)`.

No Lean declaration was added. The exact formulas have no present consuming theorem, and encoding
them would enlarge the formal surface without removing a word from the live bridge language.

## Source Lock

The shared report reproduces

```text
PROMPT-ID: M43-ALTERNATING-DEFECT-v4
SOURCE-COMMIT: fb162f181db4bcd24677bd6afb9860f2804152c4
```

The extracted transient artifacts have digests

```text
transcript  b52d0b9e65ef697f4695c6486296dd2e93c24ddbebf1dd3fc62f7b3d37779f0d
report      912726f574b2843ab30c301650c869c1485f4b9fb62b3ffb8bf586f4da493fbc
```

There is no source or branch confusion. A SymPy reconstruction from the pinned atom definitions
checked all four transition matrices, the determinant bridge, all six inverse-phase identities,
and both residue-zero projective maps exactly.

## Return Adjudication

| Reported item | Disposition |
| --- | --- |
| `z(W)=adj(W)ᵀnᵀ`, the triangle change of basis, and `det K(W)=(9ρ/2)u` | correct restatement of the safe-return audit |
| Complete `b0,c0,b1,c1` exterior transition matrices | correct; `b0,c0` already consumed, `b1,c1` unconsumed |
| Wait-free `s` dynamics for `b0,c0` | correct but incomplete |
| Fixed `b1` return wall `s=−2/(12ρ−1)` | correct but does not decide whether the wall is reachable |
| `c1` candidate-wait quotient | correct; exposes the missing projective coordinate |
| Cyclic inverse forms `ℓ₀,ℓ₁,ℓ₂` | correct coordinate reformulation; the uncontrolled coordinate `z` remains |
| Safe return, an alternating-defect cut, or `M₄(3)` | open |

## One-Coordinate Fracture

On the chart `v≠0`, set

```text
s=(u+w)/v,       t=w/v.
```

The residue-zero transitions are

```text
b0: s ↦ s/(9ρ) − (ρ−1)/(6ρ),
c0: s ↦ s/3,
```

and every regular residue-one `b` atom returns to `u=0` exactly on

```text
s = −2/(12ρ−1).
```

For a residue-one `c` atom, write its constant numerator as

```text
C(u,v,w)=a u+b v+c w
```

with

```text
a=(114Lρ−27L−38Mρ−7M−96)/32,
b=(11L−9M−32)/16,
c=(114Lρ−5L−114Mρ+15M+228ρ−280)/32,
α=(3L+2M−9)/2.
```

The candidate natural wait is therefore

```text
j = (a s+b+(c−a)t)/(αs+M−3).                         (1)
```

The second-coordinate coefficient is

```text
c−a = (11L−38Mρ+11M+114ρ−92)/16.                    (2)
```

It never vanishes in the Neary family. Indeed, `ρ≥1`, `M=27Π≥27`, and `L≤M−2`, so the
numerator in (2) is at most

```text
−38Mρ+22M+114ρ−114
  = (−38M+114)(ρ−1)−16M
  < 0.
```

Thus the `c1` return condition varies strictly with `t` at fixed `s` whenever the denominator
in (1) is nonzero. If that denominator vanishes, the residual equation is still `C(u,v,w)=0`
and still depends on `t`. The ambient projective transition is not a function of `s` alone.

This does not prove that two reachable states have the same `s` and different `t`, nor exclude a
hidden invariant graph on the reachable locus. It proves exactly that the report's displayed
scalar is not a closed state without such an additional theorem.

## Formalization Decision

The zero-line prior wins. The recurrences are algebraically correct but none presently composes
with `M4-S03` to remove either alternating phase. The new obstruction is therefore recorded in
the salvage registry and this audit, while the recurrence matrices and inverse coordinates remain
transient. `FORMALIZATION.md` and the axiom snapshot do not change.

## Campaign Census

Victory means a checked many-one reduction proving undecidability of mortality for three
`4 × 4` integer matrices, including nonempty witnesses, arbitrary-word soundness, and
zero-preserving denominator clearing. Two architectures remain.

### Two-state pushout

`M4-C01` is a finished compiler: any undecidable binary scalar source with deterministic
two-state control compiles to two data matrices and one rank-one separator in dimension four.
The missing object is the source theorem. The present Neary source does not provide it:

- exact toggle fusion preserves an immortal anchor (`M4-O01`);
- two private quotient states cannot isolate the exceptional cyclic phase (`M4-O02`);
- every finite queue of complete semantic tokens is decidable (`M4-O03`);
- distinct exact internal and final binary codes force commuting upper images (`M4-O04`);
- direct first-return recoding of the four current roles is reported impossible (`M4-O05`).

Any surviving source must keep an open front or tail, use cancellation, reconstruct state only at
a larger pulse boundary, or abandon exact coefficient preservation.

### Parabolic blade

`M4-M03` supplies a rational open cube root, one rank-two singular atom `R=Q(b,1)`, and the exact
contraction

```text
R M₁ R⋯Mₖ R = 0  ↔  K(M₁)⋯K(Mₖ)=0
```

to `2 × 2` bridges. Lean proves that every zero contains a residue-two atom (`M4-O08`) and that
one residue-two atom cannot vanish at an edge or between equal safe residues (`M4-S03`). The
Archimedean cone `M4-S02` excludes singular nonempty safe bridges made only from residue-zero
atoms. Only one-defect phases `0|2|1` and `1|2|0` survive, followed by arbitrary interactions
among multiple residue-two atoms.

The fourth external attack does not remove either phase. It instead proves that the proposed
scalar exterior compression cannot own the `c1` transition. The parabolic route now needs a
genuinely two-dimensional projective invariant, a finite multicone, an exact returning word, or a
malformed zero. Another catalogue of coordinate recurrences is not a frontier action.

## Literature Map

The local corpus was searched before acquisition. Ten adjacent works now have durable sidecars;
six lawfully redistributable source artifacts are retained. Their exact applicability is:

| Theory | Exact result available | Missing hypothesis at `M₄(3)` |
| --- | --- | --- |
| invariant multicones | finite Markov families in `SL₂(ℝ)` are uniformly hyperbolic exactly when they admit strict multicones; boundary failure has bounded periodic `±I`, parabolic, or heteroclinic witnesses ([ABY10](../references/avila-bochi-yoccoz-2010-uniform-hyperbolicity.md)) | the exterior state is three-dimensional and the wait family is initially infinite and nonunimodular |
| common convex cones | irreducible Perron semigroups of index below three have a common cone; dimensions at most four are classified ([Protasov26v2](../references/protasov-2026-perron-matrix-semigroups-v2.md)) | Perronness quantifies over every product and is not supplied by checking the generators |
| arithmetic invariants | strongest `ℤ`-linear invariants are computable; one-dimensional integer affine reachability has semilinear separators ([LOPW24](../references/lefaucheux-ouaknine-purser-worrell-2024-porous-invariants.md)) | useful nondeterministic semilinear separators need not exist, and the live target is a codimension-one wall in dimension three |
| unimodular regular languages | vector, scalar, and half-space reachability are decidable in `SL₂(ℤ)` or `GL₂(ℤ)` by regular canonical words ([PS19](../references/potapov-semukhin-2018-vector-scalar-reachability.md), [COSW19](../references/colcombet-ouaknine-semukhin-worrell-2019-low-dimensional-reachability.md)) | the bridge family has rational content growth and has not been reduced to a regular unimodular core |
| flat rational subsets | bounded alternation over `GL₂(ℤ)` inside `GL₂(ℚ)` admits membership and singular-target algorithms ([DPS24v6](../references/diekert-potapov-semukhin-2024-flat-rational-subsets.md)) | arbitrary safe contexts permit unbounded alternation; flatness must be proved, not asserted |
| single-base affine groups | rational subsets of `BS(1,q)` have effective pointed-expansion automata ([CCZ20](../references/cadilhac-chistikov-zetzsche-2020-baumslag-solitar.md)) | only the residue-zero `s` projection presently closes in a single-base affine group; `c1` needs `t` |
| `p`-adic orbit interpolation | an étale single-map orbit hits a subvariety on a finite union of arithmetic progressions ([BGT10](../references/bell-ghioca-tucker-2010-dynamical-mordell-lang.md)) | arbitrary noncommuting bridge words are not powers of one map |
| affine reachability | affine-register reachability and determinant-`{1,0}` mortality already have nontrivial complexity in dimension one/two ([JK20](../references/jaax-kiefer-2020-affine-reachability.md)) | no general nondeterministic rational-affine decision theorem may be imported |
| Pólya series | rational series with coefficients in a finitely generated multiplicative group are exactly unambiguous rational series ([BS21](../references/bell-smertnig-2021-noncommutative-polya.md)) | the bridge coefficients have not been proved Pólya; finite denominator support alone is insufficient |
| cancellation sources | inverse-transducer discrepancy implements queue deletion by free reduction with an all-path converse ([Carvalho26](../references/carvalho-2026-free-group-pcp.md)) | its control rank and alphabet are unbounded, and equality return has not been converted to three-generator mortality |

## Ranked Tendrils

### 1. Finite cone or multicone on the exterior system

Every exterior family is affine in its natural wait:

```text
T(j)=T(0)+jD,
```

with `T_b1(j)=T_b1(1)+(j−1)D_b1` for its regular domain `j≥1`. If a convex cone `C`
is mapped into a target cone by both `T(0)` and `D`, then every `T(j)` maps `C` into that
target cone. A finite Markov family of cones therefore reduces all four infinite wait families
to finitely many exact inclusions. Requiring every noninitial cone to avoid `u=0` would exclude
singular nonempty safe bridges; the remaining empty blocks `K(I)` would still require the checked
exceptional-chain analysis. An unavoidable cone-wall crossing would instead point toward a
malformed zero.

This is the most direct use of ABY, Protasov, and porous-invariant ideas. The acceptance object is
an explicit rational polyhedral cone family with parameter-uniform inequalities, or an exact proof
that no cone family of a stated combinatorial type can exist. Numerical pictures are conjecture
generators only.

### 2. Cancellation-driven source architecture

Carvalho's freely reduced discrepancy evades every closed-token obstruction because deletion is
performed by cancellation rather than by a queue of complete positive tokens. A concrete linear
starting point is the four-dimensional action on `2 × 2` matrices

```text
X ↦ g X h⁻¹,
vec(X) ↦ (h⁻ᵀ ⊗ g) vec(X),
```

for which return of `vec(I)` is equality `g=h`. The required audit must count the source alphabet,
compile vector return to mortality without a fourth punctuation generator, and classify every
free-monoid word. Either a three-generator compiler or a lower-bound obstruction would change the
master frontier. This is the best orthogonal route if the parabolic family dies.

### 3. Content stratification and regular `2 × 2` cores

Compute Smith normal forms of normalized bridges and separate scalar content, diagonal expansion,
and a `GL₂(ℤ)` core. A target-wall or determinant argument that bounds nonunimodular factors would
make the surviving language flat, after which PS19, COSW19, and DPS24v6 become applicable. The
residue-zero projection already closes in `BS(1,3)`: with `x=2s` and `ρ=3^β`,

```text
b0: x ↦ 3^(−β−2)x−1/3+3^(−β−1),
c0: x ↦ x/3.
```

Both translations lie in `ℤ[1/3]`. CCZ20 therefore makes the rational-subset structure of this
projection algorithmic. The fracture above proves that it cannot decide `c1` without a
second-coordinate invariant.

The acceptance object is a uniform factorization stable under the bridge grammar and a proof of
bounded alternation. Applying a flat-language theorem to `(A+B)*` without that bound is invalid.

### 4. Fixed-skeleton `p`-adic interpolation

After fixing a residue-one skeleton, the intervening parabolic waits produce polynomial or
linear-recurrence coordinates. If a pumping theorem reduces all successful skeletons to finitely
many periodic macro cycles, each cycle becomes powers of one map and BGT10 or the checked
low-order Skolem machinery can decide its wall hits. The missing theorem is the finite-skeleton
reduction. `p`-adic interpolation does not apply to arbitrary noncommuting words before it.

### 5. Pólya and `S`-unit retirement tests

For a constrained bridge series, proving that every nonzero coefficient lies in one finitely
generated multiplicative group would force an unambiguous rational representation by BS21. This
could show that the zero language is too regular to carry the desired source. Conversely, a small
explicit family of coefficients escaping every such group would retire the test quickly. This is
a falsification lane, not the primary attack.

## Strategy

The next external attack should compare the cone, cancellation, and arithmetic-normal-form routes
before committing. It should develop at least one into an exact theorem, counterexample, or finite
certificate problem. It should not continue the sequence of coordinate recurrences unless the new
coordinate closes the complete safe semigroup or immediately eliminates an alternating phase.

The local campaign should run two independent blades: a finite cone/multicone search against the
current exterior system and a cancellation-based source compiler against `M4-C01`. The former can
close nonempty safe return and reduce the parabolic family to its empty-block incidences, or expose
a structured return; the latter keeps `M₄(3)` alive if the current matrix mechanism is
intrinsically wrong.

## Exact Wound

```text
MASTER VERDICT: still open
REMOVED: the scalar s=(u+w)/v as a complete state for safe exterior return
REMAINS: the alternating one-defect phases 0|2|1 and 1|2|0 under arbitrary safe contexts,
         then multiple residue-two defects; independently, the missing undecidable binary
         two-state controlled source
DISTANCE: prove a parameter-uniform cone/return/malformed-zero theorem that decides the
          parabolic bridge language, or compile an open-tail/cancellation source through M4-C01
```

## Durable Sources

The acquired source records are indexed in [`references/README.md`](../references/README.md).
Raw share transcripts, model reports, symbolic scripts, and the next external prompt remain under
`/tmp` and are not repository artifacts.

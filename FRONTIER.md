# Matrix Mortality Frontier Campaign

Status date: 2026-07-21. A question mark below means “not resolved by any valid result found
in the present literature audit,” not an assertion that no unpublished argument exists.

## The source theorem

The source result is no longer conditional on the Neary–Rote terminal tile:

> **Theorem.** `GPCP(4)` over a binary target alphabet is undecidable, even with empty left
> boundaries, one empty right boundary, and nonempty morphism images.

For Neary's four ordinary pairs, the fixed-boundary equation is

```text
∃w ∈ {R_c,R_b,D_c,D_b}*: U(w)10^β = V(w).
```

A zero-run automaton forces every matching word into exact deletion-width blocks, and a
queue-history theorem proves that those blocks constitute a lawful restricted tag computation.
Conversely, every halting computation emits such a match. This equivalence is formalized in
`MatrixMortality/NearyEncoding.lean`; only Neary's Lemma 9 universality compiler remains an
external published theorem.

Adding a fresh delimiter pair `(10^β#, #)` and fixed-length binary recoding also gives a
corrected five-pair PCP family with primitive terminality. Rote's long unary guard is no longer
used.

Nicolas (2008) and CHHN (2014) explicitly list `GPCP(4)` as open. Exact-phrase searches,
forward-citation inspection of Neary's paper, and inspection of Rote's 2024/2025 versions found
no later statement of this consequence. Rote notices the special terminal role but does not
state the bounded-GPCP improvement. This is a strong novelty indication, not an absolute
bibliographic certificate; author confirmation is mandatory before priority language is used.

## Immediate Cross-Problem Consequences

CHHN's reductions turn `GPCP⁺(4)` into the following results. Rows marked
“new” were open in CHHN's tables; “dominated” adds no new mortality cell after `M₃(5)` and its
propagation.

| Reduction | Consequence | Status relative to CHHN |
| --- | --- | --- |
| CHHN Theorem 6 | structured `Z̊₃(4)` and hence `Z₃(4)` | new |
| CHHN Theorem 7, `h=1,k=3` | `Z₇(2)` | new |
| CHHN Theorem 3 | `R₃(5)` | new |
| `Z₃(4) → R₄(4)` | `R₄(4)` | new |
| `Z₇(2) → R₈(2)` | `R₈(2)` | new |
| `Z₃(4) → M₃(5)` | `M₃(5)` | the main result |
| `Z₇(2) → M₇(3)` | `M₇(3)` | dominated by `M₆(3)` |

Thus the minimal known `Z` undecidability antichain becomes

```text
Z₃(4), Z₅(3), Z₇(2),
```

and the minimal known `R` undecidability antichain becomes

```text
R₃(5), R₄(4), R₆(3), R₈(2).
```

These should be stated as corollaries of the corrected source theorem, not rediscovered through
separate matrix calculations.

## The reusable compiler

The rank-one construction is best viewed as a fixed-boundary compiler. Let `ρ` be a matrix
representation whose letter matrices are nonsingular, and consider

```text
ℓᵀ P ρ(w) S c = 0,
```

where `P,S` encode fixed left and right words. Put

```text
a = (S c)(ℓᵀ P).
```

Then

```text
a ρ(w) a = (S c) [ℓᵀ P ρ(w) S c] (ℓᵀ P).
```

In an arbitrary product, nonsingularity of the `ρ`-blocks makes the two exterior vectors
nonzero; the product vanishes exactly when one internal bridge scalar vanishes. Both fixed
boundaries therefore cost one repeated rank-one generator, not two boundary generators.

This subsumes terminal-tile absorption and the older Claus endpoint construction. Its counting
law is the important limitation:

```text
m active interior tile roles  +  one rank-one separator
                         =  m+1 mortality generators.
```

Boundary-only tiles are free; an interior-active tile is not. Neary's tile 5 is boundary-only,
but tiles 1–4 all remain active. Tile 1 is forced first yet also recurs during the simulation, so
absorbing the initial occurrence does not reduce the active alphabet. Consequently this compiler
is exhausted at `M₃(5)`. Reaching `M₃(4)` by the same route requires a source with at most three
interior roles, equivalently an undecidable `GPCP(3)` family.

## Current mortality staircase

After terminal absorption, dimension padding, and CHHN's generator–dimension trade, the
minimal known undecidable antichain is

```text
M₃(5), M₅(4), M₆(3), M₁₂(2).
```

The immediate unknown cells immediately below this staircase are:

| Cell | What would suffice | Automatic reward |
| --- | --- | --- |
| `M₃(4)` | three-active-role fixed-boundary PCP / `GPCP(3)`, or a new same-dimension generator compiler | also `M₄(4)` and, by CHHN, `M₉(2)` |
| `M₄(4)` | merge one boundary/control role using one extra state | local cell only; its generic trade reaches the already-known `M₁₂(2)` |
| `M₅(3)` | shave one state from the specialized `M₃(5) → M₆(3)` packing | also `M₁₀(2)` and supersedes `M₅(4)` |
| `M₁₁(2)` | shave one state from the specialized `M₃(5) → M₁₂(2)` packing | improves the two-generator threshold by one |
| `M₂(k≥3)` | a qualitatively different decidability or undecidability argument | settles the dimension-two wall |

No further mortality cell follows formally from `GPCP(4)` beyond those already recorded in
`AUDIT.md`. In particular, the improved `Z₇(2)` gives `M₇(3)`, which is weaker than `M₆(3)`.

## Ranked attacks

### 1. Rank-one-aware packing: `M₅(3)`

CHHN's generic `h=2,k=2` construction maps five `3×3` generators to three `6×6`
generators. Our five matrices are exceptional: four are nonsingular PCP matrices fixing `e₁`,
and one is rank one. The target is a five-dimensional reachable/observable realization of this
special packed semigroup.

The obvious quotient does **not** work. CHHN's structured five-dimensional row space relies on
every input matrix having first column `e₁`; the separator `a=ce₁ᵀ` has first column `c`, and
`c` is not collinear with `e₁` because its third coordinate is nonzero. Any successful reduction
must therefore use the rank-one normal form more deeply, alter the packing, or fuse its control
action with the separator.

First experiment: generate the symbolic `6×6` packed pair for generic upper-triangular PCP
matrices and a generic `ce₁ᵀ`; compute common invariant subspaces and minimal
reachable/observable realizations. A generic dimension six is a clean falsification of simple
quotient attacks, after which the search should move to a different word code rather than massage
the same construction.

### 2. Two-generator realization: `M₁₁(2)`

The `h=1,k=4` CHHN code gives two `12×12` matrices. Here the goal is a universal
codimension-one reduction specialized to four PCP matrices plus the rank-one separator. This is
the narrowest numerical target and admits the same invariant-space/minimal-realization audit as
the previous attack.

The common-fixed-vector shortcut again fails when the separator occupies a payload slot: cyclic
shifts move its one-dimensional defect through all four blocks. This obstruction should be
recorded as a symbolic rank certificate, not rediscovered repeatedly. A different cyclic code,
or a code that treats the separator as punctuation rather than as an ordinary fifth letter, is the
plausible escape.

### 3. Boundary/control fusion: `M₄(4)`

The source already provides four active matrices and fixed left/right behavior. A `4×4`,
four-generator construction would have to make one generator serve two semantic modes: an
ordinary occurrence of Neary's recurring start tile and a boundary collapse. One extra linear
state is just enough to make this worth a bounded block-matrix search, but no such construction
is presently proved.

The proof obligation is global. It is insufficient to manufacture the intended zero word; every
arbitrary product must admit a normal form excluding spurious zeroes. Rank of the putative fused
generator is an immediate filter: a rank-one map cannot also carry a three-dimensional interior
state, so boundary collapse must be a multi-letter macro or a state-dependent restriction.

### 4. Source-role compression: `M₃(4)`

This is the highest-value and least incremental target. Neary's four active roles are:

```text
tile 1: initialization and the c-rule,
tile 2: the b-rule,
tile 3: deletion of b,
tile 4: deletion of c.
```

A three-role source could arise by making one deletion implicit, macro-encoding a whole
deletion phase, or replacing the binary tag source by a computational model whose desynchronized
simulation needs only three interior morphism letters. Any such result is essentially a proof of
`GPCP(3)` undecidability and would be a substantial theorem in its own right.

Halava and Holub's reduction-tree analysis at the decidable `GPCP(2)` endpoint gives a second
route to examine: characterize which three-letter instances reduce to binary successors, then
search for an invariant obstruction in the corrected Neary family. This will not prove
undecidability by itself, but it replaces blind tile algebra with the established language of
beginning blocks, end blocks, successors, and suffix complexity.

The fixed-first property alone does not help: tile 1 recurs internally. Apparent word-factor
relations between tiles 2–4 must be checked against arbitrary concatenations; local equality of
one side is not enough and is a prolific source of spurious solutions.

### 5. The dimension-two wall

This is a separate, predominantly decidability-oriented program. `M₂(2)` is decidable. A
minimal mortal word has rank-one endpoints and nonsingular interior factors; Heckman's preprint
further treats every finite family with at most one nonsingular generator. The unresolved core is
therefore a scalar sandwich through a semigroup generated by at least two nonsingular rational
`2×2` matrices.

There is also a sharp arithmetic exclusion. Nuccio–Rodaro, and independently the stronger
membership theorem of Potapov–Semukhin, decide every integer family whose determinants lie in
`{0,±1}`. Thus an unresolved integer instance must include determinant growth: at least one
nonsingular generator has absolute determinant greater than one. The `GL₂(ℤ)` regular-language
method is a solved stratum to generalize, not an open case to reattack.

Potapov–Semukhin go further and decide membership of a *fixed nonsingular target* in an
arbitrary finitely generated nonsingular integer `2×2` semigroup. That does not decide the
scalar sandwich: the mortality target is the infinite incidence variety
`{K : rᵀKc=0}`, and their determinant-growth bound depends on fixing `det K`. This identifies
the precise missing extension: decide intersection of a two-generator nonsingular semigroup
with a rational projective incidence condition, rather than solve singleton membership again.

The first target should be `M₂(3)`, equivalent in CHHN to `Z₂(2)`: classify the projective
orbits of two elements of `GL₂(ℚ)` between finitely many rank-one boundary directions. Natural
tractable strata are simultaneous triangularizability, virtually solvable generated groups,
common invariant rational lines, fixed-determinant monoids extending the unimodular case, and
bounded singular-generator ideals. This lane should not be
mixed with the three-dimensional PCP campaign; the relevant machinery is projective dynamics,
matrix groups, and linear recurrences.

## Execution order

1. Publish-harden the `GPCP(4)` observation alongside `M₃(5)`: author queries, a dedicated
   novelty search, and a manuscript rewrite that treats GPCP as the conceptual source.
2. Build one symbolic packing laboratory and use it to adjudicate both `M₅(3)` and `M₁₁(2)`.
   Preserve negative invariant-space certificates as results.
3. Run a bounded ansatz search for `M₄(4)` only after its admissible word grammar and converse
   invariant are written down.
4. Attack `GPCP(3)` at the source level, beginning with a complete role/dependency graph of the
   corrected Neary simulation rather than ad hoc tile algebra.
5. Maintain `M₂(3)` as an independent decidability campaign with its own bibliography and
   formal statements.

The first item is already a second publishable theorem if the source dependency and novelty
survive author review. The next cells are research programs, not consequences, and are labeled
accordingly.

# M₃(2) Number-Theory Triangulation

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. The
present split-spectrum rank-`(3,2)` family reduces one substantial subproblem to deterministic
rational reachability. At depth two, all odd-resultant laws are already immortal and every
infinite orbit with bounded reduced denominators is eventually periodic. The surviving enemy is
therefore an even-resultant, universal-boundary-passing execution with unbounded reduced
denominators.

The last fixed-frame attack located the unbounded shear but did not bound it. This review asks a
different question: which existing number-theoretic theorem would decide the guard once a small,
exact bridge criterion is proved?

## Arithmetic Signature

Write `qᵢ=p^aᵢ`, let `(rᵢ,tᵢ)` be the primitive endpoint pair, and let `hᵢ,kᵢ` be the forward
and reverse contents. The checked depth-two identities give

```text
hᵢkᵢ = DL(qᵢ−1),
hᵢ=ηᵢuᵢ,      kᵢ=θᵢvᵢ,
ηᵢθᵢ=DL,      uᵢvᵢ=qᵢ−1,
uᵢ,vᵢ>0.
```

Thus every non-base prime in `ηᵢ,θᵢ` belongs to the fixed coefficient support of `DL`; the
moving part is confined to `qᵢ−1`. The Smith decoder is

```text
C(q,u,v) = [[v,q²],[1,(q+1)u]],        det C = −1.
```

The newly checked continuant cut is

```text
C(q,u,v)
  = [[1,v],[0,1]] [[0,1],[1,(q+1)u]],
```

because `uv=q−1`. One branch is therefore a positive shear followed by a Gauss continuant
generator. This is not a metaphorical resemblance to continued fractions; it is an exact
matrix factorization. The obstruction is also exact: changing from wait `q` to the next wait
`Q` inserts the rational gauge

```text
J(q,Q) = [[1,0],[Q²/q²−1,Q²/q²]].
```

The Smith digits are p-adic units, while the distinguished-place expansion is carried by these
`p`-power gauges. A scalar continued-fraction theorem cannot be invoked until the gauges are
absorbed into its partial quotients or into a finite-state macro rule.

The second new checked interface concerns primitive cyclotomic multiplicity. Let `Pₐ(p)` be the
product, with its full exponent in `Φₐ(p)`, of all prime factors not dividing `a`. If no such
prime sees reset in the reduced target, Lean now proves

```text
Pₐ(p) ∣ h,
p^((s−1)a) Pₐ(p) ≤ (|A|+|D|+|L|) H(r,t).
```

At depth two the first factor is `p^a`. This strictly strengthens the former squarefree-radical
gate: multiplicity is retained precisely on the no-reset branch. The literature-guided
strong-part surrogate is also checked. Above wait two,

```text
Φₐ(p) ∣ aPₐ(p),
(p−1)^φ(a) ≤ aPₐ(p),
p^((s−1)a)(p−1)^φ(a) ≤
  a(|A|+|D|+|L|)H(r,t).
```

## Theorem Map

| Result | Exact criterion | Present match | Missing bridge | Consequence if met |
| --- | --- | --- | --- | --- |
| [Capuano-Murru-Terracini, Theorem 4.5](../references/capuano-murru-terracini-2022-adic-finiteness-number-fields.md) | one scalar Gauss recurrence over a number field; locally constant P-adic floor; digits integral away from `P`; adelic factor `ν≤1` or `<1` | `K=ℚ`, `P=(p)`, exact continuant block, deterministic branch selector | absorb `J(q,Q)` and prove the selector is a floor rule; calculate `ν` | `ν<1` forces termination; effective `ν≤1` gives a finite-or-periodic decision box |
| [Capuano-Checcoli-Mula-Terracini, Theorem 4.1](../references/capuano-checcoli-mula-terracini-2026-extraneous-denominators.md) | same recurrence, with a fixed finite set `T` of permitted denominator places and their factors included in `ν` | all non-base Smith support lies over the fixed integer `DL` | same scalar or finite-state conjugacy; prove `T⊆supp(DL)` for every derived digit | closest black-box finiteness theorem for the actual coefficient support |
| [Capuano-Veneziano-Zannier, Theorem 1.1](../references/capuano-veneziano-zannier-2019-adic-periodicity.md) | Ruban digit rule; rational complete quotients either stay nonnegative or enter an effectively bounded periodic tail | guard is rational, deterministic, and p-adically digit-selected | identify a Ruban coordinate and an invariant real sign region | sign failure or repetition decides the orbit |
| [Yasutomi](../references/yasutomi-2025-simultaneous-real-adic-continued-fractions.md) | partial quotients selected jointly at one real and one p-adic place | both places already enter the Smith and readiness estimates | prove the legal wait is the paper's simultaneous nearest-point choice | rational termination by a genuine two-place descent |
| [Murru-Romeo-Santilli](../references/murru-romeo-santilli-2023-convergence-adic-continued-fractions.md) | a prescribed three-phase valuation pattern whose macro-step strictly decreases numerator plus denominator | maximal Smith steps are isolated, so every two-step macro contains a nonmaximal step | construct a bounded-state macro and show the gauge cannot repay its descent | finite rational termination without a global scalar floor |
| [Panti, Theorems 4.3 and 5.3](../references/panti-2020-decreasing-height-continued-fractions.md) | inverse branches of positive unimodular matrices on a covered interval; every infinite symbolic path begins with a height-decreasing block | each Smith decoder is positive, integral, unimodular, split into positive continuant factors, and formally height-increasing on positive primitive input | orient consecutive live states as inverse-decoder branches in one positive cone, or exhibit a complete macro-block cover despite `J(q,Q)` | strict primitive height descent; over `ℚ` the one-block height argument is elementary |
| [Wang-Deng, Theorems 1 and 3](../references/wang-deng-2024-new-adic-continued-fractions.md) | a fixed two- or three-phase p-adic selector; rational numerator-denominator contraction across each bounded block | maximal Smith steps are isolated and every following branch is nonmaximal | identify the guard selector with finitely many phases and prove the exact block denominator inequalities | rational termination with logarithmic qualitative descent |
| [Romeo-Salvatori](../references/romeo-salvatori-2025-adic-continued-fraction-arithmetic.md) | finite input consumption under fixed Möbius transforms, away from valuation ambiguity; unbounded input digit valuations force progress | each frame change is explicit and fractional-linear | the transform varies with two waits; bounded-valuation schedules remain exceptional | eliminate fixed gauges or isolate the bounded-valuation residue |
| [Glasby-Lübeck-Niemeyer-Praeger, Lemma 7](../references/glasby-lubeck-niemeyer-praeger-2017-primitive-cyclotomic.md) | the strong primitive part `Φ⁎ₐ(p)` retains all primitive prime powers and equals `Φₐ(p)` or `Φₐ(p)/r` for `a>2` | the needed elementary surrogate `Φₐ(p)∣aPₐ(p)` and its height consequence are now formalized | exact equality with `Φ⁎` is optional unless the exceptional factor must be classified | an exponential cyclotomic factor is charged to content, not merely its radical |
| [Bugeaud-Evertse](../references/bugeaud-evertse-2017-s-parts-recurrences.md) | fixed nondegenerate integer linear recurrence and fixed prime set `S`; effective power saving with a dominant root or in the binary case | each fixed wait or fixed macro is linear; fixed coefficient support is finite | the legal sequence changes its transfer with every wait | bounds fixed-support cancellation after a fixed-recurrence compression |
| [Bugeaud-Evertse-Győry](../references/bugeaud-evertse-gyory-2018-s-parts-forms.md) | one fixed polynomial with at least two roots, or a sufficiently split fixed binary form; fixed `S` | one-step content is a gcd of explicit binary linear forms | produce one fixed form rather than a moving wait-indexed family | effective power saving for coefficient-prime absorption |
| [Grieve-Wang, Theorem 1.2](../references/grieve-wang-2020-moving-gcd.md) | fixed-rank S-unit points; fixed degrees; coefficient height negligible beside point height | endpoint gcd is a moving-target problem, and the alternative is useful multiplicative degeneracy | encode endpoints in a fixed-rank S-unit torus; current `q−1` factors are not S-units | small gcd on an infinite subsequence or an algebraic subgroup classification of equality |
| [Evertse-Schlickewei-Schmidt](../references/evertse-schlickewei-schmidt-2002-multiplicative-linear-equations.md) | bounded-term linear equation in one finite-rank multiplicative group; nonvanishing proper subsums | terminality is linear after expanding a fixed word | raw word length increases both term count and apparent rank | finitely many nondegenerate terminal patterns after a bounded-term compression |

No theorem in the table applies by nomenclature alone. The CMT/CCMT criterion and Panti's
rational positive-block argument are close enough that their missing hypotheses are concrete
algebraic obligations rather than an invitation to invent a new Diophantine theory.

## Route A: Positive Unimodular Blocks

This is the cheapest possible closure and should be tested before building a new adelic
formalism. Over `ℚ`, Panti observes that if `A∈PSL₂±(ℤ)` is positive and `β>0`, then

```text
H(Aβ) > H(β).
```

Every Smith decoder meets the matrix hypothesis: its entries are positive, its determinant is
`−1`, and the continuant cut is checked. Lean also verifies the exact rational conclusion:
on positive coprime input the decoded pair remains coprime and has strictly larger primitive
height. It would therefore suffice to construct positive vectors `zᵢ` such that every legal
step, or every bounded macro, has the orientation

```text
zᵢ = Cᵢ zᵢ₊₁,
```

possibly after multiplication by a scalar whose removal does not change primitive height.
Then `H(zᵢ₊₁)<H(zᵢ)` and an infinite rational execution is impossible.

The present decoder identity does not yet supply this relation. It maps a mixed vector built
from the source and target denominators to the Smith quotient; it is not already a transfer
between two copies of one orbit coordinate. The precise bridge is thus:

1. choose a single projective coordinate carried from one branch to the next;
2. prove its primitive representative remains in one positive cone;
3. orient the Smith decoder as the inverse branch on that coordinate; and
4. absorb `J(q,Q)` into a positive macro matrix, or prove that the gauge scalar disappears on
   primitive reduction.

If the fourth obligation fails, Panti's complete-decreasing-block construction still suggests
the right repair: enumerate branch shapes, not wait values, and prove every infinite legal word
begins with a strict block. Smith maximal isolation and the Wang-Deng finite-phase contractions
make a two- or three-phase candidate natural. A failure here should produce an explicit sign or
gauge counterexample rather than another qualitative obstruction.

## Route B: Adelic Continued-Fraction Finiteness

This is the robust fallback if the cheaper positive-block orientation fails. There are two
legitimate versions.

### Scalar bridge

Construct an augmented coordinate `(σᵢ,αᵢ)`, with `σᵢ` in a fixed finite set, such that one
legal step or bounded macro satisfies

```text
αᵢ₊₁ = 1/(αᵢ−a(σᵢ,αᵢ)),
σᵢ₊₁ = δ(σᵢ,aᵢ).
```

The proof obligations are:

1. `aᵢ` depends only on a locally constant p-adic cell of `(σᵢ,αᵢ)`.
2. Every `aᵢ` lies in `ℤ[1/p,1/T]` for one coefficient-computable finite set
   `T⊆supp(DL)`.
3. The terminal guard ray is exactly termination of this expansion.
4. The CCMT adelic factor satisfies `νguard≤1`, with a strict inequality on every
   nonmaximal macro.
5. Equality macros form a finite class and cannot repeat except in an already detected cycle.

The continuant cut supplies the matrix shape for obligation 1, and `ηθ=DL` supplies obligation
2. Obligations 3 and the deterministic physical equivalence are already available in the
existing decoder and integral lift. The real work is the floor rule and `νguard`.

### Matrix-valued bridge

If scalarization introduces ceremonial state, reproduce the proof of CMT Theorem 4.5 directly
for the gauged `2 × 2` cocycle. This needs only:

```text
H(xₙ₊₁)^d ≤ C H(x₀)^d ∏ᵢ ν(Mᵢ),
```

with the local factor built from the distinguished p-adic scale, all Archimedean operator
norms, and the fixed places over `DL`. The moving ratio `Q²/q²` is a pure p-power. Its real and
p-adic sizes are product-formula duals, so it should be charged adelically rather than bounded
as an Archimedean error. This is the most promising new thread from the review: the gauge that
destroyed a real-norm contraction may be neutral in the exact all-place accounting for which
the CMT criterion was designed.

The checked Smith estimate gives a `3/4` Archimedean saving on every `v≥2` branch. Maximal
`v=1` branches are nonterminal and isolated, so a two-step adelic macro always contains one
candidate strict factor. A successful calculation would yield one of two closures:

```text
νmacro < 1                 ⇒ every rational guard execution terminates;
νmacro ≤ 1, equality finite ⇒ bounded height, repetition, and decision.
```

The calculation must use the exact gauged recurrence. Reusing the retired ungauged cocycle
would be false.

## Route C: Strong Primitive Pressure

The prior radical gate lost all multiplicity and therefore could not exploit the size of
`Φₐ(p)`. That loss was unnecessary on the no-reset branch.

For `a>2`, GLNP proves that the strong primitive part is `Φₐ(p)` or `Φₐ(p)/r`, where `r` is the
largest prime divisor of `a`. The formalization now proves the exact weaker interface needed
here without importing a second definition:

```text
Φₐ(p) ∣ aPₐ(p),
(p−1)^φ(a) ≤ Φₐ(p).
```

The proof reconstructs the source's decisive arithmetic: at most one prime dividing `a` can
occur nonprimitively in `Φₐ(p)`, and above exponent two its valuation is exactly one, including
the two-adic case. Combining that theorem with the formal pressure inequality yields, whenever
no primitive quotient sees reset,

```text
p^a (p−1)^φ(a) ≤
  a (|A|+|D|+|L|) H(r,t).                     (∗)
```

Equation `(∗)` is now kernel-checked in
`ReturnGuard.strongPrimitivePressure_le_height_of_no_reset`. The exact GLNP equality remains
useful for classifying the single exceptional index prime, but is no longer a prerequisite for
the growth inequality.

This does not decide the orbit by itself. Height may have accumulated before a large wait. Its
value is that it supplies a strict dichotomy at every large branch:

```text
primitive reset in an exact-order finite quotient
or
full strong primitive mass paid by the same content that pays p^a.
```

That dichotomy can feed Routes A and B. Reset branches enter the finite automata already formalized;
no-reset branches acquire an additional adelic/content loss. The two results attack opposite
sides of the same branch and leave no untyped “cyclotomic cancellation” case.

## Route D: Classify the Equality Locus

If the adelic calculation reaches only `ν≤1`, the equality branches should not be attacked by
generic height estimates. They are an arithmetic degeneracy locus.

The dependency order is:

1. Express equality as simultaneous saturation of Smith contraction, content allocation, and
   the p-power gauge product formula.
2. Reduce those equalities to a fixed binary form or fixed-rank S-unit point.
3. Apply Bugeaud-Evertse-Győry for effective fixed-`S` power saving when a fixed form emerges.
4. Apply Grieve-Wang when coefficients move slowly; its exceptional alternative then gives a
   proper multiplicative coset to classify.
5. Use Evertse-Schlickewei-Schmidt only after the terminal equation has bounded term count and
   fixed multiplicative rank.

The existing maximal-step theorem is already one such classification: `v=1` is nonterminal and
cannot occur twice consecutively. This is precisely the kind of equality rigidity the adelic
argument needs.

## Rejected Shortcuts

- A bare appeal to “S-unit equations” is too broad. The raw orbit has factors of `p^a−1` at
  unboundedly many primes and does not lie in a fixed-rank multiplicative group.
- A linear-recurrence `S`-part theorem does not apply while the wait changes the recurrence at
  every step.
- Northcott alone repeats the fixed-frame quantifier failure unless a coefficient-computable
  height bound is first proved.
- Möbius invariance is not free. Romeo-Salvatori explicitly shows that bounded-valuation inputs
  can require unbounded lookahead under a fixed transform.
- Cyclotomic-value growth alone is insufficient on reset branches. The full-part theorem is
  useful because the alternative is now an exact finite quotient, not because every branch
  must swallow `Φₐ(p)`.

## Attack Order

1. Test the positive-block bridge: seek one carried primitive coordinate for which a legal
   macro is the inverse of a positive Smith product. Either obtain strict rational height
   descent or record the exact sign/gauge counterexample.
2. If no positive block covers every branch, calculate the adelic norm of the exact gauge
   `J(q,Q)` at infinity and at `p`; determine whether its wait ratio is product-formula neutral
   in the CMT height recurrence.
3. Combine that calculation with the checked `3/4` Smith loss and maximal isolation over a
   two-step macro. The Wang-Deng three-phase schedule is the next bounded-state shape if two
   phases do not close.
4. If the macro factor is strictly below one, close the rational guard by a matrix-valued CFF
   proof and then transport through the physical mortality equivalence.
5. If equality remains, extract its algebraic equations before invoking moving-gcd or S-unit
   theorems. Do not search those literatures without a fixed-rank encoding in hand.
6. Use Ruban positivity or simultaneous real/p-adic selection only on coefficient cones where
   the required digit rule can be proved exactly.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GUARD VERDICT: the unbounded-denominator even-resultant stratum remains open
NEW FORMAL WOUND: no primitive reset forces the full primitive cyclotomic part, with multiplicity, into content and into the p^a-weighted height budget
PRIMARY BRIDGES: positive Smith macro -> primitive height descent; failing that, exact gauged Smith cocycle -> adelic CFF inequality
COMPLETED BRIDGES: positive Smith decoding preserves primitivity and strictly raises rational height; Φₐ(p) divides a times primitiveCyclotomicPart, yielding formal strong primitive pressure
HARDEST KNOT: absorb the p-power frame gauges without letting them repay every isolated Smith loss
```

# M₃(2) Renewal-Collapse Audit

Date: 2026-08-07

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. This
ratchet concerns the split-spectrum rank-`(3,2)` guard after the periodic-shadow obstruction.
The submitted attack tested a reset-anchored dichotomy: either shadow depth is effectively
bounded and yields a finite endpoint box, or a positive-depth renewal cycle constructs an
infinite orbit.

Both arms fail in that form. The positive-cycle arm contradicts the exact branch similarity
already formalized in `ReturnGuardGap.lean`. The finite-box arm fails even with fixed
coefficients, wait, content, Smith label, and remaining shadow depth. What survives is a new
exact reset-pullback determinant identity and a moving-reference compactness problem.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the endpoint transfer has determinant `DLp^(sa)(1−p^a)` | restatement | already checked by `endpointTransfer_det` |
| a fixed wait word has at most one legal rational periodic ray | correct, culled | follows from exact common-branch expansion; words still form an infinite parameter set |
| the primitive-normalized periodic multiplier has p-adic weight `−s∑aᵢ` | restatement | the same law is already `residualRun_sub_hasValue` |
| an aligned legal macro increases shadow depth | rejected | every nonempty aligned macro strictly consumes its full positive schedule weight |
| a finite cycle of honestly transported reference rays can have nonnegative total depth gain | rejected | its edge weights sum to `−s∑aᵢ<0` |
| a misaligned ray switch supplies an iterable positive weight | rejected | deep inputs are capped at the fixed ray-separation depth; excess depth occurs only on one threshold shell through leading-residue cancellation |
| bounded shadow depth and fixed local labels imply bounded endpoint height | rejected, formalized | one fixed guard has arbitrarily high legal endpoints and carried pairs at exact remaining depth two |
| reset ancestry is an exact adjugate determinant | promotion | formalized for every cumulative endpoint execution and every integral reference ray |
| the moving-checkpoint repetition bound is new | restatement, culled | it composes the checked moving return-depth inequality with the checked height envelope and still depends on the checkpoint position |
| the renewal dichotomy decides the guard | rejected | both proposed arms fail, and no global compactness extraction or infinite reset orbit was obtained |

## Existing Blade

For a legal wait word `w`, the checked rational guard calculus proves

```text
vₚ(F_w(x)−F_w(y)) = vₚ(x−y) − s∑w
```

whenever both points follow `w` and their difference is nonzero. This is
`ReturnGuard.residualRun_sub_hasValue`; branch persistence under a sufficiently deep
perturbation is `ReturnGuard.followsResidualSchedule_of_deep_sub`.

Consequently every honest renewal edge which transports its reference ray has strictly negative
depth weight. A finite aligned ray cycle sums those negative weights and cannot preserve or
increase depth. For a misaligned target ray `β`, write `η=F_w(α)`. Then

```text
F_w(x)−β = (F_w(x)−η) + (η−β).
```

The ultrametric equality says that sufficiently deep inputs have output depth exactly
`vₚ(η−β)`. Extra cancellation is possible only when the transported perturbation and ray
separation have equal valuation. It is residue-specific, not a macro weight. No new Lean wrapper
was retained for these immediate consequences of the stronger checked similarity theorem.

This kills the proposed fixed macro `d ↦ d+δ`, `δ>0`, and every finite cycle assembled from such
aligned macros. It does not exclude an aperiodic orbit which changes its reference ray, word, or
threshold residue at every episode.

## Reset Pullback

Let a cumulative endpoint execution with wait prefix `u` satisfy

```text
M_u P₀ = p^(s∑u) Pᶜ_u,
```

where the cumulative target `Pᶜ_u` absorbs all primitive normalization contents. For every
integral reference ray `V`, Lean now proves

```text
Δ(P₀, adj(M_u)V) = p^(s∑u) Δ(Pᶜ_u,V).
```

This is `CumulativeEndpointExecution.pullback_projectivePairCross`. If
`Pᶜ_u=H_uP_u` for the primitive endpoint `P_u`, bilinearity gives the submitted form

```text
Δ(P₀, adj(M_u)V) = p^(s∑u)H_u Δ(P_u,V).
```

Thus a depth-`d` shadow reached from reset is exactly divisibility by `p^(s∑u+d)` in one pulled-
back integral determinant. The identity retains signs and every normalization scalar. It does
not impose fixed prime support: both the endpoint product and a periodic reference ray may carry
prime factors from the varying cyclotomic terms `p^a−1`.

## Local Compactness Fails

For the fixed guard

```text
(p,s,A,D,L)=(3,2,17,−5,16),    reset=3/4,
```

Lean now strengthens the periodic-shadow obstruction. Given any bound `B`, there is a legal
off-reset wait-one primitive edge with content `−4`, Smith coordinate `v=2`, and primitive
carried pair `X=(t,−4t′)` such that

```text
v₃(X₂/X₁+4)=2,
H(endpoint)>B,
H(X)>B.
```

This is `ReturnGuard.Examples.periodicShadow_shatters_localCompactness`. The witness is the
penultimate edge of a sufficiently long checked shadow corridor. Its remaining depth relative
to the carried ray `x=−4` is always exactly two, while the common endpoint denominator tends to
infinity.

Therefore no finite endpoint box follows from shadow depth plus the finite wait, content, and
Smith labels. A valid compactness theorem must use the complete reset ancestry encoded by the
pullback determinant, not episode-local data.

## Culling

No periodic-ray structure, cross-ratio multiplier, shadow-episode type, renewal graph, or moving
checkpoint API was added. The periodic multiplier and exact depth consumption restate the
checked rational similarity. The moving power bound follows from
`repeatedMacro_returnDepth_le`, `primePower_le_rationalPairHeight`, and the checked height
envelope, but retains the moving prefix position and yields no coefficient-only orbit bound.

The only new public declarations are the reset-pullback identity and the direct local-
compactness counterexample. They respectively identify the surviving arithmetic object and
destroy the false implication aimed at it.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GUARD VERDICT: the reset-started even-reset-defect unbounded-denominator stratum remains open
REMOVED: fixed positive-depth renewal macros and finite aligned renewal cycles; bounded shadow depth plus fixed local labels as a route to a finite endpoint box
REMAINS: an essentially moving reset-ancestry problem in which height diverges with bounded depth to every fixed ray, or threshold cancellations visit infinitely many rays or macros
DISTANCE: prove an effective compactness theorem extracting one fixed recurrent ray/macro at unbounded depth, contradicting exact expansion, or directly bound the pulled-back determinant family; otherwise construct one exact aperiodic infinite reset orbit realizing the moving-ray alternative
```

## Artifact

The reset-pullback theorem is in
[`ReturnGuardCumulative.lean`](../MatrixMortality/ReturnGuardCumulative.lean). The fixed-depth
unbounded-height theorem is in
[`ReturnGuardPeriodicShadow.lean`](../MatrixMortality/ReturnGuardPeriodicShadow.lean).

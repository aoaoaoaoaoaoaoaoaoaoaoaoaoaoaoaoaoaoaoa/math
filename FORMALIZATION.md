# Formal Verification

The Lean development verifies the complete computable source reduction and the matrix compilers:

```text
mathlib code halting at input zero
  ↔ halting of one fixed binary TM0 machine
  ↔ halting of one fixed finite-alphabet two-tag system
  ↔ a distinguished firing in one fixed cyclic-tag system
  ↔ halting of the emitted restricted binary-tag system
  ↔ solvability of the emitted binary four-letter GPCP instance
  ↔ mortality of the emitted five 3 × 3 integer matrices;

four-tile terminal equation
  ↔ restricted tag halting
  ↔ corrected binary five-pair PCP
  ↔ four-generator GPCP
  ↔ mortality of the emitted five 3 × 3 integer matrices;

four-tile terminal equation
  ↔ scalar zero reachability for three 4 × 4 integer matrices
  ↔ mortality of the emitted four 4 × 4 integer matrices;

four-tile terminal equation
  ↔ scalar zero reachability for two 6 × 6 integer matrices;

for each fixed deletion width β:
four-tile terminal equation
  ↔ scalar zero reachability for two (β+2) × (β+2) integer matrices;

mortality of the emitted five 3 × 3 integer matrices
  ↔ mortality of two 10 × 10 integer matrices
  ↔ mortality of two (10+n) × (10+n) integer matrices.
```

The final `GPCP(4)`, `M₃(5)`, `M₄(4)`, `Z₆(2)`, and `M₁₀(2)` constructors are primitive
recursive. Lean proves the corresponding many-one reductions and no-decider theorems from
mathlib's halting theorem. No external universality theorem, Neary's defective terminal-pair
converse, or Rote's long-block repair is assumed.

## Checked Scope

The universal source chain is executable. Lean reifies mathlib's partial-recursive evaluator as
one fixed finitely supported binary `TM0` machine, normalizes it to the read-state form consumed by
the Cocke–Minsky compiler, and emits a fixed finite two-tag system whose variable initial queue is
primitive recursive in the source code. Forward simulation reaches one last-labelled halt symbol
without reading it early; every terminating tag execution and every queue headed by that label
reflects source-code halting.

The one-hot cyclic compiler preserves that avoidance invariant and reflects every distinguished
firing. The Table 2 compiler then proves both directions for every emitted source: protected
execution gives halting, while its arbitrary-execution converse excludes spurious halting after
the semantic data are exhausted. Its body, padding, ternary arithmetic, four-letter GPCP instance,
and five-matrix integer family are all primitive recursive. The five `codeHalts_reduces_*`
declarations are therefore complete computable many-one
reductions; their corresponding `*_not_computable` declarations are unconditional
kernel-checked no-decider theorems.

For deletion width `β`, body `q`, rules `b ↦ b` and `c ↦ q ++ [b]`, and initial queue
`q.drop (β−1) ++ [b]`, Lean proves under

```text
2 < β,    β−1 ≤ q.length,    β−1 ∣ q.length
```

that a word over Neary's four ordinary labels satisfies

```text
upper(w) ++ 10^β = lower(w)
```

if and only if the restricted tag system halts. The forward theorem accepts an arbitrary label
word. A zero-run automaton forces exact deletion-width blocks; prefix cancellation turns the
decoded history equation into lawful tag steps and stops at the first short queue.

The development also checks the fresh-marker fifth pair, fixed-length binary recoding,
primitive terminality, the ternary word-pair representation, the exact integer generators, and
the mortality converse for every nonempty word over all five labels. The four ordinary matrices
are nonsingular and upper triangular. The fifth is nonzero and has rank one over `ℚ`.

The exact Neary role pairs admit no nonerasing rolewise macro factorization through an alphabet
of cardinality below four. The formal statement permits arbitrary unequal macro lengths and
noninjective role codes. Erasing morphisms, target recoding, context-dependent codes, boundary
residuals, and solvability-only transformations remain outside its scope.

For the `4 × 4` compiler, Lean checks the side-separating change of basis, agreement of each
rule/erasure pair on the complete upper-word plane, and the explicit four-dimensional paired-role
representation. A right-to-left transducer decodes every arbitrary control word, and a constructive
surjectivity theorem encodes every four-role word. The three control matrices have common first
column `e₁`, and the toggle is an explicit permutation matrix. Adding the nonzero rank-one matrix
`CL` gives four integer matrices; the mortality converse covers every number and placement of
separators without assuming that control products are invertible. The two data controls are
singular; the toggle is an invertible permutation matrix.

Lean also certifies exact minimality of the paired scalar series. Four prefixes and four suffixes
over `{b,t}` give reachable and observable determinants

```text
48u(13a−15),      12p(s−3),
```

which are nonzero for every deletion width `β≥3` and every body. A generic finite-Hankel
factorization therefore forces every exact rational realization to have at least four states.
The generic two-channel boundary-tax theorem proves that any exact diagonal bridge adds two more
states; its inactive row and column need only be nonzero. Consequently every exact diagonal
two-channel realization of the paired series has at least six states. These declarations say
nothing about another series with the same zero set or an off-diagonal bridge.

For the `6 × 6` scalar compiler, Lean checks both explicit integer generators and a total
two-bit decoder on the complete binary free monoid. Complete pairs emit the four source roles;
an odd final bit preserves the coefficient. The decoder is surjective, the empty coefficient
is nonzero, and transposition plus word reversal gives two generators with common first column
`e₁`. The terminal equation is therefore equivalent to scalar zero reachability under both the
free-monoid and nonempty free-semigroup conventions.

For the scheduled binary compiler at deletion width `β`, Lean checks two explicit
`(β+2) × (β+2)` matrices. The input bit selects the tag letter; its position modulo `β`
selects deletion or rule semantics. A total decoder assigns a role to every bit, and the
coefficient identity holds for every binary word over every commutative ring. Reversed stroke
encoding is surjective onto every tile history. If a coefficient vanishes, the terminal-match
normal form forces a complete tile history, so `β` divides the binary-word length. At width
three and nonempty body, a symbolic `5 × 5` Hankel minor is nonsingular. Every exact rational
representation of the same series therefore has at least five states, matching the native
five-state representation.

For the `10 × 10` mortality compiler, Lean first checks a complete prefix transducer for the
code `0, 100, 101, 110, 111`. Its block-row theorem covers every binary word and every starting
prefix state. The word `00` synchronizes all four states, so mortality of the twelve-state
binary realization is equivalent to mortality of the normalized five-matrix source. Two shared
rows place both binary generators in a common ten-dimensional image. Explicit integral
embedding and retraction matrices prove the exact restriction and its converse, including any
new zero created by restriction. A generic zero-block theorem then preserves nonempty-word
mortality in every dimension `10+n`.

Lean also constructs the canonical reachable-observable quotient around any internal physical
word whose product factors as `UW`. Its generators act on

```text
span{A_w im U} / {x : WA_wx=0 for every w}.
```

Mortality passes down to the quotient. Every zero quotient word `z` lifts through the entirely
physical repair word `ωzω`, so no parser or malformed-word hypothesis is present. The
zero-dimensional branch is mortal upstairs. The quotient is linearly equivalent to the span of
the flattened block-Hankel columns `q ↦ (WA_uA_vUq)_u`; its dimension is their rank and is no
larger than the state dimension of any exact realization. Independent nonzero rescaling of
matrix generators preserves mortality, which supplies the algebraic denominator-clearing step.

Lean further proves a generic full-algebra certificate for a physical rank-one word. If finitely
many left contexts send its column to a basis and finitely many right contexts send its row to a
dual basis, their physical sandwiches span every matrix unit. For the canonical paired-binary
six-state mortality family, sparse six-column and six-row context matrices are invertible for
every `β≥3` and every body. Their final pivots are integer expressions congruent to `3 mod 9`
because the rule-`c` lower word ends in `10`. The thirty-six physical products around the
canonical separator therefore span `M₆(ℚ)`. This excludes every exact invariant restriction,
quotient, and internal-word sandwich compression of that physical family to five states; it
does not exclude another family or a same-zero realization.

The exact-series interfaces now share one primitive:

```text
word ↦ output ∘ A_word ∘ input.
```

Scalar rational series are its one-dimensional specialization, and the internal-sandwich
predicate represents the same matrix-valued behavior. Lean connects full physical word span to
this interface: a nonzero input makes the reachable carrier top, a nonzero output makes the
unobservable carrier bottom, and every exact realization then has at least the ambient number
of states. These statements are
`quotient_finrank_eq_card_of_wordProductSpan_eq_top`,
`pairedBinaryMortality_exactSandwich_six_le_finrank`, and
`prefixAlgebra_exactSandwich_ten_le_finrank`.

The restricted ten-state prefix pair is now closed by the same generic theorem. Lean proves
`B₀³=uvᵀ`, constructs ten reachable columns and ten observable rows, and proves both context
matrices invertible throughout `β≥3`, `body.length≥β−1`. Its large reachability factors are
nonzero by the sharper congruences `P(3^β)≡8 mod 9` and
`Q(3^β,V_c^R−25)≡3 mod 9`. The resulting one hundred physical sandwiches span
`M₁₀(ℚ)`. This is [`MM-O08`](SALVAGE.md#mm-o08-full-algebra-prefix-pair), formalized by
`prefixAlgebra_wordProductSpan_eq_top`.

The rank-three binary campaign now has a checked structural core. A split finite-rank cut beside
a unit fractures every arbitrary binary word into its `VAⁿU` return product; a finite
block-Hankel section lower-bounds every exact realization of that matrix-valued sequence. For
two rank-two generators, Lean compresses every nonempty word to the adjacent-edge product
`VᵢUⱼ`. It also proves the converse geometric construction: four `2 × 2` edges agreeing on one
shared source line assemble into two `3 × 3` generators, and split incoming edges force both
generators to have rank exactly two. For the generic projective-incidence reverse construction
`αβ≠0`, Lean now checks the independent basis changes, the rank-one loop fracture, the complete
constrained-path grammar, and both mortality implications. The exceptional projective points
remain outside the many-one compiler.

ReturnSquare instantiates the rank-`(3,2)` reduction. Lean proves the closed return matrix,
split interfaces, exact cut rank, internal rank-one zero-wait return, unit positive returns,
complete physical mortality equivalence, reachable and observable determinants, and the
one-return/long-word dichotomy. A discriminant trapped between parity-compatible neighboring
squares excludes every bridge of two positive returns. The reversible stack variant has a
nonsingular `4 × 4` block-Hankel section, so no exact three-state return realization can perform
that literal push/pop operation.

The stronger quadratic-pencil no-go is also checked over every linear ordered field. Three
singular coefficient modes `C₀+tC₁+t²C₂` cannot projectively exchange `t` with `κt²`; all three
coefficients are forced to zero. Requiring exact squaring at both scales `t` and `qt` instead
forces the pencil to be a scalar linear polynomial times `diag(t,1)`, hence blind scaling rather
than verification.

The projective wall is checked without affine-chart pole assumptions. For `c=−d`, define

```text
s_d(t)=(d−1)t²+1,       β_d(q)=q/s_d(q).
```

If `q≥2`, `t≥q`, and `d>1+(q−1)/q²`, the homogeneous double cone representing slopes
`(0,β_d(q)]` is backward invariant under the return at scale `t`, for either vector sign.
Pulling a zero bridge through all returns would place `[1,1]` in that cone although
`β_d(q)<1`. Lean therefore proves immortality throughout this outer negative half-line, as well
as throughout `c≥0`.

The arithmetic classification is now complete whenever `q` is a prime power. The normalized
bridge polynomial has constant coefficient `T` and leading coefficient `±T²`. Rational-root
support confines every positive root to one prime. The corpus proves the required
Bang–Zsigmondy theorem for every base greater than one above exponent two, handles its
`(2,6)` exception explicitly, and uses fixed- or two-ray finite quotient certificates to
exclude every nonresonant reciprocal. Thus prime-power ReturnSquare is mortal exactly at
`c=−q⁻ᵐ`.

Two further return architectures are checked. The exact parity-Collatz pencil
`C₀+(−1)ⁿC₁+n(−1)ⁿC₂` has one rank-compatible normal form under the stated singularity,
tangency, and positive-return hypotheses; its physical pair preserves a nonzero line modulo
seven and is immortal. In contrast, the two-scale modes `(1,p,q)` produce a minimal
three-state pencil with rail `pⁿ↦qⁿ`, an internal rank-one return, and a genuine nonresonant
two-return zero at `(p,q,c)=(3,6,−1/9)`.

The subsequent amalgamated guard closes the missing legal-wait invariant. Its three modes
`(1,p⁻¹,p^(s−1))` retain a rank-two physical cut and rank-one zero return. Lean checks the
total `ℙ¹(ℚ)` action, forward-invariant p-adic trap, exact wait and carry-depth forcing,
ready-tail coordinates, complete inverse cylinder grammar, and the full equivalence

```text
physical mortality ↔ positive-return orbit reaches 1 ↔ TransGen LegalStep ρ 1.
```

The exact return series still needs three states. Concrete checked examples include the
denominator-cleared identity `B²AB²=0` and a ready nonterminal fixed point.

Lean now factors the deterministic orbit further. In the coordinate `x=z/(z−1)`, a nonterminal
non-pole step is a variable-length p-adic prefix decoder followed by one fixed
fractional-linear formula. Readiness is exactly unit membership of the decoded prefix, and the
reciprocal residual on each branch updates affinely.

The reciprocal center displacement gives the sharper global coordinate

```text
w=(ρ−α)/(z−α),              z=α+(ρ−α)/w.
```

Reset is `w=1`; the terminal residual is `−(ρ−α)/(α−1)`. Lean proves that each positive wait is
one exact rational p-adic sphere, that the spheres are pairwise disjoint, and that the displayed
Möbius inverse branch is a bijection between its sphere and the rational unit shell. Transport
through this coordinate yields the complete equivalence

```text
physical mortality
  ↔ terminal residual has a nonempty positive inverse address from 1.
```

Distinct positive branches have no common finite fixed point. The corpus also checks an exact
rational period-three survivor with wait itinerary `1,2,3`; its first two legs are equal-depth
resonances and its third is nonresonant descent.

The resonance analysis is exact. If the unit tail differs from `α/(ρ−α)` at depth `n`, then
`n<a` forces the next ready wait to be `n`, while `n>a` destroys readiness and poisons every
subsequent positive step. The exact center has no ready continuation. Every infinite ready
chain therefore resonates at depth `a` arbitrarily far along the chain. After a resonant output
factors as `p^(a+h)U`, the correct nested readiness depth is

```text
vₚ(U−1)=(s−1)(a+h).
```

The reported expression `(s−1)a+sh` was too large by `h`.

Finally, reduced rational ready-tail rails with affine wait update are excluded. An infinite
set of defined samples forces a polynomial identity; reducedness then gives
`P(λXᵈ)∣Q(X)`. Degree, constant-coefficient, and leading-coefficient comparisons force
`d=1` and `α=λ^(s+deg P)`, contradicting the unit valuation of `α` whenever
`vₚ(λ)≠0`. The intermediate degree theorem excludes `d>1` for every nonzero `λ`.

Clearing rational parameters gives an exact primitive integer-pair recurrence. Its
projectivization is proved equal to the decoded residual step. A generic determinant lemma then
confines every common reduction factor, and the guard specialization proves

```text
gcd reduction coprime to p divides DL(pᵃ−1).
```

For every prime `ℓ∣pᵃ−1`, the reduced pair either satisfies `m′≡n′ (mod ℓ)` or `ℓ` divides the
common cancellation factor. This is an exact reset-or-cancellation dichotomy, not yet a finite
decision sieve.

The converse normalization seam is now closed. Lean proves that canonical rational
numerator-denominator pairs are primitive, that the target unit condition forces the entire
`p^(sa)` scale into the raw common factor, and hence that every decoded rational step lifts to
one `PrimitiveIntegralStep`. Exact decoded paths lift without changing their length. A safe
exact-order quotient invariant therefore proves physical immortality directly; the
drift-divisor subgroup-avoidance family is nonvacuous even when the chosen terminal
coefficients are not themselves primitive.

These are structural and decidable-stratum theorems, not an `M₃(2)` resolution. The imported
order-four Skolem theorem used to classify rank-one profiles is not reimplemented in Lean. The
generic reverse edge compiler still assumes `αβ≠0`, and no universality or decision theorem is
known for rational inverse-address membership or its cyclotomic cancellation histories. Their
boundary is recorded in
[`audits/m32-rank-return-2026-07-28.md`](audits/m32-rank-return-2026-07-28.md) and scheduled in
[#11](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/11) and
[#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

## Audited But Unformalized

The internal-sandwich audit retains two unformalized exact obstructions:

| Record | Formalization obligation |
| --- | --- |
| [`MM-O09`](SALVAGE.md#mm-o09-two-state-ternary-prefix-image) | classification of full ternary trees with five leaves and the joint-image argument for exact two-state weighted decoders |
| [`MM-O10`](SALVAGE.md#mm-o10-additive-toggle-fusion-cycle) | idempotent normalization and the identities `F²=I−TP`, `F³=F`, and `rank F=rank F²=3` |

The full-algebra theorems concern their exact physical families only. They do not exclude
same-zero series or another decoder. The reconstruction and promotion boundaries are recorded in
[`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md)
and
[`audits/six-state-sandwich-saturation-2026-07-25.md`](audits/six-state-sandwich-saturation-2026-07-25.md).
`MM-O09` and `MM-O10` remain audited stock rather than publication dependencies; no live
formalization issue is assigned to them.

The setter-projective audit now also exposes a kernel-friendly carry theorem:

| Record | Formalization obligation |
| --- | --- |
| [`MM-S03`](SALVAGE.md#mm-s03-centered-setter-carry) | centered integer recurrence, reset representatives, nonresonant valuation-gap update, unit compatibility, two-transfer shape gate, and distinguished-boundary suffix gate |
| [`MM-S04`](SALVAGE.md#mm-s04-reverse-suffix-discrepancy) | reverse cancellation recurrence, exact common-suffix invariant, first-mismatch stopping theorem, and bounded-front-fringe inequalities |
| [`MM-S05`](SALVAGE.md#mm-s05-distinguished-boundary-beta-shell) | normalized boundary discrepancy, single-erasure pole classification, `D_b` strict-fraction bound, forbidden base-three carry pattern, and `D_c` exclusion |
| [`MM-S06`](SALVAGE.md#mm-s06-valuation-one-divisor-normal-form) | gcd reduction, divisor-ray parameterization, coprimality side conditions, and equivalence `Δ=H ↔ P=V` |
| [`MM-M04`](SALVAGE.md#mm-m04-swapped-digit-setter) | parametric nonzero-digit embedding, swapped basis, regular decoder, delimiter powers, mixed separator, and orientation-preserving projective transfer |
| [`MM-S07`](SALVAGE.md#mm-s07-swapped-digit-finite-slope-reduction) | strict sign of the centered coefficient, primitive-slope gcd reduction, effective bounds, rigidity `Δ=H ↔ P=V`, and the two swapped `β`-shell formulas |
| [`MM-S08`](SALVAGE.md#mm-s08-swapped-distinguished-boundary-beta-shell) | swapped carry classification, bounded upper-prefix normal form, and complete exclusion of both distinguished-boundary single-erasure poles |
| [`MM-S09`](SALVAGE.md#mm-s09-canonical-swapped-residue-cannot-hit-a-pole) | canonical discrepancy formula, pole-ratio equation, modulo-`ρ` suffix extraction, and final-erasure contradiction |
| [`MM-S10`](SALVAGE.md#mm-s10-swapped-target-suffix-sieve) | `β+2`-digit pole congruence, swapped lower-suffix grammar, and exclusion of `Δ=ρ−1` |

These records narrow the missing arbitrary-depth theorem but do not prove
projective avoidance. Their reconstruction is
[`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#centered-integer-carry);
the swapped construction is reconstructed in
[`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md);
promotion remains in
[#6](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

The dimension-two affine audit produced five independently checked records:

| Record | Formalization obligation |
| --- | --- |
| [`D2-S02`](SALVAGE.md#d2-s02-monotone-affine-path-form) | affine conjugacy, elementary case split, operational word normal form, and recovery of block lengths |
| [`D2-D05`](SALVAGE.md#d2-d05-prescribed-translation-count) | primitive linear-polynomial divisibility, bounded carries in both scan directions, ordered-marker automaton, regular control, and `a=±1` cases |
| [`D2-D06`](SALVAGE.md#d2-d06-private-prime-peeling) | unique-minimum valuation calculation, zero endpoints, fixed-count reduction, reversed language, and positive private valuation |
| [`D2-D07`](SALVAGE.md#d2-d07-bounded-valuation-orthants) | localization support, denominator bounds in both orthants, invariant-interval recognition, finite graph, and regular-control product |
| [`D2-M01`](SALVAGE.md#d2-m01-benchmark-critical-shell) | benchmark conjugacies, endpoint-shell translation, guarded `5`-adic transition, parity guard, and no-return-after-exit theorem |

The shell record does not decide the benchmark. Every fixed exit has a decidable suffix, but an
arbitrary critical prefix can produce infinitely many exits. A formal benchmark theorem must
represent that union effectively rather than hide it behind pointwise decidability. The audit is
[`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md);
formalization and the shell attack are tracked in
[#7](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/7).

The latest `M₅(3)` delimiter attack yielded four audited records:

| Record | Formalization obligation |
| --- | --- |
| [`MM-O06`](SALVAGE.md#mm-o06-pure-power-punctuation-obstruction) | common image and kernel of the lifted paired data, fixed-vector extraction, and contradiction with a contextual pure-power separator |
| [`MM-O07`](SALVAGE.md#mm-o07-setter-parameter-rigidity) | boundary alignment forces `r=t/μ`; verify the rejected benchmark coefficient |
| [`MM-M03`](SALVAGE.md#mm-m03-five-state-setter-punctuation) | explicit setter matrices, delimiter powers and ranks, regular decoder, and `S²A_cS³=λC̃L̃` |
| [`MM-S01`](SALVAGE.md#mm-s01-square-run-projective-normal-form) | invariant square-run plane, invertible `2 × 2` transfer, Möbius normalization, rank-one fracture grammar, and equivalence with pole avoidance |
| [`MM-S02`](SALVAGE.md#mm-s02-reset-zero-projective-peeling) | scaled transfer identity, exact two-shell classification of all poles, and reset-zero one-transfer avoidance |

The candidate proves only the halting-to-mortality direction. Its converse requires a theorem
that every nonterminal projective orbit avoids every pole. No such theorem is formalized or
assumed. The exact reconstruction and promotion boundary are recorded in
[`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md).
The first projective peeling theorem and the bounded residue diagnostics are in
[`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md).
Formal promotion and the avoidance decision are tracked in
[#6](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

The generic two-state compiler [`M4-C01`](SALVAGE.md#m4-c01-two-state-pushout-compiler), the
exact toggle-fusion obstruction [`M4-O01`](SALVAGE.md#m4-o01-exact-toggle-fusion-leaves-an-immortal-core),
the two-private-state phase obstruction
[`M4-O02`](SALVAGE.md#m4-o02-two-private-state-phase-signature), and the closed-serialization
obstruction [`M4-O03`](SALVAGE.md#m4-o03-closed-serialization-collapse) are now Lean
declarations. The phase theorem uses the exact Neary lower scales. The serialization theorem
is an exact initial-queue criterion: a finite closed-token substitution halts precisely when
none of the tokens reachable from that queue lies on a dependency cycle. The exact-code
obstruction [`M4-O04`](SALVAGE.md#m4-o04-exact-internal-final-code-defect) is formalized from
first principles: noninjectivity of a binary free-monoid morphism forces its two letter images
to commute, contradicting the two explicit Neary macro upper words.

The odd-phase macro cut [`M4-S01`](SALVAGE.md#m4-s01-odd-phase-macro-cut) remains reported.
Lean already defines the relevant phase residues and Table 2 tracks, but no theorem yet proves
the even-track invariant through every reachable queue or the induced macro solvability
equivalence. The direct first-return obstruction [`M4-O05`](SALVAGE.md#m4-o05-direct-two-state-first-return-recoding)
also remains reported. Neither claim enters the checked theorem ledger.

No `M₄(3)` undecidability theorem follows from the present corpus. The missing source is an
undecidable binary two-state controlled scalar system, or a matrix-level open-residue compiler
with a complete arbitrary-word converse.

## Modules

| File | Responsibility |
| --- | --- |
| `Computability.lean` | primitive-recursive closure lemmas used by the explicit compilers |
| `MatrixSemigroup.lean` | shared word semantics, mortality transports, common-image restriction, transposition, and zero padding |
| `LinearRepresentation.lean` | finite Hankel sections and exact-realization state lower bounds |
| `BoundaryTax.lean` | generic finite-witness two-channel boundary tax |
| `ReturnFamily.lean` | split finite-rank return normal form and matrix-valued block-Hankel witnesses |
| `EdgeCompression.lean` | exact adjacent-edge compression for split finite-rank families |
| `TwoPlaneEdges.lean` | compatible two-plane realization of a `2 × 2` edge square and exact rank-two certificates |
| `ReverseEdge.lean` | generic projective-incidence reverse compiler, basis adaptation, and all-path converse |
| `PolynomialPencil.lean` | coefficient support and exact evaluation of words over affine matrix pencils |
| `PrimitiveDivisor.lean` | cyclotomic prime support and Bang–Zsigmondy above exponent two |
| `ReturnSquare.lean` | exact rank-`(3,2)` laboratory, bridge normal form, and two-return square cage |
| `ReturnSquareDynamics.lean` | homogeneous projective trap and outer negative immortality wall |
| `ReturnSquarePrimePower.lean` | bridge-polynomial root support and finite quotient walls |
| `ReturnSquareClassification.lean` | complete prime-power ReturnSquare parameter classification |
| `ReturnSquareTax.lean` | exact four-state lower bound for literal reversible-stack returns |
| `ReturnSquareNoGo.lean` | quadratic-pencil reversible-squaring obstruction and blind-scaling collapse |
| `ReturnJordan.lean` | parity-Jordan rail rigidity and modular immortality certificate |
| `ReturnConvert.lean` | minimal two-scale return pencil and nonresonant multi-return zero |
| `ProjectiveLine.lean` | total affine-chart presentation of `ℙ¹` and exact unit-word ray action |
| `PadicValuation.lean` | nonzero rational p-adic shells and exact unequal-valuation calculus |
| `ReturnGuard.lean` | three-mode amalgamated return algebra, split mortality compiler, and exact state lower bound |
| `ReturnGuardDynamics.lean` | permanent trap, ready-tail grammar, and deterministic physical mortality equivalence |
| `ReturnGuardShift.lean` | shifted prefix decoder and affine reciprocal-residual transport |
| `ReturnGuardGauss.lean` | canonical residual coordinate, exact branch spheres, and guarded-step conjugacy |
| `ReturnGuardAddress.lean` | finite inverse-address mortality grammar and branch fixed-point incompatibility |
| `ReturnGuardArithmetic.lean` | primitive-pair recurrence and cyclotomic reset-or-cancellation sieve |
| `ReturnGuardTerminalGate.lean` | primitive cyclotomic radical and terminal-or-finite-reset gate |
| `ReturnGuardQuotient.lean` | exact-order finite projective automata, swallowed-factor semantics, and safe invariant certificates |
| `ReturnGuardIntegralLift.lean` | canonical rational pairs, decoded-to-integral execution lifting, and quotient certificates of physical immortality |
| `ReturnGuardQuotientCompleteness.lean` | zero-wait terminal kernel, cancellation-reachability completeness, and synchronized-product no-amplification |
| `ReturnGuardCancellationJet.lean` | primitive-cancellation blow-up, three projective exits, fixed-jet obstruction, and unbounded-depth integral witnesses |
| `ReturnGuardDriftCertificate.lean` | exact drift-divisor certificate classification, cyclic subgroup criterion, and executable finite test |
| `ReturnGuardCocycle.lean` | terminal-defect transport and the reduced second-order denominator recurrence |
| `ReturnGuardTangent.lean` | exact primitive-cancellation tangent cocycle, determinant support, recursive cyclotomic gate, and finite-field kernel line |
| `ReturnGuardLocalization.lean` | canonical fixed-support localization, localized cyclotomic invertibility, and the strict surviving novel-depth tower |
| `ReturnGuardTangentBudget.lean` | exact tangent product-content law and prescribed canonical cyclotomic cancellation |
| `ReturnGuardParameterLift.lean` | rank-one fixed-reset parameter perturbation and the unique visible incidence digit |
| `ReturnGuardSensitivity.lean` | total center derivative and exact p-adic sensitivity transport |
| `ReturnGuardAntiHensel.lean` | annular incidence compatibility determinant and complete one-digit obstruction |
| `ReturnGuardAntiHenselExamples.lean` | a full center congruence cylinder with a common two-step prefix and no third step |
| `ReturnGuardParameterPlane.lean` | exact center/reset perturbation plane, affine escape solver, shell discharge, and exterior sensitivity cocycle |
| `ReturnGuardParameterPlaneExamples.lean` | reset-only resurrection of a center cylinder killed by the one-parameter obstruction |
| `ReturnGuardParameterLattice.lean` | exact anisotropic sensitivity valuations and p-adic freezing of the projective parameter ray |
| `ReturnGuardParameterLatticeExamples.lean` | full center/reset congruence cylinder with the common legal wait prefix `1,3,1` |
| `ReturnGuardResonance.lean` | nonresonant descent, resonance localization, and corrected nested readiness |
| `ReturnGuardRail.lean` | polynomial divisibility and rational affine-wait rail obstruction |
| `ReturnGuardExamples.lean` | concrete mortal pair, nonterminal fixed point, and nested rational period-three orbit |
| `ReturnGuardTangentExamples.lean` | projective tangent three-cycle carried by the canonical rational survivor |
| `ReturnGuardParameterLiftExamples.lean` | five-step canonical novel-collision ladder |
| `ReturnGuardQuotientExamples.lean` | four-state modulo-eleven certificate excluding every primitive terminal execution of the period-three guard |
| `BinaryDefect.lean` | binary two-word defect theorem and exact Neary macro obstruction |
| `CHHNPacking.lean` | generic two-slot CHHN packing and six-state finite-Hankel kernels |
| `CHHNPackingRank.lean` | all-placement exact six-state lower bound for the Neary packing |
| `ClosedSubstitution.lean` | exact reachable-cycle criterion for finite closed-token queues |
| `FullMatrixAlgebra.lean` | generic full-algebra certificate from invertible physical contexts around a rank-one word |
| `PhaseSignature.lean` | two-private-state cyclic phase obstruction and Neary instantiation |
| `SideNormal.lean` | side-normal word-pair calculus, common upper plane, boundary coefficient, and terminal-match semantics |
| `ControllerPushout.lean` | arbitrary finite-controller pushout, total suffix decoder, and transposed prefix decoder |
| `TwoStatePushout.lean` | rule/erasure specialization, exact rank classification, and integer mortality compiler |
| `TwoStateObstructions.lean` | exact local toggle-fusion obstruction |
| `IndexedExecution.lean` | exact finite relational execution and closure views |
| `TagQueue.lean` | tag steps, indexed execution specializations, and generic history soundness |
| `NearyEncoding.lean` | four ordinary tiles, synchronization, source equivalence, and composed reductions |
| `MarkedTerminal.lean` | fresh marker, primitive terminality, and binary recoding |
| `TernaryEncoding.lean` | injective nonzero ternary representation |
| `PCPEncoding.lean` | `3 × 3` word-pair morphism and equality entry |
| `TerminalTile.lean` | arbitrary rank-one chains and fracture at every separator |
| `TerminalReduction.lean` | rational and integer fixed-boundary mortality compiler |
| `TerminalSource.lean` | generic primitive extraction and GPCP bridge |
| `PairedCompression.lean` | reset/toggle specialization, explicit coordinate certificates, and arbitrary-word decoding |
| `PairedMortality.lean` | common-column mortality converse and exact integer `4 × 4` family |
| `PairedRank.lean` | uniform exact rank-four certificate for the paired scalar series |
| `PairedBoundaryTax.lean` | exact six-state lower bound for diagonal paired-series bridges |
| `PairedBinary.lean` | total two-bit decoder and exact six-state scalar representation |
| `PairedBinaryContexts.lean` | closed paired-binary generator actions, physical context words, and source arithmetic |
| `PairedBinaryContextsClosed.lean` | explicit six-column and six-row physical context matrices |
| `PairedBinaryContextsNonsingular.lean` | modulo-nine pivot certificates and invertibility of both context matrices |
| `PairedBinaryFullAlgebra.lean` | canonical mortality alphabet and the full `M₆(ℚ)` physical-product span theorem |
| `ScheduledBinary.lean` | cyclic-controller specialization, source semantics, and malformed-word converse |
| `ScheduledBinaryRank.lean` | exact width-three rank-five certificate and universal exact-state lower bound |
| `WeightedTransducer.lean` | deterministic matrix transducers and the arbitrary-word block-row theorem |
| `PrefixMortality.lean` | complete prefix decoder, twelve-state realization, and ten-state common-image restriction |
| `PrefixContexts.lean` | closed ten-state generators, internal rank-one word, and physical contexts |
| `PrefixContextsClosed.lean` | Krylov-adapted reachable and observable context matrices |
| `PrefixContextsNonsingular.lean` | polynomial and congruence certificates for both context matrices |
| `PrefixFullAlgebra.lean` | full `M₁₀(ℚ)` product span and exact internal-sandwich lower bound |
| `LintAudit.lean` | package-wide default mathlib environment lint |
| `AxiomAudit.lean` | transitive axioms of publication-facing declarations |
| `Undecidability/UniversalMachine.lean` | verified two-tape interpreter for mathlib code halting |
| `Undecidability/FiniteTM0.lean` | finite-state restriction of supported `TM0` machines |
| `Undecidability/SeededTM2.lean` | exact rooting of `TM2` machines at an arbitrary source label |
| `Undecidability/UniversalTM0.lean` | fixed universal binary `TM0` machine and primitive-recursive input |
| `Undecidability/TM0ToRead.lean` | exact binary `TM0` normalization to read-state machines |
| `Undecidability/CockeMinsky.lean` | explicit deletion-width-two phase algebra and machine semantics |
| `Undecidability/CockeMinskyAvoidance.lean` | canonical exact halt-avoiding simulation, ordinary views, and reflection |
| `Undecidability/CyclicTag.lean` | two-tag semantics and the one-hot cyclic-tag simulation |
| `Undecidability/CyclicTagAvoidance.lean` | distinguished-phase avoidance and firing reflection |
| `Undecidability/TwoTagSource.lean` | verified finite two-tag sources and their Cook cyclic consequences |
| `Undecidability/Tracks.lean` | typed fixed-stride track serialization and recovery |
| `Undecidability/TagExecution.lean` | exact finite executions, sliced-track recovery, and congruence-head drainage |
| `Undecidability/NearyCompiler.lean` | exact Table 2 words, tracks, padding, and arithmetic envelope |
| `Undecidability/NearySimulation.lean` | traversal semantics of raw, bit, epsilon, and halting objects |
| `Undecidability/NearyData.lean` | garbage calculus, token invariant, and ordinary cyclic pulses |
| `Undecidability/NearyExecution.lean` | literal initialization, first-firing extraction, and the complete post-seed halting cascade |
| `Undecidability/NearySource.lean` | compositional Cook–Neary compiler into verified restricted-tag sources |
| `Undecidability/UniversalTwoTag.lean` | fixed universal finite two-tag system and primitive-recursive source queue |
| `Undecidability/UniversalNeary.lean` | complete computable reductions to binary `GPCP(4)`, `M₃(5)`, `M₄(4)`, `Z₆(2)`, and `M₁₀(2)` |
| `Undecidability/NearyProblems.lean` | canonical `Fin 4` and `Fin 5` target instances |
| `MacroIrreducibility.lean` | exact nonerasing Neary role-macro lower bound |
| `Undecidability/PairedProblems.lean` | canonical four-matrix target instance and structural promises |
| `Undecidability/BinaryProblems.lean` | canonical structured `Z₆(2)` instance |
| `Undecidability/PrefixProblems.lean` | canonical `M₁₀(2)` instance and all zero-padded dimensions |
| `Undecidability/Problems.lean` | encoded source and target decision predicates |

## Principal Declarations

| Claim | Lean declaration |
| --- | --- |
| History equation implies halting | `tagHaltsFrom_of_history` |
| Terminal equality forces deletion blocks | `tileHistory_of_terminal_match` |
| Four-tile equality iff tag halting | `terminal_match_iff_tagHaltsFrom` |
| Corrected five-pair PCP iff tag halting | `nearyPCP_solvable_iff_tagHaltsFrom` |
| Primitive solutions end in tile five | `nearyPCP_primitive_terminal` |
| Four-generator GPCP iff tag halting | `nearyGPCP_solvable_iff_tagHaltsFrom` |
| Nonempty-witness GPCP iff tag halting | `nearyGPCPPlus_solvable_iff_tagHaltsFrom` |
| Five integer matrices mortal iff tag halting | `nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom` |
| Arithmetic-envelope specialization | `NearyArithmeticEnvelope.mortality_iff_halts` |
| Four ordinary matrices are nonsingular and triangular | `nearyMortality_ordinary_det_ne_zero`, `nearyMortality_ordinary_upperTriangular` |
| Exceptional matrix is nonzero and rank one | `nearyMortality_terminal_ne_zero`, `nearyMortality_terminal_rank_eq_one` |
| Exact nonerasing Neary role macros require four letters | `ExactNearyMacroFactorization.four_le_card` |
| A nonsingular finite Hankel section lower-bounds every exact realization | `finiteHankel_card_le` |
| Exact diagonal two-channel bridges pay two additional states | `exactDiagonalTwoChannel_card_lower_bound` |
| A split finite-rank binary pair is mortal exactly when one return product vanishes | `ReturnFamily.pairGenerator_isMortal_iff` |
| Finite return block-Hankel sections factor through every exact ambient realization | `ReturnFamily.finiteReturnHankel_factor`, `ReturnFamily.returnHankel_card_le` |
| A split finite-rank family is mortal exactly when one constrained edge path vanishes | `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero` |
| Every compatible two-plane edge square is realized by two rank-two generators | `TwoPlaneEdges.output_mul_input`, `TwoPlaneEdges.generator_rank` |
| Generic projective incidence compiles to two rank-two `3 × 3` generators | `ReverseEdge.isMortal_adaptedGenerator_iff`, `ReverseEdge.adaptedGenerator_rank` |
| ReturnSquare physical mortality is exactly positive-return scalar bridge zero | `ReturnSquare.physical_isMortal_iff_positiveBridge` |
| Every nonresonant ReturnSquare zero uses at least three positive returns | `ReturnSquare.positiveBridge_zero_shape` |
| Nonnegative and outer-negative ReturnSquare parameters are immortal | `ReturnSquare.not_physical_isMortal_of_nonneg`, `ReturnSquare.not_physical_isMortal_of_beyond_negative_wall` |
| Bang–Zsigmondy holds above exponent two, except for `2⁶−1` | `exists_primitivePrimeDivisor` |
| Prime-power ReturnSquare is mortal exactly at one-return resonances | `ReturnSquare.physical_isMortal_primePower_iff` |
| Literal reversible-stack returns require at least four exact states | `ReturnSquareTax.reversibleStack_card_lower_bound` |
| Three singular quadratic modes cannot exchange `t` with `κt²` | `ReturnSquareNoGo.threeMode_swap_eq_zero` |
| Two exact squaring checks collapse to blind scaling | `ReturnSquareNoGo.verifiedPush_eq_blindScale` |
| The rank-compatible parity-Jordan branch is unique and immortal modulo seven | `ReturnJordan.normalForm_unique`, `ReturnJordan.not_isMortal_generator` |
| The two-scale return pencil is minimal and has a nonresonant two-return zero | `ReturnConvert.three_le_card_of_exact_realization`, `ReturnConvert.example_zero`, `ReturnConvert.example_nonresonant` |
| The amalgamated guard rejects every illegal wait permanently | `ReturnGuard.trap_forward`, `ReturnGuard.live_step_forces_ready` |
| Three-state physical mortality is exactly deterministic guarded reachability | `ReturnGuard.physical_isMortal_iff_guardedReachable` |
| Ready cylinders have unit tails and a complete inverse transition grammar | `ReturnGuard.readyState_ready`, `ReturnGuard.ready_transition` |
| Guard steps factor through a p-adic prefix decoder and affine reciprocal residual | `ReturnGuard.shift_step`, `ReturnGuard.ready_iff_prefixDecode_isUnit`, `ReturnGuard.reciprocalResidual_affine` |
| Physical mortality is finite inverse-address membership in disjoint residual spheres | `ReturnGuard.residualBranch_wait_unique`, `ReturnGuard.physical_isMortal_iff_inverseAddress` |
| Distinct positive residual branches have no common finite fixed point | `ReturnGuard.residualFixed_exclusive` |
| The primitive-pair recurrence projectivizes to the residual step exactly | `ReturnGuard.integralStep_realizes_residualStep` |
| Cyclotomic primes either reset the reduced pair or enter its common cancellation | `ReturnGuard.integralStep_cyclotomic_reset_or_cancel` |
| A cyclotomic factor is swallowed exactly when the source pair is terminal-congruent modulo it | `ReturnGuard.integralStep_cyclotomic_cancel_iff_terminalCongruent` |
| Outside the fixed parameter support, cancellation is exactly cyclotomic terminal congruence | `ReturnGuard.integralStep_novel_cancel_iff_cyclotomic_terminalCongruent` |
| Terminal defects obey an exact cocycle and reduced second-order denominator recurrence | `ReturnGuard.integralStep_terminalDefect`, `ReturnGuard.reducedDenominator_recurrence` |
| Every base-coprime cancellation depth is the minimum of the terminal-defect and displacement depths | `ReturnGuard.integralStep_cancel_iff_terminalDefect_and_displacement`, `ReturnGuard.integralStep_commonFactor_padicValInt` |
| Legal waits are logarithmic in primitive height and reduced height is uniformly Lipschitz | `ReturnGuard.integralStep_wait_le_log_height`, `ReturnGuard.integralStep_reduced_height_le` |
| A large primitive cyclotomic radical forces terminality or a surviving exact-order reset | `ReturnGuard.terminalDefect_zero_or_exists_primitive_reset`, `ReturnGuard.primitiveCyclotomicRadical_le_height_of_no_reset` |
| Exact-order quotient dynamics is periodic in the wait, and its annihilation state is exactly swallowed primitive reduction | `ReturnGuard.quotientTransfer_mod_of_primitive`, `ReturnGuard.quotientTransition_integralStep_eq_cancelled_iff` |
| A finite quotient invariant excluding annihilation and the target excludes every primitive integral execution | `ReturnGuard.no_primitiveExecution_of_quotientInvariant` |
| A primitive divisor of the drift gives a reset-automaton no-certificate whenever the center ratio avoids the base subgroup | `ReturnGuard.no_primitiveExecution_of_drift_divisor` |
| Every decoded rational execution canonically lifts step for step to primitive integral execution | `ReturnGuard.decodedStep_primitiveIntegralStep`, `ReturnGuard.decodedExecution_primitiveIntegral` |
| A safe exact-order quotient invariant certifies physical immortality | `ReturnGuard.not_physical_isMortal_of_quotientInvariant` |
| A drift-divisor subgroup-avoidance certificate is physically sound without coefficient-coprimality assumptions | `ReturnGuard.not_physical_isMortal_of_drift_divisor` |
| The zero-residue transfer annihilates every primitive terminal pair | `ReturnGuard.quotientTransition_zero_terminal_eq_cancelled`, `ReturnGuard.terminal_mem_forces_cancelled` |
| Safe quotient certificate existence is exactly cancellation unreachability from reset, which directly certifies physical immortality | `ReturnGuard.hasQuotientCertificate_iff_cancelled_unreachable`, `ReturnGuard.not_physical_isMortal_of_cancelled_unreachable` |
| Terminal exclusion is redundant in physical finite-quotient certificates | `ReturnGuard.not_physical_isMortal_of_cancellationFreeQuotient` |
| Every cancellation-free synchronized two-prime invariant projects to both single-factor certificates | `ReturnGuard.hasSynchronizedCancellationFreeInvariant_imp_components`, `ReturnGuard.hasSynchronizedCancellationFreeInvariant_imp_quotientCertificates` |
| Removing a swallowed prime power has exactly two rigid exits and one equal-depth tangent exit | `ReturnGuard.cancellationJet_terminalDepth_lt_ofPair`, `ReturnGuard.cancellationJet_displacementDepth_lt_ofPair`, `ReturnGuard.cancellationJet_depth_eq_mod`, `ReturnGuard.integralStep_cancellationExit` |
| The equal-depth exceptional divisor covers the full projective line and no fixed congruence jet determines all exits | `ReturnGuard.localCancellationExit_surjective`, `ReturnGuard.cancellationExit_escapes_fixed_truncation` |
| Every exact cyclotomic prime-power factor is realizable as primitive integral cancellation, and one fixed recurrence realizes every positive 3-adic depth | `ReturnGuard.primitive_integralStep_of_exact_cyclotomicDepth`, `ReturnGuard.exists_primitive_integralStep_with_three_cancellationDepth` |
| A tangent trajectory removes exactly the product of its leg scalars, which equals the final image content at a primitive endpoint | `ReturnGuard.ScaledTrajectory.chronologicalProduct_mulVec`, `ReturnGuard.ScaledTrajectory.image_gcd` |
| A canonical reset can swallow a prescribed divisor of one cyclotomic factor as its complete primitive reduction | `ReturnGuard.prescribedReset_primitiveIntegralStep`, `ReturnGuard.prescribedReset_factor_isCoprime_fixedSupport` |
| One fixed canonical reset orbit has four consecutive legal cyclotomic cancellations | `ReturnGuard.Examples.cyclotomicLadder_decodedSteps`, `ReturnGuard.Examples.cyclotomicLadder_primitiveSteps`, `ReturnGuard.Examples.cyclotomicLadder_novelFactors` |
| Fixed-reset center perturbation moves each residual exit on one rank-one affine line, with one unique digit meeting any visible kernel | `ReturnGuard.integralResidualTransfer_centerDrift_factor`, `ReturnGuard.existsUnique_centerDriftDigit` |
| One fixed canonical reset orbit has five consecutive legal novel cyclotomic cancellations | `ReturnGuard.Examples.fiveCollision_decodedSteps`, `ReturnGuard.Examples.fiveCollision_primitiveSteps`, `ReturnGuard.Examples.fiveCollision_novelFactors` |
| Negative center sensitivity transports through one legal step by subtracting the depth-scaled wait | `ReturnGuard.readyLegalValue_hasDerivAt`, `ReturnGuard.parameterSensitivityStep_hasValue` |
| A visible affine incidence digit preserves an old annular coefficient exactly when their cross-determinant is nonzero | `ReturnGuard.exists_incidenceDigit_and_preserves_iff`, `ReturnGuard.no_incidenceDigit_preserves_of_liftCompatibility_eq_zero` |
| One full integral center cylinder shares legal waits `1,3` and admits no third decoded step | `ReturnGuard.Examples.deadLift_twoStepPrefix`, `ReturnGuard.Examples.deadLift_noThirdStep` |
| At a primitive drift divisor, a safe quotient certificate exists exactly when the center avoids the scaled base-power orbit | `ReturnGuard.hasQuotientCertificate_iff_centerPowerOrbit_avoids` |
| For nonzero center and scale, the excluded orbit is exactly the cyclic subgroup generated by the base | `ReturnGuard.mem_centerPowerOrbit_iff_centerRatio_mem_zpowers` |
| The forbidden orbit has `period` elements and exactly `factor-period` center residues certify immortality | `ReturnGuard.card_centerPowerOrbit`, `ReturnGuard.card_certifyingCenters` |
| The Boolean drift-divisor classifier decides certificate existence and emits a physical immortality theorem | `ReturnGuard.hasQuotientCertificate_iff_driftDivisorCertifies`, `ReturnGuard.not_physical_isMortal_of_driftDivisorCertifies` |
| Every nonresonant continuation descends and every infinite ready chain resonates arbitrarily late | `ReturnGuard.nonresonant_nextWait_lt`, `ReturnGuard.infinite_ready_chain_resonates` |
| Resonant nesting has normalized depth `(s−1)(a+h)` | `ReturnGuard.resonance_ready_iff` |
| No reduced rational chart realizes a nontrivial affine wait rail at infinitely many prime powers | `ReturnGuard.Rail.no_infinite_primePower_affineWait_rail` |
| The guarded return series intrinsically needs three states | `ReturnGuard.parameters_three_le_card_of_exact_realization` |
| Rational resonant survivors can have exact period three | `ReturnGuard.Examples.cycle_decoded_orbit`, `ReturnGuard.Examples.cycle_first_two_resonant` |
| The checked period-three survivor is a genuine immortal physical matrix pair | `ReturnGuard.Examples.cycle_not_physical_isMortal` |
| Every normalization factor in the checked period-three survivor lies in the fixed parameter support | `ReturnGuard.Examples.cycle_commonFactors_dvd_fixedSupport` |
| A four-ray invariant modulo eleven excludes every primitive integral terminal execution of the period-three guard | `ReturnGuard.Examples.cycle_no_primitive_integral_terminal_execution` |
| The executable drift-divisor classifier accepts the modulo-eleven period-three parameters | `ReturnGuard.Examples.cycle_driftDivisorCertifies` |
| The same modulo-eleven certificate proves physical immortality through canonical integral lifting | `ReturnGuard.Examples.cycle_not_physical_isMortal_by_quotient` |
| Rule and erasure matrices agree on the upper-side plane | `rule_erase_agree_on_upperSide` |
| Every finite-controller letter routes its selected private channel exactly | `controllerMatrix_mulVec_controllerVector` |
| Every suffix-controlled word obeys the generic total decoder | `controllerProduct_mulVec_controllerVector` |
| Transposition gives the generic prefix-controlled decoder | `controllerVector_vecMul_transposeProduct` |
| The paired generators have their displayed coordinate normal forms | `pairedDataMatrix_eq_explicit`, `pairedToggleMatrix_eq_explicit` |
| Every compressed word realizes its decoded four-role word | `pairedProduct_mulVec_column`, `pairedCoefficient_eq_sideCoefficient` |
| Every four-role word has a compressed encoding | `decodePairedWord_surjective` |
| Three-matrix scalar zero iff the terminal equation | `paired_zero_iff_terminal_match` |
| Four integer matrices mortal iff the terminal equation | `pairedMortalityFamily_int_mortal_iff_terminal_match` |
| Canonical `M₄(4)` instance mortal iff tag halting | `nearyMortality44_mortal_iff_tagHaltsFrom` |
| Three control matrices have common first column | `nearyMortality44_control_fixes_anchor` |
| Toggle control is a permutation matrix | `nearyMortality44_toggle_eq_permMatrix` |
| Fourth matrix is nonzero and rank one | `nearyMortality44_separator_ne_zero`, `nearyMortality44_separator_rank_eq_one` |
| Paired scalar series has a nonsingular `4 × 4` Hankel section | `pairedRankHankel_det_ne_zero` |
| Every exact paired-series realization needs four states | `paired_exact_state_lower_bound`, `paired_native_state_card`, `paired_native_represents` |
| Every exact diagonal paired-series bridge needs six states | `paired_exact_diagonal_twoChannel_state_lower_bound` |
| Every literal Neary CHHN placement needs six exact states | `chhnNeary_exactRepresentation_six_le_card` |
| Every two-state pushout word obeys its suffix decoder | `twoStateProduct_mulVec_phaseVector`, `twoStateCoefficient_eq_controlled` |
| A two-state reset has rank three; separated destinations have rank four | `twoStateDataMatrix_rank_eq_three_of_eq`, `twoStateDataMatrix_rank_eq_four_of_ne` |
| The integer two-state family is mortal exactly at a nonempty controlled scalar zero | `twoStateMortalityFamily_int_mortal_iff_nonempty_zero` |
| Exact left-context toggle fusion is immortal | `exactLeftToggleFusion_immortal` |
| A finite closed-token queue halts iff no reachable token lies on a dependency cycle | `closedSubstitutionHalts_iff_noReachableCycle` |
| Two private quotient states cannot isolate the Neary rule phase | `twoPrivateState_ruleScale_eq`, `neary_twoPrivateState_phaseCompiler_impossible` |
| A noninjective binary morphism cannot realize both Neary macro upper words | `binarySpell_not_injective_commute`, `neary_exact_internal_final_code_impossible` |
| Every binary word has the exact six-state coefficient | `pairedBinaryRow_wordProduct`, `pairedBinaryCoefficient_eq_sideCoefficient` |
| Every four-role word has a two-bit encoding | `decodePairedBinary_surjective` |
| Canonical paired-binary mortality products span `M₆(ℚ)` | `pairedBinaryMortality_wordProductSpan_eq_top` |
| Canonical structured `Z₆(2)` instance iff tag halting | `nearyScalarZero62_hasZero_iff_tagHaltsFrom` |
| Free-monoid `Z₆(2)` instance iff tag halting | `nearyScalarZero62_hasZeroStar_iff_tagHaltsFrom` |
| Both `Z₆(2)` generators fix `e₁` | `nearyScalarZero62_fixes_anchor` |
| Every scheduled binary word has the decoded source coefficient | `scheduledRow_wordProduct`, `scheduledCoefficient_eq_sideCoefficient` |
| Every tile history has a scheduled binary encoding | `decodeScheduled_historyCode` |
| A scheduled zero has no incomplete clock cycle | `decodeScheduled_is_tileHistory_of_coefficient_zero`, `scheduledCoefficient_zero_length_dvd` |
| Scheduled scalar zero iff the terminal equation and tag halting | `scheduledBinary_zero_iff_terminal_match`, `scheduledBinary_zero_iff_tagHaltsFrom` |
| Width-three scheduled series has a nonsingular `5 × 5` Hankel minor | `scheduledWidthThreeHankel_det_ne_zero` |
| Every exact width-three rational realization needs five states | `scheduledWidthThree_exact_state_lower_bound`, `scheduledWidthThree_native_state_card`, `scheduledWidthThree_native_represents` |
| Every binary prefix-machine word has one decoded block per row | `prefixMachine_run`, `WeightedTransducer.wordProduct_apply` |
| Prefix-machine mortality iff five-matrix mortality | `prefixMachine_mortal_iff_normalized` |
| Both prefix generators share the ten-dimensional image | `prefixProjection_generator` |
| Ten-state mortality iff prefix-machine mortality | `restrictedPrefixGenerator_mortal_iff_prefixMachine` |
| Canonical `M₁₀(2)` instance mortal iff tag halting | `nearyMortality102_mortal_iff_tagHaltsFrom` |
| Every zero-padded `M₁₀₊ₙ(2)` instance iff tag halting | `nearyMortality10Plus_mortal_iff_tagHaltsFrom` |
| Mathlib code halting has a verified `TM2` interpreter | `exists_universalTM2` |
| Fixed two-tag halt-label reachability iff code halting | `UniversalTwoTag.reaches_halt_iff` |
| Emitted restricted-tag halting iff code halting | `UniversalNeary.tagHaltsFrom_iff_codeHalts` |
| Code halting many-one reduces to binary `GPCP(4)` | `UniversalNeary.codeHalts_reduces_gpcp4` |
| Binary `GPCP(4)` solvability is not computable | `UniversalNeary.gpcp4_not_computable` |
| Code halting many-one reduces to `M₃(5)` | `UniversalNeary.codeHalts_reduces_mortality35` |
| `M₃(5)` mortality is not computable | `UniversalNeary.mortality35_not_computable` |
| Code halting many-one reduces to `M₄(4)` | `UniversalNeary.codeHalts_reduces_mortality44` |
| `M₄(4)` mortality is not computable | `UniversalNeary.mortality44_not_computable` |
| Code halting many-one reduces to `Z₆(2)` | `UniversalNeary.codeHalts_reduces_scalarZero62` |
| `Z₆(2)` scalar zero is not computable | `UniversalNeary.scalarZero62_not_computable` |
| Code halting many-one reduces to `M₁₀(2)` | `UniversalNeary.codeHalts_reduces_mortality102` |
| `M₁₀(2)` mortality is not computable | `UniversalNeary.mortality102_not_computable` |
| Two-tag executions reach their cyclic firing phase | `CyclicTag.reaches_firing_phase` |
| A woven compiler word emits its prescribed track | `read_wholeAppendant_track` |
| One arbitrary ordinary cyclic pulse has a nonempty physical simulation | `read_next_dataBit_transGen` |
| Literal Neary initialization reaches the token invariant | `read_initialQueue` |
| Every nonfiring cyclic execution is simulated | `read_avoidingReaches` |
| A run reaching the distinguished pulse reaches its first such pulse | `read_until_firing` |
| The distinguished pulse appends the halting seed | `read_to_haltingSeed` |
| Exact-empty firing leaves only junk before the seed | `read_exact_firing_to_haltingSeed` |
| Exact-empty cyclic firing forces restricted-tag halting | `read_exact_firing_halts` |
| A two-atom garbage reserve cannot halt | `GarbageBoundary.not_tagHaltsFrom` |
| Restricted-tag halting reflects a reachable distinguished cyclic firing | `compiled_halts_implies_firing` |

## Logical Foundation

Lean checks proof terms in dependent type theory with inductive and quotient types and an
impredicative, proof-irrelevant `Prop`. Mathlib supplies proved definitions and lemmas; it is not
a second proof engine. Tactics such as `simp` and `omega` produce terms that Lean's kernel checks.

For every publication-facing theorem, `#print axioms` reports only:

```text
propext
Classical.choice
Quot.sound
```

These provide propositional extensionality, ordinary classical choice, and quotient soundness.
The project declares no axiom and uses no `sorry`, `admit`, `unsafe`, `partial`, `native_decide`,
external declaration, or unverified proof certificate.

The operational trusted computing base comprises the Lean kernel implementation, executable,
runtime, operating system, hardware, and the correctness of the formal specification. Parsers,
elaborators, tactics, and mathlib lie outside the logical trusted core because the kernel checks
their resulting terms.

## External Boundary

There is no unformalized theorem boundary in the binary `GPCP(4)`, `M₃(5)`, `M₄(4)`, `Z₆(2)`,
or `M₁₀(2)` undecidability proofs. Neary's Table 2 and Cocke–Minsky's tag construction are
historical sources for locally defined compilers, not imported premises. Mathlib's
kernel-checked noncomputability theorem for `Nat.Partrec.Code` supplies the source predicate.

CHHN's generator–dimension and scalar-to-corner frontier transports remain external paper
theorems. Bibliographic priority claims likewise depend on the recorded literature audits rather
than Lean.

The scheduled compiler introduces a separate source-width seam. Neary's published construction
sets `β = 10p`, where `p` is the simulated cyclic-tag program period. The fixed-width audit found
no universality theorem for the required binary deletion-width-three family. Cocke and Minsky
fix deletion width two only by allowing the alphabet to grow; the adjacent binary width-three
class remains unresolved in the located literature. The width-three Lean theorem is therefore
a conditional five-state reduction and an exact-rank result, not an established undecidable
cell.

## Prior Formalizations

The public Lean corpus was audited on 2026-07-22 for an executable reduction chain. A usable
component had to provide a computable translation,
the required halting equivalence, a compatible license, and no admitted simulation theorem.
Name-level overlap was not enough.

| Development | Audited revision | Result | Reuse decision |
| --- | --- | --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/809c3fb3b5c8f5d7dace56e200b426187516535a/Mathlib/Computability) | `809c3fb3` (`v4.12.0`) | Proves noncomputability of code halting and interprets partial-recursive code by Turing machines | Adopt the code-halting theorem and verified TM compilers; reify the finitely supported result as one fixed finite machine locally. |
| [Wolfram TuringMachine](https://github.com/WolframInstitute/TuringMachine/tree/ff67008a07d37dee380567d5eeb556ed127759e7/Proofs/TagSystem) | `ff67008a` | Proves the one-hot two-tag to cyclic-tag step simulation | Use as an independent specification only. The repository has no stated license; its Turing-machine to two-tag simulation is an explicit hypothesis. |
| [UniversalityDB](https://github.com/WolframInstitute/UniversalityDB/tree/d4383c47b5db3a3673a7d88472409eb1bd912ff0) | `d4383c47` | Catalogues the Wolfram universality chain | Not adopted: the catalogue records the same missing Turing-machine to two-tag theorem. |
| [DiagonaLean](https://github.com/DiagonaLean/DiagonaLean/tree/28ed8223dcfb389c8c1b655521099500b7bc53af) | `28ed8223` | Formalizes substantial HALT, MPCP, PCP, and matrix-mortality semantics | Not adopted. Its `ManyOneReduces` permits an arbitrary function, `SDecidable` permits an arbitrary Boolean characteristic function, and the HALT-to-MPCP tile compiler is declared `noncomputable`; these statements do not supply the executable many-one reduction required here. The general compiler also retains machine-normalization side conditions. |
| [cslib](https://github.com/leanprover/cslib/tree/0268c49a549b093bf865fc6c66c96ae5412494fe/Cslib/Computability) | `0268c49a` | Supplies finite-state Turing-machine and unlimited-register-machine semantics | Potential semantic library only. No universality or halting-noncomputability bridge was present at the audited revision. |
| [Jacob Weightman's tag-system branch](https://github.com/jacobdweightman/mathlib4/tree/ec3a5db58c8d2f7222116101980787788a5bfc36/Mathlib/Computability) | `ec3a5db5` | Develops tag-system semantics and elementary dynamics | Not adopted: it has no universality compiler and contains admitted declarations. |
| [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability/tree/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c) | `c7257b73` | Gives certified generic reductions through binary PCP | Proof blueprint only. It is Coq rather than Lean and its generic PCP instances do not preserve the four-generator bound. |
| [rule110-lean](https://github.com/novaspivack/rule110-lean/tree/cbbc170e48f254fcd822d10e759eecb4e359a943) | `cbbc170e` | Formalizes portions of Cook's Rule 110 simulation | Not adopted: its published status leaves the central simulation bridges as hypotheses and uses native evaluation certificates. |
| [dna-tiles](https://github.com/CharlesCNorton/dna-tiles/tree/0410cdf30e11da33678d9e1ae94c94cffbcc22ef) | `0410cdf3` | Defines Turing machines and cyclic tag systems in Rocq | Not adopted. Its claimed cyclic-tag completeness selects a trivially halting or looping system by classical excluded middle after asking whether the source machine halts. This proves an extensional existence statement, not a computable compiler. |

No audited public artifact supplied both specialized edges: an executable universal
source-to-two-tag compiler and Neary's cyclic-tag-to-restricted-binary-tag Table 2 compiler.
This project therefore retains mathlib's code-halting theorem and formalizes those translations
locally. This is a search result, not a claim that no unpublished or unindexed development exists.

## Mechanical Verification

```sh
./scripts/check.sh
```

The build treats warnings as errors, disables automatic implicit variables, enables mathlib's
strict syntax profile, runs every default environment linter, compares
`verification/axioms.txt` byte-for-byte, rejects proof escapes and strictness relaxations, runs
the typed finite falsifier, validates the HTML, checks reference-PDF identities, and reproduces
the manuscript PDF. The finite search independently checks bounded source words, compressed
coefficients, decoder coverage, and arbitrary four-matrix products. It is a transcription-error
detector, not part of the proof.

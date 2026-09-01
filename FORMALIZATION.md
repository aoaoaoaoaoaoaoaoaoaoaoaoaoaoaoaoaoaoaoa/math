# Formal Verification

## Frankl abundance theorem

Lean proves the following unconditional finite theorem at

```text
38234553336670271/100000000000000000
  = 0.38234553336670271
  > (3−√5)/2.
```

For every finite union-closed family of distinct Boolean vectors that is nonempty and not
`{∅}`, some coordinate occurs in strictly more than this fraction of its members. The
publication-facing declaration is `Frankl.unionClosed_exists_abundant_coordinate` in
`Frankl/AffineEntropyBridge.lean`. Its affine parameters are

```text
α=356069804374481/10000000000000000,    ε=10⁻¹⁸.
```

The proof is kernel-checked from the finite family to the scalar certificate. Its main layers are:

- finite Shannon entropy, conditioning, deterministic pushforwards, product laws, and the chain
  rule, including zero-probability fibers;
- independent and recursively dependent symmetric couplings with the prescribed marginals;
- the exact entropy bridge: Yu's strict one-coordinate affine inequality sums to an entropy gain
  for a union that remains supported on the original finite union-closed family;
- exact-mean lifting, fixed-mean concavity, one-moment support reduction, half-support
  elimination, orbit classification, and contraction to canonical objective families;
- analytic collapse of the diagonal family;
- a support-aware endpoint contraction on
  `1/4≤a≤38234553336670271/10^17, 0≤q≤1/2`, using support `max(a,q)` and conditional center

  ```text
  r=(a(1−2t)+tq)/(1+q−a−t);
  ```
- exact positivity of the saturated centered curve on `1−t≤y≤21/25`. Its third-derivative
  polynomial is monotone; this makes the second derivative unimodal, so rational logarithm
  enclosures at the two endpoints prove convexity on the whole interval. A 72-term rational
  enclosure at `y=670545261496963/10^15` supplies the strict supporting line;
- analytic domination of the `q=1` endpoint by `q=a`, which preserves the marginal law and
  independent entropy while decreasing the dependent entropy term;
- kernel replay of generated static certificates only on the low endpoint rectangle
  `0≤a≤1/4, 0≤q≤1/2`. The former residual high-`a` subdivision and `q=1` trace are gone.

The generated trace is ordinary proof data: every leaf contains a closed rational subdivision
term and a definitional equality that the proved checker accepts it. The Python/Arb program is
retained as an independent outward-rounded oracle, not as a Lean premise. No theorem uses
`native_decide`, an external declaration, a generated axiom, or another proof aperture.

An independently audited centered-endpoint factorization places the affine two-coupling wall in

```text
(0.38234553336670272114599300,
 0.38234553336670272114599301).
```

Thus the checked target is less than `1.2×10⁻¹⁷` below the analytic obstruction. This exact real
wall is not formalized and is not a premise of the rational theorem; its finite Arb enclosure and
written algebra are recorded in `audits/frankl-affine-wall-2026-08-10.md`.

The principal files are `Frankl/EndpointBoundary.lean`, `Frankl/SupportEndpoint.lean`,
`Frankl/CenteredEndpoint.lean`, `Frankl/FiniteEntropy.lean`,
`Frankl/ConditionalEntropy.lean`, `Frankl/FiniteCoupling.lean`, and
`Frankl/AffineEntropyBridge.lean`. The target remains compartmentalized: `lake build Frankl`
builds the Frankl library without building `MatrixMortality`; the repository-wide
`scripts/check.sh` intentionally runs both publication gates.

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

The exact Neary role pairs admit no rolewise macro factorization through an alphabet of
cardinality below four. The original theorem permits arbitrary unequal macro lengths and
noninjective role codes but assumes nonerasing target morphisms. A second paired-Parikh theorem
removes nonerasure entirely: empty or coincident macro words and nonunique decoding still factor a
nonsingular four-channel map through the physical alphabet, forcing at least four letters.
State-dependent spelling, nonfactorial overlap, an open residual, target recoding, and
solvability-only transformations remain outside the formal theorem.

For the `4 × 4` compiler, Lean checks the side-separating change of basis, agreement of each
rule/erasure pair on the complete upper-word plane, and the explicit four-dimensional paired-role
representation. A right-to-left transducer decodes every arbitrary control word, and a constructive
surjectivity theorem encodes every four-role word. The three control matrices have common first
column `e₁`, and the toggle is an explicit permutation matrix. Adding the nonzero rank-one matrix
`CL` gives four integer matrices. The unconditional outer-separator theorem proves the mortality
converse for every number and placement of separators, arbitrary singular controls, and zero
control-only or exterior blocks. The two data controls are singular; the toggle is an invertible
permutation matrix.

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

The paired phase-fracture core is also checked. Lean derives the four local rule/erase matrices,
their affine chart actions, both discrepancy shears, their nontrivial private scaling and mixing,
and the two exact commutators. A two-dimensional pencil of affine forms invariant under the
constant and radial commutators must forget the accumulator. This checks the algebraic rigidity
step in the linear-fractional line-image branch once equivariance supplies pencil invariance.
Independently of dimension, a same-zero realization whose erase-phase suffix target column after
`c`-prefixing is a scalar multiple of its prior column cannot coexist with a paired zero: a toggle
normalizes the phase without changing the coefficient, while the erase-`c` prefix forces distinct
first binary symbols and hence a nonzero source coefficient.

This does not make the full rational phase-fracture theorem Lean-checked. Zariski density of the
reachable phase orbit, extension to rational-map identities, the fixed field of private scaling,
and arbitrary-rational two-translation rigidity remain independently audited. The precise seam
is recorded in
[`m34-rational-phase-fracture-2026-08-06.md`](audits/m34-rational-phase-fracture-2026-08-06.md).

The history-sensitive escape is now checked on the exact boundary where it is valid. Lean first
refutes terminal-word uniqueness in general: at width three and body `bcbb`, two explicit,
distinct role words satisfy the complete terminal equation. The longer word appends a null
history after the deterministic execution has already halted. For every minimum-length body
`body.length=β−1`, a length deficit excludes any such extension, so the sole terminal word is
`R_c :: body.map erase`.

An injective nonzero-digit base-five code of role words then yields three explicit integral
control matrices. On every arbitrary control word their reachable column is exactly the decoded
role code, suffix-phase sign, and homogeneous unit. The resulting coefficient has precisely the
zeros of the paired compiler on every minimum-length body. An outer-product separator and the
unconditional separator theorem give four `3 × 3` integral matrices with a complete mortality
converse; the former rational rescaling and fixed-anchor proof have been deleted. Lean checks the
concrete instance `β=3`, body `bb`, code `92`, and control witness `ctbbt`. The data matrices are
singular, yet their semantic state retains an injective code of every decoded positive history;
singularity alone therefore supplies no positive collision. This does not prove `M₃(4)`: selecting
a terminal code is nonuniform on unrestricted source instances. The independently audited
full-product phase graph is recorded in
[`m34-history-fracture-2026-08-06.md`](audits/m34-history-fracture-2026-08-06.md).
The unconditional separator reconstruction and the exact surviving `M₃(4)` obstruction are
recorded in
[`m34-unconditional-separator-2026-08-07.md`](audits/m34-unconditional-separator-2026-08-07.md).

The nonminimum body `bcbb` is now closed exactly. Lean proves that its null histories are
precisely `(bbb,cbb)^k` and its complete terminal role language is `P₀Q*`. A second singular
three-state decoder maintains the most-significant-digit-first role code, suffix-phase sign times
`5^length`, and unsigned `5^length` on every control word. For

```text
κ=5443/15624,       α=5417371/9765000,
```

the affine row vanishes exactly on `P₀Q*`. The converse proves coprimality modulo `5⁶−1`, forces
the decoded length modulo six, rejects the empty word, and then invokes injectivity of the
base-five code. `bcbb_periodicCoefficient_zero_iff_paired_zero` identifies these zeros with the
paired coefficient on the complete control free monoid. Clearing the rank-one separator gives
four explicit integral `3 × 3` matrices, and
`bcbbIntegralFamily_mortal_iff_paired_zero` proves their arbitrary-product converse.

The adjacent body `bcbc` certifies the first branching wall. Lean checks two distinct
four-stroke null blocks of equal length and injectively concatenates them according to arbitrary
bit words. It now also proves the complete null grammar `(X(DZ)*F)*` and terminal grammar
`FD(X(DZ)*F)*` from a canonical residual path. The critical invariant is that every reachable
nonempty right residual is exactly `b`; the proof classifies entrances to the three live
residuals rather than using a false forward recursion.

The reported singular rational matrices are formalized through their complete raw-control state
recurrence. Lean proves both data determinants vanish, the toggle determinant is `−1`, canonical
stroke controls decode to the exact terminal histories, and every such control is a matrix zero.
The finite reverse-carry converse on malformed controls remains audited rather than kernel-checked.
Its reverse graph, descending dead-state certificate, and bounded cross-check are recorded in
[`m34-bcbc-singular-recognizer-2026-08-08.md`](audits/m34-bcbc-singular-recognizer-2026-08-08.md).
Accordingly, `zdim_ℚ(L₃,bcbc)≤3` is an audited fixed-instance result, not a theorem in this file.
The construction has source-fitted constants and does not weaken the uniform obstruction in
`G3-O04`.

A separate direct-mortality route now has a complete punctuation grammar. For arbitrary ordinary
matrices and any distinguished `S` satisfying `S²=uvᵀ`, Lean proves that the physical family is
mortal exactly when `vᵀH_zu=0` for some word `z` with no adjacent `S`. The proof recursively cuts
at an arbitrary punctuation square; it does not assume rank, invertibility, normalized boundary
vectors, or intended placement. For the side-normal Neary boundary, Lean checks the explicit
source-uniform rational matrix

```text
S=[[1,0,0], [−1/μ,0,0], [T/μ+1,μ,0]]
```

has square `(γ/μ)λ`, rank exactly two, and determinant zero. A `3×3` inserted Hankel section on
the contexts `ε,D_c,D_b` further proves that exact coefficient preservation on the complete
`R_bR_b`-free subshift forces the proposed `R_b` matrix to be invertible. This remains true after
arbitrary nonzero per-letter rescaling. The surviving obligation is precisely a word-dependent
same-zero representation on that subshift; see
[`m34-square-root-punctuation-2026-08-08.md`](audits/m34-square-root-punctuation-2026-08-08.md).

The first scalar-carry response to that branching is also closed. Lean checks a terminal control
and a same-length nonterminal near-fork, then proves a dimension-independent local collision law:
if `BBv=CBTγ` and `DZv=FXv` for the four stroke products, both controls reach the same state.
No same-zero representation can satisfy those identities. For the proposed rational phase-line
family, Lean strengthens the projective calculation to equality of the two full `3 × 3` control
products for every parameter `ρ≠−1`; no row or column repairs the false zero. Arbitrary singular
three-state dynamics need not satisfy the local identities and remain open. See
[`m34-near-fork-carry-collision-2026-08-07.md`](audits/m34-near-fork-carry-collision-2026-08-07.md).

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
constrained-path grammar, and both mortality implications. Lean now also transports the unique
hard compatible one-loop edge stratum back to that compiler with intrinsic `β=1`; the audited
remaining edge-rank census gives `Mort₃^(2,2) ≡ₘ GPI₂`. `ProjectiveIncidence` now proves the
exact two-ray exceptional locus and rescales every generic instance to `α=β=1` while preserving
all word zeros. It also proves that the relative projectivity permutes every two-point common
bad set, forcing both labelled transitions to exit together. The positive first-exit audit then
reduces arbitrary PI₂ to at most two GPI₂ queries. The surviving enemy is GPI₂ itself, not
genericization or the edge graph.

`ProjectiveCollatz` now checks an exact fixed-projectivity arithmetic benchmark inside that
enemy. The inverse maps `A(z)=2z` and `B(z)=(2z−1)/3` generate an integer `n` from `1` exactly
when shortcut Collatz reaches `1` from `n`. Lean identifies the inductive predecessor language
with the conventional forward relation and proves the arbitrary-word converse by permanent
negative 3-adic valuation after the first illegal odd predecessor. For every nonzero integer
target it then constructs unit scalar representatives with `α=β=1` and proves that normalization
preserves the complete zero language. See `R32-S37` and
[`audits/m32-collatz-incidence-2026-08-10.md`](audits/m32-collatz-incidence-2026-08-10.md).

The broader guarded-affine route now has an audited terminal normal form. Clearing an odd
denominator reduces rational 2-integral reachability to an integer parity map. The all-unit and
all-expansive slope strata admit explicit finite-box decision algorithms; every mixed stratum is
affinely conjugate, after accelerating the unit branch, to one signed generalized `ax+B`
Syracuse map. Macro multipliers and finite-chart telescoping reject direct radix-tag, FRACTRAN,
and affine-controller encodings. Only carry propagation against the fixed eventually periodic
2-adic word `−B/a` remains. This is `R32-S40`, retained without a duplicate Lean orbit API because
the existing p-adic gate, genericity theorem, normalization, and two-plane compiler already own
every formal matrix seam. See
[`audits/m32-binary-affine-syracuse-2026-08-11.md`](audits/m32-binary-affine-syracuse-2026-08-11.md).

The GPI₂ decision report reaches the same arithmetic core from group theory. An effective basis
change turns any projective incidence into intersection of the positive monoid with an explicit
upper-triangular coset in `GL₂(ℤ[S⁻¹])`, equivalently identity membership in a rational
subset. For the checked Collatz projectivities, the generated group is the rank-two affine cusp
`ℤ[1/6]⋊ℤ²`, and the target varies only as a translation tested against one fixed rational
subset. This independently kills the proposed Tits-alternative split: the obstruction already
lies in the metabelian branch, while the positive monoid itself is free. The reduction is
retained as audited `R32-S41`; no general rational-subset library or unproved decision oracle was
added to Lean. See
[`audits/m32-parabolic-rational-subset-2026-08-11.md`](audits/m32-parabolic-rational-subset-2026-08-11.md).

The finite-shadow attacks on this artery are now closed at their exact scopes. The generic Lean
module `FinitePositiveImage` proves that a submonoid of a finite group contains inverses and that
a group-generating set has full positive monoid closure. Applied to the Collatz cusp, this is
audited `R32-O21`: every finite ambient image sends `P={A,B}*` onto the whole image of `Γ₆`, so
`R=PK` fills that image and cannot exclude any target translation.

This failure is not peculiar to positive-coset saturation. `R32-O22` gives explicit shears
`A=U(3)`, `B=L(3)` and rays `p=[1:1]`, `q=[10:13]`. Lean proves by ping-pong that their
representation is free, `Stab(p)=1`, and `q` is outside the rational orbit. The checked
five-factor bridge and idempotent interpolation send `p` projectively to `q` in every CRT
component. Lean now also constructs the modular inverses, composite-ring CRT unit, unimodular
rays, and one witness for every positive modulus. Thus one generic free-orbit no-instance
survives every ordinary modulus.

The affine critical shell has a complementary checked obstruction. `PeriodicShell` composes an
arbitrary nonempty list of rational `5`-unit affine scales, constructs its explicit rational
fixed point, proves that point is a `5`-adic unit, and propagates unit membership backward to
every phase. `shellPeriodicCycle` specializes this to every nonempty finite wait schedule of
`T_m(u)=(1+3u(2/3)^m)/5`. The infinite-completion theorem, exact finite-precision transition
calculation, rational-source aperiodic forward construction, and density and single-wait
rigidity of period-one points remain audited strengthening under `D2-O02`; they introduce no
unproved Lean dependency. The checked repeated-schedule theorem proves that each repetition
subtracts the schedule length from the `5`-adic valuation of displacement from its periodic
point. A distinct rational source can therefore repeat a fixed schedule inside the unit shell
only a computably bounded number of times. Exact target and accepting-exit reachability from a
specified rational source, rather than rational realization or fixed-block pumping of shell
paths, remains the benchmark seam.

`MixedPrimeDebt` resolves the valuation topology of genuinely varying schedules inside the
negative `3`-adic chamber. For a rational carrier `c` with `v₃(c)=0`, write `u=c/3^d`. Every
step which remains at positive depth has the exact recurrence

```text
d' = d+m−1,      c' = (2^m c+3^d')/5.
```

The only chamber exit is `d=1,m=0`. Conversely, a target `c'/3^d'` has one distinct debt
predecessor for every wait `m=0,…,d'`, with depth `d'+1−m` and carrier
`(5c'−3^d')/2^m`. If the target carrier is additionally a `5`-adic unit, every predecessor
carrier is a `5`-adic unit, so the whole fan is legal in the critical shell. Arbitrary
debt-safe schedules satisfy the checked Łukasiewicz balance
`d_end+length=d_start+sum(waits)`. Their slope is fixed by the two depths and the length; two
same-length bridges between the same depths which collide at one source are already the same
affine map globally. This moves all within-length point collisions back to the affine-kernel
problem. It does not bound the reverse tree: its exact fan has width `d'+1`, and cross-length
carrier equality remains open.

The cross-length collision itself now has a checked normal form. Every nonempty schedule has
both slope and intercept of `5`-adic valuation `−length`. Two unequal lengths therefore have
different slopes and collide at exactly

```text
u=(b_right−b_left)/(a_left−a_right).
```

Unequal valuations force both numerator and denominator to the negative larger length, so this
unique collision source is automatically a `5`-adic unit. Source-shell exclusion cannot prune
cross-length collisions. The common target is exactly

```text
y=(a_left b_right−a_right b_left)/(a_left−a_right),
```

and it is a `5`-adic unit exactly when the numerator determinant has valuation
`−max(left.length,right.length)`. Since its two terms begin at valuation
`−left.length−right.length`, this is an exact cancellation demand of the shorter length. For
debt-safe bridges between common endpoint depths with lengths `n` and `n+1`, the slope ratio
is forced to `2/5`. Writing the cleared rational offset as `C_w=5^|w|b_w`, Lean proves

```text
C_(m::w)=3^|w|(2/3)^sum(w)+5C_w,
y=(C_long−2C_short)/(3·5^n),
y is a 5-unit  ↔  v₅(C_long−2C_short)=n.
```

This is an exact adjacent-bridge carry law, not a decision procedure: the offset recurrence still
has unbounded length and varying exponents. Acceptance is not automatic. The debt-safe pair
`[4]` and `[0,5]` runs from depth two to depth five and collides at `2/9↦55/243`, whose target has
`5`-adic valuation one. Fixed-source equality is nevertheless saturated by an exact parametric
family. For every `m≥0`, the bridges

```text
[1,m+2]  and  [3,1,m]
```

run from depth one to depth `m+2` and both send `43/24` to
`(11(2/3)^m+9)/45`. For `m=10k`, Lean proves the cleared numerator
`11·2^(10k)+9·3^(10k)` has `5`-adic valuation exactly one, so the target is a unit. One rational
source therefore supports infinitely many accepted chamber-contained cross-length collisions
with unbounded waits. The target formula is injective in `m`; no fixed target occurs twice, and
fixed-target intersection with this ray reduces to testing its sole valuation-derived candidate
`m=max(0,v₂((45y−9)/11))`. Every target on the ray also satisfies the complementary endpoint
pole `v₂(1−2y)=0`, which is the normalized form of `v₂(6y_original−15)=0`. Thus the family lies
inside both unresolved endpoint shells, although it does not decide reachability outside this
one ray. Its first exit extension is exact as well. If `u_k` is the accepted `m=10k` target and
`E(k,r)=T_r(u_k)`, then every `E(k,r)` has `5`-adic valuation `−1`; a further tail of length `ℓ`
has valuation `−1−ℓ`. The displacement identity
`75E(k,r)−15=(2/3)^r(9+11(2/3)^(10k))` makes the surface injective and reduces fixed-target
membership to two explicit valuation-derived equality tests, separating the exceptional
`k=0` carrier from `k>0`. Thus neither the collision ray nor its first exit block has an infinite
fixed-target fibre. For every later tail, Lean recovers its length as
`max(0,−v₅(y)−1)` from the prescribed target and identifies the full fixed-source schedule as a
regular-control word with exactly three more shell blocks. The audited prescribed-translation-
count algorithm therefore decides the entire controlled continuation cone. The suffix bound is
in fact independent of this family: every nonunit step from any `5`-adic unit is zero, has
valuation `−1`, or has positive valuation. A zero or positive exit reaches valuation `−1` after
one further block. Hence every nonempty suffix to a fixed target has valuation `−1−ℓ` or `−ℓ`,
and its length `ℓ` is one of two explicit consecutive candidates. Arbitrary post-exit scheduling
is therefore decidable pointwise; the infinite benchmark seam is the set of pre-exit shell
prefixes and their exit images. Exact accepted examples also show that the debt chamber's one-bit
carrier residue is saturated: `[1]` and
`[1,1]` collide at `1/3↦1/3`,
while `[1]` and `[1,2,0]` collide at `19/42↦8/21`; their carrier orientations modulo three are
opposite, and both sources and both targets are `5`-adic units.

The real exterior is decidable. Every shell block preserves `[1/5,1/2]`; above `1/2` and below
`1/5`, the zero-wait block is extremal and contracts distance toward `1/2` by `3/5` per block.
Lean turns the resulting envelope into an explicit rational-search bound on schedule length.
The audited prescribed-count algorithm decides every smaller length. Thus real monotonicity leaves
exactly the closed recurrent target interval `[1/5,1/2]`; it supplies no further bound inside.
Indeed every rational `5`-adic unit target in `(1/5,1/2]` has a rational unit predecessor there.
Lean iterates this construction to produce guarded predecessor schedules of every prescribed
length. The source varies, so the remaining question necessarily couples both fixed endpoints.
Inside the trap, however, every fixed target has predecessors at only three consecutive waits.
Lean computes their maximal wait, reduces fixed-source one-step reachability to three equality
tests, and proves the width sharp. The reverse survivor is therefore a locally finite ternary
tree; only its unbounded depth remains. The deepest branch realizes every sufficiently deep band
and normalized mantissa. A period-fifty residue calculation exhibits guarded resets from source
depths `50k+50` to target depth four at fixed wait two, so depth and unit status do not form a
finite quotient. The same deep states are reached from the fixed real-trap source `2/9` at waits
`50k+48`; their targets are distinct.

Target depth itself is now eliminated from the fixed-endpoint seam. Lean proves that raising a
normalized target band and the final wait by the same amount preserves exact equality. For every
base depth at least two, the nonempty predecessor set is therefore unchanged by arbitrary upward
depth shifts; the reverse direction subtracts the shift from the final wait, whose nonnegativity
follows from the sharp three-wait window. Unit acceptance is periodic under depth shifts by ten.
Consequently every guarded nonempty fixed-source query reduces to depths `0`, `1`, or one of the
canonical representatives `2,…,11`, while retaining the exact rational mantissa. The surviving
unbounded object is the mantissa address, not Archimedean target depth.

That address is now exact. A target `U(d,μ)` has only the three predecessor candidates `μ/2`, `μ/3`, and
`2μ/9`; their waits are `d`, `d−1`, and `d−2`, with the last branch present exactly when
`μ>9/10`. For a reduced unit mantissa `a/b`, Lean expresses the normalized lower predecessor
through the centered numerator `N=10a−9b` and proves `gcd(N,b)=gcd(2,b)`. Odd denominators and
denominators divisible by four therefore have rigid two-adic updates. The sole secondary wall is
`b=2c` with `c` odd, where every remaining cancellation is exactly `v₂(5a−9c)`. Both the full
two- and three-adic transition formulas are checked. The wall supports an explicit infinite
guarded fixed family: for every `d≥7`, the reduced mantissa
`μ_d=3^(d−1)/(10·3^(d−3)−2^(d−1))` satisfies `9/10<μ_d≤1`, `v₂(b_d)=1`, centered
residual value `d−2`, and `T_(d−2)(U(d,μ_d))=U(d,μ_d)`. Lean also proves that every
repetition of this lower wait fixes the state and preserves every five-adic shell guard. Thus no
uniform strict height, odd-part, or centered-valuation descent can cross all lower branches. The
family is the exact secondary-wall coordinate of the singleton cycles previously known from
`PeriodicShell.shellPeriodicCycle`, not a new periodicity phenomenon.

Consecutive recurrence on that wall is finite. For a reduced unit transition
`a/(2c)→a'/(2c')`, exact cancellation gives `c=3^k c'` for some bounded `k`; every successor
therefore lies in the explicit rectangle `a'≤2c`, `c'≤c`. Lean proves that the lower-wall
transition witness has the computable depth `v₂(5a−9c)+2`; the relation is functional, and every
infinite wall-only orbit is eventually periodic. Lean also identifies the preceding fixed family
as terminal singleton components, preserves the five-adic state guard, and pairs every successor
with its canonical depth in the twelve-class product.
Thus an unbounded nonperiodic component cannot remain inside the secondary wall; only exits and
returns through the other reverse strata survive.

The first excursion stratum is terminal. Lean gives exact normalized coordinates for the upper
and middle predecessors and proves that a reduced denominator divisible by four remains divisible
by four under all three branches. The outgoing two-adic values are explicit, not bounds. It also
splits every lower-wall exit into value at most `−2`, exactly `−1`, or nonnegative value according
to whether `v₂(5a−9c)` is below, at, or above the canonical wall depth. Thus under-cancellation
can never return; only wall-preserving upper steps and over-cancellation into an odd denominator
remain.

`MixedPrimeKernel` now owns the raw `D,T` affine kernel. It checks the published shortest
length-27 relation, an infinite family of distinct equal-map pairs at every odd length
`29+2k`, and three independent length-30 relations. The former isolated length-29 relation is
the `k=0` member; `k=1` captures one of the seven relations found by the length-31 census.
`PeriodicShell.shellRun_eq_wordAction` proves the exact `z=5u` conjugacy from raw words to shell
schedules. The two schedule boundaries of the published relation are then factored in Lean as the
single raw context `T D^last _ D^first`; the apparent two-parameter schedule family is not a
family of new relations.

The odd raw family also lifts uniformly to the guarded shell. Exact schedule factorizations give
`shellRawWord_kernelOddScheduleLeft/Right`; `kernelOddScheduleContextGuard` proves equal guard
domains in every schedule context, and `kernelOddScheduleCycle` supplies a common rational
all-unit cycle for every pump depth.

`MixedPrimeNormalization` proves that this is exact normalized semigroup nonfreeness. The raw
action is realized by invertible homogeneous matrices; every odd-family pair has equal matrix
products and equal letter multisets, so arbitrary independent scaling of `D` and `T` preserves
the relation. The generic theorem
`MixedPrimeNormalization.groupPump_eq_of_zero_one` also shows that the `k=0,1` instances force
the entire odd family in any group-valued interpretation. This is a
cancellative pump only: the relations preserve length and letter content, and no fixed-source
reachability bound follows.

`shellRun_benchmarkRelation` proves global affine equality of the two published schedules;
`benchmarkRelationCycle` proves that their explicit periodic points coincide and every phase of
both cycles is a `5`-adic unit. The generic `shellPrefixesUnit_iff` identifies all-phase legality
with final-output unit membership; `benchmarkRelationContextGuard` therefore proves that the
relation preserves every intermediate shell guard in every word context. The source and
block-order translation are recorded in
[`cassaigne-nicolas-2012-semigroup-freeness.md`](references/cassaigne-nicolas-2012-semigroup-freeness.md).

Rewrite-system completion remains audited. With `D<T`, every checked rule is oriented from its
lexicographically larger side to its smaller side; equal length and content make termination
immediate. The published raw rule has two nonjoinable self-overlap critical pairs. The five-rule
basis has 45 nonjoinable proper critical overlaps, so it is not confluent. Exact enumeration of
all raw words proves that this basis accounts for every affine collision through length 30; seven
independent collisions appear among the `2^31` words of length 31. One is the formal index-one
family member; six remain computational. The exact enumerator and all-branch critical-pair
checker are retained in
[`audit_mixed_prime_kernel.rs`](tools/audit_mixed_prime_kernel.rs); its independent small-radius
self-check is part of the canonical gate, while the multi-billion-word census is not. No
presentation-completeness claim survives. Fixed-source point collisions add a separate stabilizer
problem. See
[`audits/m32-gpi2-residue-blindness-2026-08-30.md`](audits/m32-gpi2-residue-blindness-2026-08-30.md).

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
`(2,6)` exception explicitly, and uses fixed- or two-ray finite quotient certificates under the
general sieve [`R32-M02`](SALVAGE.md#r32-m02-finite-quotient-sieve) to
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

The cyclotomic gate now retains multiplicity on the no-reset side. If every prime factor of
`Φₐ(p)` outside the exponent support misses reset, the product of its full prime powers divides
the common cancellation. A nonterminal step therefore obeys both a terminal-defect height bound
and the sharper content-weighted pressure law

```text
p^((s−1)a) Pₐ(p) ≤ (|A|+|D|+|L|)H.
```

This removes repeated primitive prime powers as an untyped loss. Above wait two, Lean also
reconstructs the strong-part growth interface

```text
Φₐ(p) ∣ aPₐ(p),
p^((s−1)a)(p−1)^φ(a) ≤ a(|A|+|D|+|L|)H.
```

The literature's exact `Φ⁎ₐ(p)` classification is no longer required for this bound.

The converse normalization seam is now closed. Lean proves that canonical rational
numerator-denominator pairs are primitive, that the target unit condition forces the entire
`p^(sa)` scale into the raw common factor, and hence that every decoded rational step lifts to
one `PrimitiveIntegralStep`. Exact decoded paths lift without changing their length. A safe
exact-order quotient invariant therefore proves physical immortality directly; the
drift-divisor subgroup-avoidance family is nonvacuous even when the chosen terminal
coefficients are not themselves primitive.

At critical depth two, Lean now splits complementary endpoint contents as

```text
h=ηu,    k=θv,    ηθ=DL,    uv=pᵃ−1,
u,v>0,      gcd(u,θ)=1.
```

The attached `2 × 2` decoder has determinant `−1` and factors exactly as

```text
[[v,q²],[1,(q+1)u]] = [[1,v],[0,1]][[0,1],[1,(q+1)u]].
```

Thus its moving factors are continued-fraction data. Its explicit inverse confines every
subsequent common divisor to fixed coefficient support. Every prescribed factor of `pᵃ−1`
not swallowed by `h` divides `k`, with multiplicity, and is coprime to the target denominator.
In the weighted norm `|x|+4|y|`, every branch with `v≥2` contracts by at most `3/4` after
the natural `p^(2a)` rescaling. The exceptional branch `v=1` is reduced to one exact
first-order maximal-cancellation recurrence.

Parity now closes that exceptional branch as an infinite escape. Lean first proves generically
that two adjacent rational p-adic units force the valuation prime to be odd, then applies this
to the guard parameters. If `R=A+D−L` is odd, every primitive endpoint numerator reachable
from reset is odd, while the canonical physical target has numerator zero. Thus physical
mortality is impossible. If `R` is even, a maximal depth-two step simplifies to

```text
r′=θt+(Dq²+A−L)t′.
```

Its target numerator is odd; if another step follows, the next Smith coordinate `v` is even.
Thus maximal steps cannot terminate or occur consecutively. The proof consumes the existing
decoded-to-primitive lift, cumulative step equation, and Smith split; no second execution
structure or quotient state was introduced. See
[`audits/m32-parity-maximal-isolation-2026-08-04.md`](audits/m32-parity-maximal-isolation-2026-08-04.md).

The motivating multi-wait cocycle did not survive reconstruction. One step is exact in a
lagged wait frame; changing to the next wait requires a separate rational gauge. Lean checks
the lagged transfer, frame change, and honest composed cocycle. The ungauged global path bound
is false and is not part of the corpus.

Consecutive primitive endpoint reductions now carry one exact primitive edge coordinate. With
`q=p^a`, `Q=p^b`, and `Xᵢ=(tᵢ,hᵢtᵢ₊₁)ᵀ`, prequotient coprimality and a new depth-uniform
transport theorem give

```text
Q^s hᵢ Xᵢ₊₁ = [[0,Q^s],[DL(q−1),A+Dq^s−LQ]]Xᵢ.
```

No complementary content or tangent state enters the matrix. One fixed integral basis also
conjugates every rational wait gauge to `diag(1,Q²/q²)`. These theorems remove the missing
carried-coordinate and wait-gauge shear obstructions, but do not prove cone entry, a local
continued-fraction selector, or global height descent. See
[`audits/m32-prequotient-adelic-2026-08-06.md`](audits/m32-prequotient-adelic-2026-08-06.md).

The later Jacobi handoff proposal also failed reconstruction. The exact denominator recurrence
retains the coefficient `A+Dqˢ−Lq′`. If a divisor of reverse content recurs in the next
cyclotomic boundary outside `L(A+D−L)`, Lean proves that it is coprime to the next forward
content and divides the next reverse content with full multiplicity. Thus recurring factors do
not alternate into forward cancellation. See
[`audits/m32-jacobi-handoff-2026-08-05.md`](audits/m32-jacobi-handoff-2026-08-05.md).

Depth two now also has a coefficient-level prime-adic wall. For an integral presentation
`center=A/L`, `drift=D/L`, put `R=A+D−L` and, at any prime `ℓ`,

```text
λL=vℓ(L),  λR=vℓ(R),  λD=vℓ(D),  e=vℓ(p−1),  ε=vℓ(2).
```

Lean proves that `R≠0`, `λR<λL+e`, and

```text
2λR < λD+e+min(λL,λR+ε)
```

make the open `ℓ`-adic reset ball invariant under every positive decoded branch. The endpoint
identity is checked directly in the existing coordinate; the zero numerator-blade branch is
handled separately and returns exactly to reset. Terminal lies outside the ball, so the
arbitrary-word compiler yields physical immortality. Consequently every prime divisor of
`p−1` divides `R` for a mortal guard. The theorem does not assert that an arbitrary
common-period tail enters the ball. See
[`audits/m32-universal-boundary-2026-08-05.md`](audits/m32-universal-boundary-2026-08-05.md).

The proposed exact-order continuation is now fenced on its other side. Lean checks the
even-resultant guard `p=3`, `A=R=249398`, `D=L=1`: wait four enters the strict `5`-adic reset
ball, wait one breaks the exact order and returns to its boundary, and the target remains ready
at wait one. The bridge's primitive reduction removes exactly `18`, coprime to `5`, while its
denominator grows from `19` to `270178`. This excludes every uniform first-bridge invariance,
auxiliary-content, repetition, or denominator-descent charge under continued readiness. The
submitted endpoint normalization formula was not duplicated: it is the existing complete
cancellation law transported through the checked endpoint factorization. See
[`audits/m32-order-breaking-bridge-2026-08-05.md`](audits/m32-order-breaking-bridge-2026-08-05.md).

The proposed all-legal block theorem is now false. Lean checks the fixed guard

```text
p=3,   A=17,   D=−5,   L=16,   reset=3/4,
```

whose reset is ready and fixed, together with legal off-reset corridors longer than any
prescribed bound. Every corridor edge has wait one, exact primitive content `−4`, and Smith
coordinate `v=2`. Both the carried prequotient pair and the actual primitive Smith quotient are
primitive and rise strictly along arbitrarily long runs of consecutive edge coordinates; the
raw Smith decoder output is exactly four times the latter pair. A new generic theorem verifies
that the primitive endpoint equation
is the actual rational `guardedStep`, so legality is not inferred from a parallel recurrence.
This rejects coefficient-uniform carried or Smith descent over all legal corridors. It does not
reject a theorem anchored at reset or the terminal boundary: every constructed state is off
reset, while reset itself is fixed. See
[`audits/m32-periodic-shadow-2026-08-06.md`](audits/m32-periodic-shadow-2026-08-06.md).

The proposed positive-renewal continuation is also closed. The existing exact branch-similarity
theorem already proves that every nonempty aligned macro subtracts its full schedule weight from
p-adic separation, so no fixed macro or finite aligned ray cycle can replenish shadow depth.
Formalization strengthens the fixed obstruction family in the other direction: exact remaining
depth two, together with fixed coefficients, wait, content, and Smith label, coexists with
arbitrarily large endpoint and carried heights. A new cumulative theorem records the
reset-history datum exposed by this attack exactly:

```text
Δ(P₀,adj(M_u)V)=p^(s∑u)Δ(Pᶜ_u,V).
```

The local renewal dichotomy is therefore exhausted. See
[`audits/m32-renewal-collapse-2026-08-07.md`](audits/m32-renewal-collapse-2026-08-07.md).

The next ratchet shows that the pulled-back family is not radially moving at the distinguished
prime. Every nonempty positive endpoint product reduces modulo `p` to one fixed rank-one flag,
and every actual cumulative prefix from reset has the exact full-weight kernel

```text
ker(M_u mod p^(s∑u)) = (ℤ/p^(s∑u)ℤ)·P₀.
```

Positive endpoint terminality is also complete: it is equivalent to inverse address one, so the
endpoint zero language is singleton-or-empty and physical mortality is exactly the existence of
a nonempty endpoint zero. The coefficients `(3,2,122753,−17,39232)` have unique terminal word
`[1,1,1]`, refuting every universal two-return bound. The live question is now a coefficient-
effective auxiliary-place bound on the global angular carry, opposed by an exact aperiodic
reset-started orbit with unbounded denominators. See
[`audits/m32-fixed-geodesic-endpoint-completeness-2026-08-07.md`](audits/m32-fixed-geodesic-endpoint-completeness-2026-08-07.md).

The fixed-support universality branch is now bounded without enlarging the Lean API. A finite
control system whose canonical tails are rational functions of fixed auxiliary-prime powers and
whose waits are affine in their exponents cannot execute a repeatable cycle. Laurent-monomial
charts cannot execute even one nonconstant instruction, and one affine monomial ray has at most
five exact instruction samples. The proof is an independently reconstructed combination of
paired-prime-power Zariski density, Laurent-support comparison, the checked common mod-`p` flag,
and the Gauss valuation. It is retained as audited `R32-O15`, not as a second polynomial-chart
library. See
[`audits/m32-fixed-support-toric-obstruction-2026-08-08.md`](audits/m32-fixed-support-toric-obstruction-2026-08-08.md).

The nonsplit cubic fallback has also lost its proposed punctuation channel. `CubicReturn` proves
that `A³=NI`, with `N≠0`, reduces every arbitrary return word exactly to a word over the three
residue returns and transfers physical mortality to that finite triple. The surrounding audits
derive a common-left reflection form for every irreducible cubic and the exact pure
one-singular normal form `(P R,P,P Jμ)`. Lean now checks the decisive synthesis: for row
`(1,1)` and column `Pe₁`, both exceptional reverse-compiler scalars are `μ⁻¹`. The pure fork is
therefore already GPI₂; only the non-pure recurrence-of-reflections orbit remains independently
open. See
[`audits/m32-cubic-punctuation-collapse-2026-08-08.md`](audits/m32-cubic-punctuation-collapse-2026-08-08.md)
and
[`audits/m32-cubic-reflection-generic-bridge-2026-08-09.md`](audits/m32-cubic-reflection-generic-bridge-2026-08-09.md).

The non-pure fork is now canonical without another Lean API. Projected multiplication on the
cubic field's trace-zero plane gives `Mₙ=F T_(γθⁿ)` with arbitrary twist `F`; Clifford
normalization turns mortality into endpoint reachability on the determinant null conic. The
explicit physical family with characteristic polynomial `X³−X−1` has two unit returns generating
a free binary submonoid with an injective rational-line orbit. This rejects finite bridge-state
or bounded-length collapse from recurrence order and involutivity alone. That first line witness
was not singular-endpoint-faithful; `R32-S42` below closes precisely that former seam. The
trace/Jordan coordinates were culled as a duplicate formal representation; see
[`audits/m32-cubic-null-conic-orbit-2026-08-10.md`](audits/m32-cubic-null-conic-orbit-2026-08-10.md).

The formerly missing endpoint placement is now realized, and formalization cuts deeper than the
submitted numerical instance. `CubicReturnNonPure` defines one common non-pure companion ambient,
proves its exact order-three return recurrence, invertibility, failure of every pure-cubic
relation, and rank two of two physical cuts. The first twist checks
`M₀M₁M₀=0`, while audited interval ping-pong keeps its selected semigroup free. For the
second twist Lean proves that every word over selected waits `{1,5}` misses the actual singular
kernel, yet the strictly unselected word `[12,12,8,12,12,15,8]` gives an exact zero between
singular returns. This closes endpoint geometry and kills selected ping-pong as an arbitrary-word
guard. The live cubic object is the complete fixed recurrence, not another reflection coordinate
system. See `R32-S42` and
[`audits/m32-cubic-endpoint-false-waits-2026-08-11.md`](audits/m32-cubic-endpoint-false-waits-2026-08-11.md).

The rank-(2,2) graph is no longer an independent residue. `RankTwoPunctuation` proves that every
compatible square with one rank-one loop and three units transports exactly to the existing raw
reverse compiler [`R32-M01`](SALVAGE.md#r32-m01-generic-reverse-edge-compiler). Its intrinsic
first scalar is the loop self-bridge and compatibility forces the second scalar to one; mortality
is exactly immediate loop nilpotence or one generic PI₂ instance. The remaining edge-rank
patterns and the effective cyclic-orbit discharge of the cross-edge case are audited as
`R32-S32`, using the locally recorded Evertse–Győry unit-equation
theorem. The full audited rank-(2,2) boundary is `Mort₃^(2,2) ≡ₘ GPI₂`; `R32-S35` separately
reduces arbitrary PI₂ to at most two GPI₂ queries. See
[`audits/m32-rank-two-punctuation-2026-08-08.md`](audits/m32-rank-two-punctuation-2026-08-08.md).

The proposed endpoint-only angular compactness has a checked counterexample. For the lawful
first-hit terminal word `[3,1]` at `(p,s,A,D,L)=(3,2,467,−35,124)`, Lean computes the full
endpoint product and primitive pole `(494,−41)` and proves that its emergent primes `19,41`
divide neither the coefficient/reset support nor any branch-cyclotomic factor. The surrounding
audit shows why: terminality leaves the angular extension lift free, and the pure-`p` wait gauge
has projective adelic height `p^(2|b−a|)` rather than one. `R32-O17` therefore retires every
support-only or direction-free product-formula proof. The exact additive continuant was already
present in the cumulative endpoint recurrence, so formalization adds only the consuming
counterexample. See
[`audits/m32-angular-emergent-primes-2026-08-08.md`](audits/m32-angular-emergent-primes-2026-08-08.md).

The recurrence-sensitive gcd has now been localized. The lower row of the final endpoint
transfer gives an exact Casoratian showing that every common divisor of the terminal scalar and
the angular coefficient divides the determinant of the preceding word. The final branch creates
no primitive normalization. The surrounding `R32-S33` audit combines this checked identity with
the existing recurrent-boundary and primitive-part theorems: exact-order mass persisting to the
right is forced forward, mass persisting to the left is forced reverse, the global wait gcd is
effectively finite, and divisibility-chain terminal schedules are decidable. The unformalized
global induction introduces no new state or recurrence API. See
[`audits/m32-casoratian-order-allocation-2026-08-09.md`](audits/m32-casoratian-order-allocation-2026-08-09.md).

The moving-support allocation is also exact. Outside `pDL`, an arbitrary composite divisor
enters forward content if and only if it divides both the current endpoint numerator and the
current branch boundary `pᵃ−1`. This theorem retains every prime-power multiplicity and gives the
Casoratian's emergent-prime consequence an exact activation rule. The report's reciprocal
coordinates and Wronskian were culled as duplicate representations; its no-Mahler theorem is
already subsumed by the checked rational-rail degree obstruction. See `R32-S34` and
[`audits/m32-moving-prime-ledger-2026-08-09.md`](audits/m32-moving-prime-ledger-2026-08-09.md).

The content calculus also subsumes the proposed endpoint potential without another Lean API.
Iteration in its fixed endpoint-adapted norm bounds cumulative content jointly with reduced
denominator, forces fresh activated primes to have count `O(N/log N)`, makes every activated
packet microscopic on an aperiodic orbit, and imposes logarithmic recovery after large
allocation. Consecutive full-numerator handoffs have bounded second wait. Formalization then
continued the reported order-breaking tuple instead of leaving it as an unproved candidate:
Lean checks its forced wait prefix `[4,1,1,1,1]` and the ensuing nonterminal 3-adic unit, which
lies in the forward-invariant trap. See `R32-S29`,
`ReturnGuard.Examples.orderBreaker_candidate_enters_trap`, and
[`audits/m32-sparse-genealogy-budget-2026-08-10.md`](audits/m32-sparse-genealogy-budget-2026-08-10.md).

The proposed all-packet endpoint potential is false. The period-three guard has exact primitive
forward and reverse contents, and its endpoint macro has two rational eigenlines. Lean proves
that every repeated legal period fixes the residual reset while the transverse eigenvalue gains
one exact factor of thirteen and the reset eigenvalue remains coprime to thirteen. This is
`R32-O20`, formalized by `ReturnGuard.Examples.cycle_endpointReductions` and
`cycle_transverseReservoir`; the associated reset-defect and terminal-content estimates are
audited corollaries of the existing `R32-S29` calculus rather than a duplicate API. See
[`audits/m32-transverse-reverse-reservoir-2026-08-10.md`](audits/m32-transverse-reverse-reservoir-2026-08-10.md).

First-hit terminality now has a sharper replacement for that false endpoint potential. Pulling
reset backward through the terminal address gives a canonical same-address companion, and the
existing inverse-address, primitive-lift, exterior-product, and complementary-content theorems
already own its exact transport law. Their audited synthesis turns actual reverse content into
companion forward content and compresses the unresolved mass to one angular gcd deficit. No
duplicate companion API was added. Lean instead checks the consuming counterexample:
`ReturnGuard.Examples.resetCompanion_counterfamily` is an unbounded family of one-return
first-hit histories for which the actual forward product exceeds the companion reverse product
by `(12n+1)/2`. Thus per-step shadow descent and multiplication of local Smith savings are false;
only coefficient-effective bilateral amortization across a complete first-hit history remains.
See `R32-S39` and
[`audits/m32-reset-companion-2026-08-11.md`](audits/m32-reset-companion-2026-08-11.md).

The widened finite-atlas counter route is also closed without adding Lean code. For finitely
many rational tail charts and finitely many fixed additive wait shifts, polynomial divisibility,
degree at infinity, and leading/constant coefficient comparison force every control-cycle shift
to sum to zero. Recurrent shifts are therefore a coboundary; waits become bounded and the
deterministic rational orbit is eventually periodic. This is retained as audited `R32-O18`.
The existing formal one-chart rail and bounded-denominator periodicity theorem already own both
ends of the argument, while a general rational-function atlas would not tighten the surviving
history-sensitive enemy. See
[`audits/m32-finite-radial-atlas-2026-08-08.md`](audits/m32-finite-radial-atlas-2026-08-08.md).

The schedule-first counter route now has one exact Jacobi coordinate. Lean proves the consecutive
shell transition and the backward map's reciprocal difference factor. Their p-adic iteration
gives one compatible unit tail for every prescribed wait schedule; reset-started rational
realization is one scalar continued-fraction incidence. The audited consequences exclude finite
handoff alphabets and one fixed rational ready-tail chart from every aperiodic orbit. These
infinite completion and height arguments are not kernel checked; they consume the checked finite
identities and the existing formal rail theorem. See `R32-S38` and
[`audits/m32-jacobi-schedule-incidence-2026-08-11.md`](audits/m32-jacobi-schedule-incidence-2026-08-11.md).

These are structural and decidable-stratum theorems, not an `M₃(2)` resolution. The imported
order-four Skolem theorem used to classify rank-one profiles is not reimplemented in Lean. The
reverse compiler still assumes `αβ≠0`, but arbitrary PI₂ now reduces to at most two generic
queries. No universality or decision theorem is known for normalized GPI₂, despite its exact
shortcut-Collatz subfamily, or for rational inverse-address membership and its cyclotomic
cancellation histories. Their boundary is recorded in
[`audits/m32-rank-return-2026-07-28.md`](audits/m32-rank-return-2026-07-28.md) and scheduled in
[#11](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/11) and
[#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

## Audited But Unformalized

[`G3-S01`](SALVAGE.md#g3-s01-shift-equivariant-zero-incidence) identifies same-zero dimension
with shift-equivariant row-column incidence dimension. Its static factorization is elementary;
the decisive burden is compatibility with common letter maps, which is why the support-only
rank arguments below do not settle the three-state wall.

The static half of [`G3-O05`](SALVAGE.md#g3-o05-cancellative-projective-state-tax) is fully
formalized: phase-aware prefix decomposition, free-group residual equality, one global rational
conic factorization of the paired zero support, and the rank-three bound for every finite sample.
Lean also checks the four role fractions and the rational odd-dimensional commutator law. The
remaining dimension-tax proof comprises the parameterized Stallings fiber product,
inverse-saturated projective descent, fixed-locus lemma, and the commutant classification excluding
`F₂×F₂≤PGL₃(ℚ)`. These are audited in
[`m34-cancellative-projective-no-go-2026-08-06.md`](audits/m34-cancellative-projective-no-go-2026-08-06.md).
No claim about general positive-only projective dynamics is made.

[`G3-O11`](SALVAGE.md#g3-o11-positive-shifts-do-not-force-saturation) closes that omitted
implication by counterexample. Lean checks three explicit integral generators on the whole free
monoid: their scalar zero language is `{t}`, every generator has rank two, selected reachable and
observable context matrices have determinants `1` and `−1`, and no matrix product vanishes. It
also checks the decisive collision `H_bγ=H_bH_tγ` with `γ≠H_tγ`, hence failure of backward
cancellativity. The injective semidirect-product labeling into a group containing `F₂×F₂`, the
infinite Fibonacci orbit, and the no-nilpotent-product strengthening remain audited paper
arguments; the formal counterexample does not depend on them.

[`G3-O17`](SALVAGE.md#g3-o17-paired-inverse-chamber) closes the paired-specific saturation
repair itself. Lean proves that every actual suffix residual has reduced sign form `+*−*`, every
phase-aware prefix residual has form `−*+*`, and the formal inverse states
`x⁻ᵝzxᵝz⁻¹` and `xz⁻²x⁻¹z²` have both sign turns. It checks their exact origin in the independent
role discrepancies, every Neary upper/lower endpoint letter, free reduction of all positive
continuations, and disjointness of both complete forward cones from every actual residual. Thus
inverse-orbit cofinality is false for the grammar; only an extra representation-specific
projective completion remains outside the theorem.

[`G3-O12`](SALVAGE.md#g3-o12-positive-reset-dimension-tax) attacks the constructive side without
formal inverses. Lean defines projective ray equality over an arbitrary finite-dimensional
rational vector space and proves that a legal prepend cylinder spanning the space forces its data
map to be injective. Applying this to both data letters at the single legal queue `qb` proves
`v_q∼v_ε` from the four reverse rule/erase equations. It also checks the determinant
`B²(B−1)(d_b−d_c)` for the standard homogeneous radix cylinder. The resulting four-dimensional
ambient tax for a faithful three-vector legal chart is retained as an audited dimension
corollary; the kernel theorem states the exact collision and hypotheses.

[`G3-S02`](SALVAGE.md#g3-s02-rank-two-kernel-bifurcation) records the singular geometry left by
that tax. Lean proves that a route difference in a common data kernel remains there through any
number of kernel-preserving toggles and is annihilated by the first subsequent data action. For
transverse coordinate kernels it also proves the exact projective fibre intersection: quotient
targets `[u:v]` and `[r:s]`, with `s≠0`, determine the bilinear ray `[rv:us:vs]`. These are
structure theorems, not a universal exclusion of common-kernel history-sensitive compilers or a
construction of the missing shift-equivariant bilinear invariant. The existing periodic compiler
now supplies the sharp countercase: Lean computes its exact common data kernel, proves that its
toggle leaves that kernel, and proves nonzero recovery by either next data action. Hence only the
toggle-invariant common-kernel subcase factors away.

The semantic core of [`G3-O04`](SALVAGE.md#g3-o04-expanding-affine-history-no-go) is formalized:
the reset-affine orbit, finite reverse box, exact caged DFA, regularity, and universal
noncomputability contradiction are kernel-checked. The remaining mechanization seam is uniform
extraction of a mathlib `ComputablePred` decision procedure from an encoded rational
normalization certificate. The finite graph algorithm is audited in
[`m34-expanding-history-no-go-2026-08-06.md`](audits/m34-expanding-history-no-go-2026-08-06.md);
the broader phrase “finitely many rational curves” is rejected without the formalized shared
affine-coordinate transition law.

For [`G3-C02`](SALVAGE.md#g3-c02-fixed-bcbc-singular-recognizer), Lean checks the complete
residual grammar, terminal grammar, affine state recurrence, determinants, canonical decoder, and
all intended terminal zeros. The remaining theorem is the arbitrary-control converse for the
displayed matrices. Its finite reverse graph is audited, but the rank certificate has not yet
been transcribed into Lean. No publication-facing theorem identifies the matrix and paired zero
sets until that transcription is complete.

For [`G3-C05`](SALVAGE.md#g3-c05-equal-length-mixed-branching-recognizer), no converse remains
outside Lean. The body `bcbcbb` has exact terminal grammar `P₀(A₀|B₀)*`, with two distinct
equal-length null blocks. Lean proves the grammar from residual paths, the complete raw-control
toggle normal form, the integral affine recurrence, and every node and dead branch of the
inverse congruence graph. The publication-facing theorem
`MixedBranchingRecognizer.recognizerCoefficient_eq_zero_iff_paired` identifies the displayed
three-state coefficient zero set with the paired coefficient zero set on every control word.
The same module checks singular data determinants, the exact common kernel, toggle involution,
nonzero boundary vectors, affine-chart suffix states, and absence of zero generator products.
This is a fixed-body countermodel only; no source-uniform terminal-section theorem is claimed.

For [`G3-M02`](SALVAGE.md#g3-m02-square-root-punctuation-fracture), the complete fracture,
explicit square identity, exact rank, and exact/weighted-series rigidity are formalized. The
source-specific reverse-marker exclusion and the immortality of every boundary-aligned additive
fusion are retained as audited paper proofs. [`G3-O10`](SALVAGE.md#g3-o10-square-root-boundary-saturation)
now closes the construction itself: Lean proves that every nondegenerate rank-one square root
scales both boundary vectors, hence preserves coefficient vanishing under either boundary
insertion. It also proves that every arbitrary Neary terminal match starts with `R_c`, that an
`R_b` prefix never vanishes, and the resulting same-zero contradiction on a square-free witness
pair. The final assembly of that pair from a complete width-at-least-three stroke history remains
an audited list-syntax composition, not a hidden publication-facing theorem.

For [`G3-O08`](SALVAGE.md#g3-o08-erasing-and-stationary-closed-block-obstruction), Lean checks
the exact paired bit counts, injectivity and nonsingularity of the four-role Parikh matrix, the
arbitrary erasing macro factorization, and its cardinality-four consequence. It also checks the
two complete integer case reductions used by the stationary closed-block theorem. The remaining
kernel-dimension assembly, the nonempty-deletion word argument, and the application to mixed
universal compiler bodies are independently audited in
[`m34-ternary-closed-block-no-go-2026-08-08.md`](audits/m34-ternary-closed-block-no-go-2026-08-08.md).
Accordingly, the exact erasing-macro theorem is publication-facing; the broader closed-return
no-go is not advertised as Lean-checked.

[`G3-O13`](SALVAGE.md#g3-o13-rational-serializer-pumping) closes the finite-control extension at
the paper-audit level. Lean strengthens the checked seam to a bidirectional equivalence between
the binary terminal equation and `consumed(H)·b=c·produced(H)` on every exact stroke history,
including null extensions, and verifies the final natural-number contribution contradiction.
The periodic-insertion lemma, asynchronous-transducer pumping, and three-pulse word-factor audit
are independently reconstructed in
[`m34-rational-serializer-pumping-2026-08-08.md`](audits/m34-rational-serializer-pumping-2026-08-08.md).
The same audit proves [`G3-D01`](SALVAGE.md#g3-d01-bounded-prefix-residuals) by an explicit finite
free-prefix-reduction graph; no Lean declaration currently extracts that generic decision
procedure.

[`G3-D02`](SALVAGE.md#g3-d02-virtually-cyclic-prefix-discrepancy) strengthens the global decision
boundary. Lean checks that equality after arbitrary continuations forces the original prefixes to
be comparable, so a first mismatch is permanent, and proves all four signed residual update laws
and both terminal-boundary tests exactly. The two-power periodicity lemma and reduction of a
finite union of capped periodic rays to one-counter reachability remain independently audited in
[`m34-virtually-cyclic-discrepancy-2026-08-08.md`](audits/m34-virtually-cyclic-discrepancy-2026-08-08.md).
No publication-facing declaration claims the generic decision procedure.

[`G3-D04`](SALVAGE.md#g3-d04-priority-affine-residual-atlas) strictly extends that audited
decision boundary to any finite-dimensional effectively proper affine atlas whose equality guards
test one fixed nested priority of counter prefixes. Lean checks the exact transition macro: debit
the guarded constants, test the initial segment for zero, then restore the constants while adding
the requested translation. It also proves nesting monotonicity. Decidability of the resulting
VASS with nested zero tests is imported from Guttenberg, Czerwiński, and Lasota; the effective
atlas-to-machine assembly and normal-witness decision theorem remain independently audited.

[`G3-D05`](SALVAGE.md#g3-d05-priority-triangular-transfer-atlas) extends that boundary beyond
finite unions of translations. Lean defines one destructive forward fanout, proves that natural
semantics forbids overdrain, and proves that the next nested-prefix exit test forces exactly one
loop per old pivot token. The resulting equivalence identifies the logical reset/transfer with
an ordinary VASS drain loop plus one nested test in both directions. Lean also proves that the
unbounded reset graph is not a finite union of translations, establishing strict extension of
`G3-D04`. Cascading private stages, finite atlas assembly, properness reduction, and VASSnz
decidability remain audited rather than encoded as a new reachability implementation.

[`G3-D06`](SALVAGE.md#g3-d06-functional-phase-transfer-guillotine) closes the functional
private-head source architecture. Lean classifies all eight labeled loopless maps on three
phases, constructs positive rational weights which kill two transfer drifts exactly, and proves
that the remaining drift makes all three one-sided. A separate finite-sum theorem lifts those
phase weights through every nonnegative quotient with positive column support to strictly
positive symbol weights. Lean also checks the two- and three-cycle product inequalities and the
sharp forked two-cycle whose three Parikh drifts remain mixed under every positive weighting. The
bounded-word reachability enumeration induced by the one-sided weight is audited rather than
implemented as a second decision procedure.

[`G3-D07`](SALVAGE.md#g3-d07-pure-phase-fork-closure) closes complete pure two-chamber forks,
including the mixed-drift canonical example. Lean proves that opposite drifts in an additive
relation force a positive diagonal and checks the canonical fork's exact linear equations,
factor-two bounds, residue law, additivity, symmetry, and descent steps. The effective regular
trace reduction to a semilinear additive relation, the finite residue grammar, and the final
decision step are audited. The imported theorem is Bizière and Czerwiński's peer-reviewed
decidability of one-dimensional GVAS reachability. No declaration claims decidability when a
mixed or neutral word survives the return, a consume is empty, or recurrent output splits.

[`G3-C03`](SALVAGE.md#g3-c03-endpoint-prefix-compiler) supplies the exact direct compiler for a
three-production prefix normal system. Lean defines traced execution, proves that every lawful
trace telescopes to its endpoint equation, and proves the converse under endpoint prefix forcing
by reconstructing every intermediate residual. It also checks a three-production underflow
counterexample: the aggregate boundary equation holds although the first rule is inapplicable.
Thus the compiler theorem is publication-facing; existence of an undecidable source satisfying
its hypothesis is not claimed.

[`G3-C04`](SALVAGE.md#g3-c04-head-separated-endpoint-debt) discharges that forcing hypothesis
locally whenever every production emits a nonempty word whose first symbol is absent from the
same production's consumed word. Lean compares the two initial prefixes of an endpoint equality:
if the source ends inside the consumed word, the remaining nonempty debt begins with a consumed
symbol, while the output begins with the forbidden fresh symbol. This contradiction removes the
first underflow, reconstructs the complete trace, and proves endpoint prefix forcing for every
source and target. Universality inside this restricted source class remains open.

[`G3-D03`](SALVAGE.md#g3-d03-one-sided-corrected-drift) is formalized only at its arithmetic
throat: every prefix of a nonnegative corrected-drift trace spends at most the total endpoint
budget. The finite-control potential criterion, accepting-residual bound, exact search graph, and
source-rewriting consequence are independently audited in
[`m34-endpoint-prefix-compiler-2026-08-08.md`](audits/m34-endpoint-prefix-compiler-2026-08-08.md).
No Lean declaration claims the generic decision procedure.

For [`G3-M01`](SALVAGE.md#g3-m01-free-group-discrepancy-engine), the rank-`3m+1` closed-path
basis, the trivial-or-cyclic fixed-subgroup classification, and the rank-zero-or-one equalizer
corollary are audited consequences of Carvalho's explicit inverse transducer. Direct source
inspection also proves the exponent-one equalizer sharpening
`C halts ↔ ∃u, g(u)=h(u) ∧ κ(u)=1` and the global character identity `χ∘g=χ∘h`. Lean does not
reconstruct the transducer or these external consequences.

[`G3-M03`](SALVAGE.md#g3-m03-three-positive-affine-exponent-cover) isolates the exact positive
cover used by that surviving slice. Lean defines the first-generator exponent on `F₂` and the
signed positive weight `#x−#z`, then proves that triangle evaluation preserves them exactly. More
strongly, evaluation from positive words of any prescribed signed weight onto free-group elements
of the matching exponent is surjective. The positive identity spelling `xyz` has weight zero, so
padding preserves both the group value and affine constraint. The Nielsen-Schreier embedding of
Carvalho's source group into the finite-index exponent subgroup and the full-pair `GL₃` no-go
remain audited rather than formal dependencies.

[`G3-O19`](SALVAGE.md#g3-o19-correlated-affine-slice-density) is wholly audited rather than a
Lean dependency. For the synthetic graph `h=id`, `g(a)=a`, `g(b)=b²`, the equalizer and affine
slices are checked by free-product normal form. Zariski density follows from dense projections,
algebraic Goursat, and the unequal projective trace-squared values `16` and `196`; the
dimension-four carrier bound then uses the characteristic-zero representations of
`SL₂×SL₂`. Exact arithmetic reproduces the displayed `4×4` Hankel minor and determinant
`1,197,990`. None of these claims is promoted to the actual Carvalho program graph or to a
same-zero language lower bound.

[`G3-O21`](SALVAGE.md#g3-o21-actual-carvalho-slice-density) is also audited rather than a Lean
dependency. For the actual numbered-state transducer, explicit kernel-character loops give dense
projections; algebraic Goursat and the fixed noncommuting marker subgroup reduce the graph case to
conjugation by the initial discrepancy; `ψ(0ᵐ)=Hᵐ` contradicts that case. Thus every
fixed-character slice of the actual correlated graph is dense under a faithful Schottky
embedding. The representation-theoretic dimension-four conclusion applies only to
algebraically extendable carriers using both coordinates, not to same-zero language rank or
spelling-sensitive/nonalgebraic dynamics.

[`G3-O22`](SALVAGE.md#g3-o22-invertible-fibre-span-rigidity) is formalized at its linear-algebra
core. Lean proves exact transport of positive spelling-fibre spans under every invertible word
transition, transport back under the inverse equivalence, common positive fibre rank, the
rank-one/rank-two dichotomy under a nonzero scalar boundary in dimension three, and equality with
the boundary kernel in the rank-two branch. It also constructs the unital identity-word operator
algebra and identifies its seed orbit with the identity fibre. The finite context-free subspace
saturation algorithm computing that algebra for the triangle cover is audited, not formalized.
No Lean declaration identifies inverse orbit edges with positive generators or claims a positive
`M₃(2)` reduction.

[`G3-O23`](SALVAGE.md#g3-o23-singular-triangle-carrier-collapse) is formalized through literal
two-state rational coordinates. Lean proves that a rank-at-most-one semantic identity loop makes
every group-saturated scalar zero language universal or empty. In dimension three, a nontrivial
singular identity loop therefore has rank two; every letter sandwiched through its image is
invertible, since a singular sandwich and a positive inverse spelling would create another
rank-at-most-one identity loop. Interleaving the identity word gives exact zero equivalence for
all words, including the empty word. Lean chooses a basis of the image, conjugates the carrier to
`Fin 2→ℚ`, supplies a fixed invertible model for the empty language, and specializes the result
to the triangle dichotomy: either all original transitions are invertible or an equivalent
everywhere-invertible two-state carrier exists. Rational Gaussian-elimination effectivity requires
an effective positive inverse-spelling section, fixed explicitly for the triangle cover. The
`F₂` singleton-fibre `PGL₂`/at-most-one Borel-coset sharpening is also audited outside Lean. No
declaration converts group inverses into positive controls or claims `M₂(3)`.

[`G3-O24`](SALVAGE.md#g3-o24-directed-dyck-absorption-collapse) is formalized in the algebra
which owns the cancellation relation. Lean proves direct finiteness for every finite-dimensional
algebra over a field, then lifts it to complete scalar-value contexts and to any selected
zero-context family which separates elements projectively. It also proves the two necessary
failures for an asymmetric zero carrier: the forward product is not a nonzero scalar identity,
and the selected contexts are not globally projectively faithful. The application to the
directed Matiyasevich–Sénizergues stable cone, including its positional redex semantics and
greatest-lower-bound decoder, is source-audited rather than encoded in Lean.

The adjacent [`R32-O22`](SALVAGE.md#r32-o22-congruence-blind-free-orbit) obstruction applies to
this residual group-orbit shell: its all-modulus CRT closure is formalized without claiming
orbit density, decidability, or hardness for rational Borel-coset intersection.

Lean checks the internal algebra at the positive boundary: three positive letters surject onto
the binary free group; quotient-blind boundaries accepting `g` and `g²` admit a nonempty identity
witness; every injective transition on a finite invariant semantic fibre pumps an identity loop;
and a singular lift over a one-dimensional kernel absorbs every later quotient identity. It also
checks a six-row support certificate proving that any standalone scalar zero test for the
triangle-irreducible spelling language needs at least six states. The exact division is recorded
in [`m34-free-group-discrepancy-2026-08-08.md`](audits/m34-free-group-discrepancy-2026-08-08.md)
and
[`m34-positive-cancellation-obstructions-2026-08-08.md`](audits/m34-positive-cancellation-obstructions-2026-08-08.md).

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

The boundary-correct setter shear detour is closed in Lean. Record
[`MM-O12`](SALVAGE.md#mm-o12-boundary-calibrated-setter-shear-is-gauge) comprises
`SetterShear.sideBasis_det`, `SetterShear.delimiter_cube`,
`SetterShear.delimiter_square_distinguishedColumn`, and `SetterShear.transfer_tail`. Together
they prove that the side-basis shear changes coordinates but, after physical calibration,
changes neither the internal rank-one separator nor the transfer tail. It therefore cannot
repair the missing arbitrary-depth projective-avoidance theorem.

The decimal hyperbolicity route now has a formal closure boundary. Record
[`MM-O14`](SALVAGE.md#mm-o14-decimal-setter-elliptic-product) proves exact coefficient boxes
for a defect-`11` leading-`b` block and `D_c`; both J-fraction matrices are strictly hyperbolic,
but their product is elliptic. The public declaration is
`SetterJFraction.leadingB_elliptic_pair`. It closes real-cone deductions from individual
hyperbolicity without claiming a false pole orbit.

The decimal arithmetic seam is now kernel-checked. Record
[`MM-S12`](SALVAGE.md#mm-s12-decimal-two-prime-carry) comprises
`DecimalSetterArithmetic.centeredCoordinate_step`, `reciprocalCoordinate_step`,
`successive_pole_shellBalance`, `multiErasure_trace_hasDecimalShell`, and the two singleton
erasure shell theorems. Together they prove the centered and reciprocal carry recurrences, the
exact `(1,1)` and `(β+1,β)` target shells, and the simultaneous valuation balance forced by a
prospective pole. They do not decide the normalized decimal suffix on the surviving `(1,1)`
corridor and therefore do not prove projective avoidance.

Record [`MM-S13`](SALVAGE.md#mm-s13-decimal-first-transfer-extinction) now extinguishes the
entire first-transfer boundary from both centered resets. `DecimalSetterCarry` proves the two
successive-pole identities, simultaneous shell balances, incompatible ordinary-reset singleton
depths, exact `5/7` suffix exhaustion, and the strict prefix intervals separating every false
target. The finite Neary prefix trichotomy joining those declarations remains audited rather
than a single end-to-end Lean theorem. Arbitrary depth begins only after two completed transfers.

Record [`MM-S14`](SALVAGE.md#mm-s14-ordinary-depth-two-shell-forest) classifies every ordinary
depth-two target-shell pair. `DecimalSetterCarry.twoTransferTrace_identity` eliminates the
intermediate denominator, while `twoTransferTrace_shell_of_nonresonant` and
`ordinaryTwo_shellBalance` compare its joint `2`/`5` shell with the prospective target. The
result leaves only the two-role A/A resonance, the all-`c` A/B resonances of lengths `β+1` and
`β+2`, and the all-`c` length-`β` block followed by `D_b` in B/A; B/B is impossible. These gates
do not yet decide the surviving phase words or the distinguished-reset suffix corridor.

Record [`MM-S15`](SALVAGE.md#mm-s15-ordinary-a-to-a-length-two-extinction) closes the first
resonant family. `DecimalSetterChamber.encodedJUpper_in_window`, `lowShell_pole_below`, and
`highShell_pole_above` separate every target pole into two exact rational chambers.
`doubleDeletion_step_in_gap` puts the `D_cD_c` image strictly between them. For `R_cD_c`,
`compiler_ruleDeletionLowerWord_shape` derives the emitted lower prefix and length;
`ruleDeletion_cLeading_avoids_positivePole` and `ruleDeletion_bLeading_avoids_positivePole`
put the two source-prefix images outside `(0,1)`. Together with the shell gate, these
declarations extinguish the ordinary A-to-A depth-two branch. They do not decide A-to-B,
B-to-A, or the distinguished-reset normalized suffix.

Record [`MM-S16`](SALVAGE.md#mm-s16-complete-ordinary-depth-two-extinction) closes both remaining
ordinary families. `DecimalSetterResonance.allC_cLeading_avoids_singletonPole` and
`allC_bLeading_avoids_singletonPole` exhaust every phase word in the two long A/B shells by an
all-deletion/first-rule split. `encodedSingleB_after_repeatedC_avoids_encodedPole` proves the
exact B/A image is above one, while every positive target pole is below one.
`compilerBody_resonanceEnvelope` discharges the body hypotheses for every Neary compiler
instance. Thus no ordinary-reset false pole exists through two completed transfers; the
distinguished-reset suffix corridor remains open.

Record [`MM-S17`](SALVAGE.md#mm-s17-recursive-decimal-carrier) gives the surviving A-shell
corridor an all-depth normal form. `DecimalSetterDepth.peeledNumerator_multi_shell` proves that
`R=NT−10μGVD` has exact shell `(m−1,m−1)` before a multi-role pole, and
`peeledStep_factor` turns its quotient into the next carrier `(N',EN)`.
`depthTwo_suffix_to_peeled` connects this recurrence to the distinguished-reset suffix peel.
`peeledHead_trichotomy` and `bTag_cannot_head_equalDepth` exclude the initial leading-`b`
head. `peeledNumerator_forces_lastDigit` and `peeledLastDigit_twoStep` prove that the
generalized carrier's unit residues form a compatible period-two cycle. Record
[`MM-S18`](SALVAGE.md#mm-s18-length-two-carrier-extinction) removes the former exceptional
transition: `peeledNumerator_twoAdic_deepens` proves that the difference of the two normalized
`2`-adic units cannot remain a unit, and `peeledMultiPole_three_le_length` therefore forces
every non-singleton consecutive multi-pole block to have upper length at least three. The module
does not identify later product residuals with raw encoded heads or decide singleton targets.

The dimension-two affine ledger has twenty-eight independently checked records:

| Record | Formalization obligation |
| --- | --- |
| [`D2-S02`](SALVAGE.md#d2-s02-monotone-affine-path-form) | affine conjugacy, elementary case split, operational word normal form, and recovery of block lengths |
| [`D2-S04`](SALVAGE.md#d2-s04-real-trap-ternary-predecessor-nucleus) | computable maximal predecessor wait, sharp three-wait real-trap window, and exact fixed-source one-step reduction |
| [`D2-S05`](SALVAGE.md#d2-s05-fixed-source-real-trap-rays) | exact source trisection, normalized mantissa rays, target-depth offsets, and one-candidate fixed-source membership |
| [`D2-S06`](SALVAGE.md#d2-s06-spectator-prime-denominator-skeleton) | preservation of every prime-to-30 denominator exponent through arbitrary shell schedules and first exits |
| [`D2-S07`](SALVAGE.md#d2-s07-period-ten-shell-guard) | exact period-ten acceptance, the tail-dependent period `2·5^(ℓ+1)`, finite residue reduction, sharpness by unit zero preimages, and failure of every fixed wait modulus |
| [`D2-S08`](SALVAGE.md#d2-s08-twelve-class-target-depth-collapse) | exact target/wait shift conjugacy, equality of every deep nonempty predecessor set, depth-periodic unitality, and guarded reduction to twelve canonical target-depth classes |
| [`D2-S09`](SALVAGE.md#d2-s09-centered-lower-mantissa-recurrence) | complete three-branch reverse address, centered lower numerator, exact gcd cancellation and valuation transition, isolation of the sole secondary wall, and an infinite guarded fixed family with unbounded centered cancellation |
| [`D2-S10`](SALVAGE.md#d2-s10-finite-secondary-wall-nucleus) | exact wall cancellation, computable return depth, bounded three-power denominator loss, target-dependent finite successor rectangle, functional transition, eventual periodicity, fixed-component recognition, and twelve-class depth product |
| [`D2-S11`](SALVAGE.md#d2-s11-absorbing-four-divisible-cone) | exact upper and middle normalized coordinates, exact two-adic updates in the four-divisible stratum, branchwise denominator absorption, and the lower-wall three-stratum exit classifier |
| [`D2-S12`](SALVAGE.md#d2-s12-exact-wall-odd-two-cycle-family) | sharp admissible depth range, reduced wall and odd coordinates, exact guarded two-step return, uniqueness at fixed depth pair, strict infinitude, and accumulation at the wall boundary `9/10` |
| [`D2-S14`](SALVAGE.md#d2-s14-arbitrary-body-wall-excursion-saturation) | periodic-point real-trap localization, arbitrary-body wall anchoring, exact two-/five-adic guards, factor universality, and the finite forbidden-factor no-go |
| [`D2-S15`](SALVAGE.md#d2-s15-fixed-endpoint-centralizer-reduction) | two-adic slope value, exact length/sum slope classification, fixed-point uniqueness, periodic-point equality iff global commutation, and the equal-/unequal-slope fibre split |
| [`D2-S16`](SALVAGE.md#d2-s16-periodic-centralizer-determinant-fork) | schedule-power periodicity, guarded bipowers, the dependent-vector global power relation, and the independent-vector injective `ℕ²` loop family |
| [`D2-S17`](SALVAGE.md#d2-s17-fixed-endpoint-fibre-dichotomy) | equal-grade point-collision rigidity and the exact balanced-kernel/unequal-slope collision-source decomposition of every fixed endpoint fibre pair |
| [`D2-S18`](SALVAGE.md#d2-s18-same-length-cross-grade-five-carry) | parity/LTE valuation of every shell-ratio and equal-length slope gap, plus the exact five-unit collision-source criterion for unequal total waits |
| [`D2-S19`](SALVAGE.md#d2-s19-same-length-collision-acceptance-certificate) | the exact affine-determinant valuation criterion for a five-unit common target and, equivalently, every prefix guard on both sides of a same-length cross-grade collision |
| [`D2-S20`](SALVAGE.md#d2-s20-positive-endpoint-suffix-antichain) | the cleared fixed-source equation, gain and offset antitonicity in reverse cumulative waits, strict positive-source endpoint order, and the two-sided suffix-crossing condition for every collision |
| [`D2-D05`](SALVAGE.md#d2-d05-prescribed-translation-count) | primitive linear-polynomial divisibility, bounded carries in both scan directions, ordered-marker automaton, regular control, and `a=±1` cases |
| [`D2-D06`](SALVAGE.md#d2-d06-private-prime-peeling) | unique-minimum valuation calculation, zero endpoints, fixed-count reduction, reversed language, and positive private valuation |
| [`D2-D07`](SALVAGE.md#d2-d07-bounded-valuation-orthants) | localization support, denominator bounds in both orthants, invariant-interval recognition, finite graph, and regular-control product |
| [`D2-D10`](SALVAGE.md#d2-d10-real-trap-exterior) | invariant real trap, extremal zero-wait envelopes on both exterior components, explicit computable schedule-length bounds, and fixed-count reduction |
| [`D2-M01`](SALVAGE.md#d2-m01-benchmark-critical-shell) | benchmark conjugacies, endpoint-shell translation, guarded `5`-adic transition, parity guard, and no-return-after-exit theorem |
| [`D2-O02`](SALVAGE.md#d2-o02-critical-shell-periodic-saturation) | complete: rational periodic cycles for every nonempty finite wait schedule, raw/shell conjugacy, contextual boundary factorization, an infinite odd-length raw kernel family with guarded contextual cycles, exact persistence under unit normalization, a two-seed cancellative pump, and three independent length-30 relations; audited strengthening: terminating but nonconfluent critical-pair census, bounded five-rule kernel completeness through length 30 and six unexplained classes at 31 after adjoining the family member, infinite completion, finite-precision completeness, rational aperiodic addresses, density, and period-one single-wait transition rigidity |
| [`D2-O03`](SALVAGE.md#d2-o03-fixed-source-adjacent-saturation) | accepted fixed-source adjacent collision family, target injectivity, complementary target pole, and sole-candidate ray membership |
| [`D2-O04`](SALVAGE.md#d2-o04-forced-exit-surface) | exact forced-exit valuation, post-exit valuation descent and target-derived tail length, two-adic surface coordinates, injectivity, two-candidate surface membership, and fixed-count regular-control reduction of the full continuation cone |
| [`D2-O07`](SALVAGE.md#d2-o07-universal-exit-suffix-collapse) | exhaustive valuation classification of every critical-shell exit and the two-candidate fixed-target length reduction for every nonempty suffix |
| [`D2-O08`](SALVAGE.md#d2-o08-real-trap-backward-saturation) | exact rational predecessor cover of the half-open real trap, preservation of `5`-adic units in reverse, and guarded predecessor schedules of every prescribed block length |
| [`D2-O09`](SALVAGE.md#d2-o09-guarded-real-pole-reset) | exact normalized band coordinates, full deepest-branch depth reset, an unbounded period-fifty reset family preserving the real and `5`-adic guards, its fixed-source feeder, two-/three-adic profile, and target injectivity |

The shell record does not decide the benchmark. Every fixed exit has a decidable suffix and every
real-exterior target has a computable length bound, but an arbitrary critical prefix inside
`[1/5,1/2]` can produce infinitely many exits. A formal benchmark theorem must represent that
union effectively rather than hide it behind pointwise decidability. The audit is
[`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md);
the periodic saturation theorem and its remaining arithmetic boundary are reconstructed in
[`audits/m32-gpi2-residue-blindness-2026-08-30.md`](audits/m32-gpi2-residue-blindness-2026-08-30.md);
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

The positive overlap-queue compiler [`M4-C02`](SALVAGE.md#m4-c02-positive-overlap-queue-compiler)
is formalized in
[`MatrixMortality/OverlapQueue.lean`](MatrixMortality/OverlapQueue.lean). A binary two-state
queue consumes its open head and appends a role-dependent word. Four positive frame-cocycle
identities, empty-state isolation, and avoidance of one framed return suffice for an exact
equivalence between acceptance and mortality of three integer `4 × 4` matrices. The proof
quantifies over every positive physical word: `OverlapQueue.causality` forces an arbitrary
coefficient equality to be a genuine trace or to contain an earlier empty prefix. The same file
formalizes the source obstruction [`M4-O11`](SALVAGE.md#m4-o11-pure-deletion-necessity): every
accepted initial queue of length greater than one has a state-preserving role whose production
and cancellation words are both empty. The audit is
[`audits/m43-overlap-queue-2026-08-08.md`](audits/m43-overlap-queue-2026-08-08.md).

The zero-framed binary Lag specialization
[`M4-C03`](SALVAGE.md#m4-c03-zero-framed-binary-two-lag-compiler) is formalized in
[`MatrixMortality/OverlapLag.lean`](MatrixMortality/OverlapLag.lean). Lean identifies the
scanner step with literal context-2 Lag deletion, proves both directions of chronological trace
translation, translates empty-state isolation to singleton isolation and the framed-return
promise to avoidance of `10ⁿ⁺¹`, and composes the exact kernel to three integer `4 × 4`
matrices. The same module formalizes
[`M4-O12`](SALVAGE.md#m4-o12-terminal-frame-morphism-obstruction), the length contradiction
which kills direct terminal-to-frame morphic coding. The larger three-scanner classification
[`M4-S05`](SALVAGE.md#m4-s05-deletion-scanner-normal-form) is independently audited rather
than Lean-formalized. Its evidence boundary is recorded in
[`audits/m43-deletion-scanner-2026-08-08.md`](audits/m43-deletion-scanner-2026-08-08.md).

The Lag source itself is now closed by
[`M4-D01`](SALVAGE.md#m4-d01-zero-framed-binary-two-lag-decision), formalized in
[`MatrixMortality/OverlapLagDecision.lean`](MatrixMortality/OverlapLagDecision.lean). For every
positive `n` and arbitrary `U,V,W`, Lean proves

```text
Accepts(n,U,V,W) ↔ (n=1 ∧ U=ε) ∨ (V=ε ∧ U∈0*).
```

This classification is unconditional and yields a decision procedure without orbit simulation.
Under the existing compiler promises it also classifies mortality of the associated three
integer `4 × 4` matrices. The audit is
[`audits/m43-overlap-lag-decision-2026-08-10.md`](audits/m43-overlap-lag-decision-2026-08-10.md).

The reset scanner is independently decided, but remains outside the Lean ledger.
[`M4-D02`](SALVAGE.md#m4-d02-zero-framed-reset-scanner-decision) contracts complete rule
boundaries by zero-run reduction to a two-token quotient. Its accepting set is a direct equality
when `W` contains `1` and the regular language `(101|11)*10` when `W∈0*`. No auxiliary scanner
code was retained because the result deletes its own attack lane. The exact evidence boundary is
[`audits/m43-reset-scanner-decision-2026-08-10.md`](audits/m43-reset-scanner-decision-2026-08-10.md).

The periodic-conjugate scanner is likewise decided outside the Lean ledger.
[`M4-D03`](SALVAGE.md#m4-d03-periodic-conjugate-scanner-decision) computes the initial return,
normalizes `AP=KA` into primitive conjugate powers, and reduces every remaining promised orbit
to at most `#₁(K)` odd-gap tests. Its prefix telescope was independently reconstructed against
self-consumed appendants and malformed queues. This closes the final consumer of the audited
scanner semantics, so no scanner-specific Lean layer is retained. The evidence and exact use of
the `(R,A)` avoidance promise are in
[`audits/m43-periodic-conjugate-decision-2026-08-10.md`](audits/m43-periodic-conjugate-decision-2026-08-10.md).

The odd-phase macro cut [`M4-S01`](SALVAGE.md#m4-s01-odd-phase-macro-cut) remains reported.
Lean already defines the relevant phase residues and Table 2 tracks, but no theorem yet proves
the even-track invariant through every reachable queue or the induced macro solvability
equivalence. The direct first-return obstruction [`M4-O05`](SALVAGE.md#m4-o05-direct-two-state-first-return-recoding)
also remains reported. Neither claim enters the checked theorem ledger.

The finite-order monomial blade [`M4-M02`](SALVAGE.md#m4-m02-universal-monomial-cube-root-blade)
is parked after the audited closed-residue obstruction
[`M4-O07`](SALVAGE.md#m4-o07-closed-residue-monomial-obstruction). Its live replacement
[`M4-M03`](SALVAGE.md#m4-m03-parabolic-blade-and-bridge-grammar) is formalized in
[`MatrixMortality/ParabolicBlade.lean`](MatrixMortality/ParabolicBlade.lean). Lean checks the
open cube root's toggle action and invertibility, the nonzero rank-one physical blade, all six
infinite gap determinant pencils, the unique singular rank-two atom, every one-step instance of
the annihilator guard [`M4-O06`](SALVAGE.md#m4-o06-punctuation-image-annihilator), and nonzero
products through two singular incidences. It also proves the stronger all-length contraction:
an exceptional chain vanishes exactly when its induced `2 × 2` bridge word vanishes. The audit
and exact promotion boundary are
[`audits/m43-parabolic-blade-2026-08-05.md`](audits/m43-parabolic-blade-2026-08-05.md).

The residue-two obstruction [`M4-O08`](SALVAGE.md#m4-o08-residue-two-necessary-wall) is
formalized in
[`MatrixMortality/ParabolicResidueWall.lean`](MatrixMortality/ParabolicResidueWall.lean). After
one integral scaling and reduction modulo three, every residue-zero and residue-one atom acts on
two protected rays with nonzero weight. Lean therefore proves
`ParabolicBlade.residueTwoWall_wordProduct_ne_zero`: for every `β`, body, and word over
`Q(x,3j)` and `Q(x,3j+1)`, the product is nonzero. This subsumes and deletes the former
closed-phase theorem. The audit is
[`audits/m43-residue-two-wall-2026-08-05.md`](audits/m43-residue-two-wall-2026-08-05.md).

The residue-zero cone [`M4-S02`](SALVAGE.md#m4-s02-residue-zero-safe-bridge-cone) is audited
against the same transition formulas. It proves strict cone preservation and negative
determinant for every nonempty regular residue-zero bridge; the unformalized boundary is
arbitrary residue-one alternation, not the residue-zero compression.

The one-defect phase cut [`M4-S03`](SALVAGE.md#m4-s03-one-defect-phase-cut) is formalized in the
same module. `ParabolicBlade.oneDefect_wordProduct_ne_zero_of_same_residue` proves that arbitrary
safe contexts around one residue-two atom cannot vanish when their adjacent residues agree.
Together with safe-word nonvanishing and residue-two atom invertibility, only adjacency phases
`0|2|1` and `1|2|0` remain. The audit is
[`audits/m43-one-defect-phase-2026-08-07.md`](audits/m43-one-defect-phase-2026-08-07.md).

The arbitrary-switching exterior flag
[`M4-S04`](SALVAGE.md#m4-s04-arbitrary-switching-three-adic-exterior-flag) is formalized across
[`MatrixMortality/ParabolicExterior.lean`](MatrixMortality/ParabolicExterior.lean),
[`MatrixMortality/ParabolicFlag.lean`](MatrixMortality/ParabolicFlag.lean), and
[`MatrixMortality/ParabolicSafeFlag.lean`](MatrixMortality/ParabolicSafeFlag.lean). Lean checks
the complete adjugate exterior state, its exact left-multiplication law, and the bridge identity
making its first coordinate the singular wall. Every regular safe atom sends the two-sector
`3`-adic flag into the sector selected by its residue, even under arbitrary switching and
unbounded common-power cancellation. On the wall, the leftmost residue forces a strict
orientation of the other coordinates. This does not prove safe return because both sectors meet
the wall. The first exact wound is also checked: a regular residue-one `b` atom returns precisely
when `(12·3^β−1)(u+w)+2v=0`. The audit is
[`audits/m43-parabolic-flag-2026-08-08.md`](audits/m43-parabolic-flag-2026-08-08.md).

The arbitrary defect grammar
[`M4-S06`](SALVAGE.md#m4-s06-arbitrary-defect-bridge-grammar) is formalized in
[`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean). Lean proves
`A₂⁴=2I` for the protected-plane defect action and the complete four-periodic local-incidence
table. It factors every arbitrary cleared `3 × 3` residue skeleton into those incidences and
composes the result with the concrete integral numerators: every physical skeleton without a bad
internal run is nonzero over `ℚ`. This subsumes the one-defect phase cut `M4-S03`.

The same module proves the exact pure-defect reset: every nonempty block of residue-two atoms has
an invertible bridge. Every regular wall bridge is a nonzero rank-one outer product, and an
arbitrary chain of varying walls separated by arbitrary transports vanishes exactly at one
consecutive projective incidence. For wall exterior state `(0,v,w)`, the explicit cokernel is
`(v,-4w)`; it is nonzero on every regular wall word and annihilates the bridge. The exact checks
and evidence boundary are in
[`audits/m43-arbitrary-defect-2026-08-08.md`](audits/m43-arbitrary-defect-2026-08-08.md).

The one-sided wall-orbit normal form
[`M4-S07`](SALVAGE.md#m4-s07-one-sided-wall-orbit-normal-form) has a formal kernel spine in
[`MatrixMortality/ParabolicIncidence.lean`](MatrixMortality/ParabolicIncidence.lean). Lean
defines the canonical right kernel `coreLeftInverse ρ *ᵥ (adj(M) *ᵥ bladeKernel)`, proves that
the exceptional output factor maps it back to `adj(M) *ᵥ bladeKernel` on the wall, proves that
the bridge annihilates it, and proves nonvanishing for every regular wall word. The final
two-wall identity and its one-sided exterior target are independently audited rather than
claimed as formalized. The evidence boundary is
[`audits/m43-one-sided-wall-orbit-2026-08-11.md`](audits/m43-one-sided-wall-orbit-2026-08-11.md).

The safe-wall transport chamber
[`M4-S08`](SALVAGE.md#m4-s08-safe-wall-transport-chamber) is formalized in the same module.
`ParabolicBlade.safeWall_incidence_orients_transport` composes the checked wall orientation and
cokernel formula: a zero incidence with a nonempty safe right wall forces the nonzero transported
kernel into the strict valuation chamber selected by the wall's leftmost residue. The proof
handles a zero higher coordinate explicitly and otherwise transfers the strict inequality across
`v a=4 w b`, using that four is a `3`-adic unit.
`ParabolicBlade.safeWall_rejects_balanced_transport` then excludes every transported kernel with
two nonzero coordinates of equal `3`-adic valuation. The exact evidence boundary is
[`audits/m43-safe-wall-transport-2026-08-30.md`](audits/m43-safe-wall-transport-2026-08-30.md).

The uniform all-`b` defect-run exclusion
[`M4-S14`](SALVAGE.md#m4-s14-uniform-all-b-defect-run-exclusion) is formalized in
[`MatrixMortality/ParabolicLongDefect.lean`](MatrixMortality/ParabolicLongDefect.lean).
`ParabolicBlade.bDefectRun` is the physical product of an arbitrary wait list of residue-two
`b` atoms. `ParabolicBlade.bridge_bSafe_bDefectRun_bSafe_det_ne_zero` proves that every such run
between regular safe `b` endpoints has nonzero bridge determinant at `β=3`, without a parity or
nonemptiness hypothesis. Its invariant-cone proof tracks the exact `(−1)^length` exterior sign
and retains `b(1)` as the sole forbidden endpoint. This subsumes the one-defect formulas of
[`M4-S09`](SALVAGE.md#m4-s09-minimal-all-b-bad-run-exclusion) and replaces the deleted explicit
three-defect coefficient cores. The exact boundary is
[`audits/m43-uniform-all-b-defect-run-2026-08-30.md`](audits/m43-uniform-all-b-defect-run-2026-08-30.md).

The opposite double-`c` endpoint exclusion
[`M4-S15`](SALVAGE.md#m4-s15-opposite-double-c-endpoint-exclusion) is formalized in
[`MatrixMortality/ParabolicMixedEndpoint.lean`](MatrixMortality/ParabolicMixedEndpoint.lean).
`ParabolicBlade.bridge_cOne_bTwo_cZero_det` collects the exact determinant of
`c(3z+1)b(3x+2)c(3y)` into eight wait monomials in the native scale gap and code discrepancy.
`ParabolicBlade.bridge_cOne_bTwo_cZero_det_ne_zero` proves every coefficient positive from the
exact nonempty-code interval, including the sole quadratic `q²` coefficient competition. The
exact boundary is
[`audits/m43-opposite-double-c-endpoint-2026-08-30.md`](audits/m43-opposite-double-c-endpoint-2026-08-30.md).

The phase-zero `c`-defect exclusion
[`M4-S10`](SALVAGE.md#m4-s10-phase-zero-c-defect-exclusion) is checked in the same module.
`ParabolicBlade.bridge_bZero_cTwo_bOne_det` computes the exact width-three determinant for
`b(3z)c(3x+2)b(3y+1)`. Its nonzero corollary proves all four wait-monomial coefficients positive
from the native code bounds for every nonempty body. The same module compresses the opposite
phase to one affine wait incidence and proves the uniform endpoint-coefficient difference that
fixes its root-interval width. See
[`audits/m43-phase-zero-c-defect-2026-08-30.md`](audits/m43-phase-zero-c-defect-2026-08-30.md).

The opposite `c`-defect cylinder exclusion
[`M4-S11`](SALVAGE.md#m4-s11-opposite-c-defect-cylinder-exclusion) is formalized in
[`MatrixMortality/ParabolicDefectCylinder.lean`](MatrixMortality/ParabolicDefectCylinder.lean).
`ParabolicBlade.bridge_bOne_cTwo_bZero_det_ne_zero` partitions every nonempty body into an all-`c`
word or a leading `c`-run followed by `b`, derives the exact ternary-code interval in each case,
and excludes every natural root of the compressed determinant. The two cylinders which meet one
integer force the remaining wait below one and then contradict their strict endpoint bounds. The
exact boundary is
[`audits/m43-opposite-c-defect-cylinder-2026-08-30.md`](audits/m43-opposite-c-defect-cylinder-2026-08-30.md).

The residue-zero `c`-endpoint exclusion
[`M4-S12`](SALVAGE.md#m4-s12-residue-zero-c-endpoint-exclusion) is checked in the same module.
`ParabolicBlade.bridge_cZero_bTwo_bOne_det` and
`ParabolicBlade.bridge_bOne_bTwo_cZero_det` compute the two exact width-three determinants with a
`b` defect and a body-dependent `c` atom at the residue-zero safe endpoint. Their nonzero
corollaries derive positivity of all remaining coefficients from the native nonempty-code
interval. The exact boundary is
[`audits/m43-residue-zero-c-endpoints-2026-08-30.md`](audits/m43-residue-zero-c-endpoints-2026-08-30.md).

The residue-one left `c`-endpoint exclusion
[`M4-S13`](SALVAGE.md#m4-s13-residue-one-left-c-endpoint-exclusion) is also checked there.
`ParabolicBlade.bridge_cOne_bTwo_bZero_det` collects the exact determinant of
`c(3z+1)b(3x+2)b(3y)` into eight wait monomials.
`ParabolicBlade.bridge_cOne_bTwo_bZero_det_ne_zero` proves every coefficient positive from the
coarse native code interval. The exact boundary is
[`audits/m43-residue-one-left-c-endpoint-2026-08-30.md`](audits/m43-residue-one-left-c-endpoint-2026-08-30.md).

The original fixed-ray semantic route is obstructed by
[`M4-O14`](SALVAGE.md#m4-o14-original-semantic-endpoint-obstruction), formalized in
[`MatrixMortality/ParabolicSemanticObstruction.lean`](MatrixMortality/ParabolicSemanticObstruction.lean).
Lean identifies the complete ternary correspondence middle as a fixed conjugate of
`sidePcpMatrix`, proves that every original complete gap evaluates to it, composes arbitrary
complete tile words, and computes their exceptional bridge determinant. The determinant is
strictly negative for every nonempty complete Neary word, so such a word cannot be a wall. For
arbitrary fixed endpoint rays, vanishing on the correct formal terminal plane `Y=tX+m, τ=tσ`
forces vanishing on the entire compulsory length plane. The proof does not classify coincidences
confined to the discrete code locus.

The same module formalizes the conditional identity
[`M4-C04`](SALVAGE.md#m4-c04-original-mixed-gap-endpoint-compiler). Two explicit endpoint ray
equations make one semantic bridge followed by the empty bridge vanish exactly on the
four-parameter Neary terminal equation. Complete semantic contexts cannot reach either ray, so
both endpoint words must contain incomplete gaps. The exact evidence boundary is
[`audits/m43-original-semantic-obstruction-2026-08-10.md`](audits/m43-original-semantic-obstruction-2026-08-10.md).

The retuned semantic boundary
[`M4-M04`](SALVAGE.md#m4-m04-retuned-semantic-boundary) is formalized in
[`MatrixMortality/ParabolicRetuned.lean`](MatrixMortality/ParabolicRetuned.lean) and
[`MatrixMortality/ParabolicRetunedBoundary.lean`](MatrixMortality/ParabolicRetunedBoundary.lean).
Lean proves the fixed root cube, all six reduced-atom determinant pencils, and uniqueness of the
gap-two `b` singularity under the source hypotheses. A sparse ternary side normal form evaluates
every complete Neary word without reversal. Its exceptional bridge determinant vanishes exactly
on the terminal equation and, after paired decoding, exactly on `pairedCoefficient = 0`.

The bridge is realized by a literal word over the root and two data generators. A fixed physical
minor is `-2052·3^β` times its determinant; explicit retractions recover the bridge and prove the
context never vanishes. On a terminal match the context is a nonzero outer product with fixed
right row `(-1,(15·3^β+3)/2,28,24)`, and right multiplication kills the context exactly when it
kills this row. Every complete-gap continuation preserves the row's first coordinate, so any
annihilator must use an incomplete root gap. The audit is
[`audits/m43-retuned-semantic-boundary-2026-08-08.md`](audits/m43-retuned-semantic-boundary-2026-08-08.md).

The fixed-row closure is refuted by
[`M4-O13`](SALVAGE.md#m4-o13-retuned-pseudo-terminal-obstruction), formalized in
[`MatrixMortality/ParabolicRetunedObstruction.lean`](MatrixMortality/ParabolicRetunedObstruction.lean).
For the admissible nonhalting source `(β,body)=(3,bbcc)`, Lean proves that a literal length-100
word with one gap-thirty pseudo-production is a nonzero outer product with terminal row
`(-1,204,28,24)`. Appending an arbitrary physical word gives zero exactly when that word
annihilates the row. The same module proves the legal tag orbit cycles and hence has no genuine
terminal match. The exact evidence boundary is
[`audits/m43-retuned-pseudo-terminal-obstruction-2026-08-10.md`](audits/m43-retuned-pseudo-terminal-obstruction-2026-08-10.md).

The same gap-thirty pseudo-production refutes the original conditional endpoint architecture.
[`M4-O15`](SALVAGE.md#m4-o15-original-pseudo-terminal-endpoint-obstruction) evaluates the
malformed atom and the complete poison word in the original side-normal semantics. Lean proves
that the admissible source `(β,body)=(3,bbcc)` has no terminal word, while every instantiation
of the `M4-C04` endpoint hypotheses kills a regular 33-tile middle containing `(b,30)`. Thus
endpoint failure destroys completeness and endpoint success destroys soundness.

The orthogonal free-group punctuation mechanism
[`M4-M05`](SALVAGE.md#m4-m05-boundary-guarded-homogeneous-punctuation) has two formal layers.
[`MatrixMortality/SchottkyPunctuation.lean`](MatrixMortality/SchottkyPunctuation.lean) defines
the four-dimensional left--right action `B.adjugateᵀ⊗A`, proves its multiplication law and
unimodularity, and computes its fixed row--column coefficient as the determinant of the first
columns of `A` and `B`. The explicit Schottky ping-pong argument making this coefficient an
equality detector is audited rather than Lean-checked.

[`MatrixMortality/TerminalTile.lean`](MatrixMortality/TerminalTile.lean) now proves the generic
boundary-fold theorem `unitFamily_mortal_boundaryOuter_iff`. For any unit data family, fixed
left and right data words are absorbed into the two rays of one rank-one separator; mortality is
equivalent to a zero scalar on one bounded interior word, with a converse over every placement
and number of separators. No source compiler from Carvalho's four-letter marker-tail equation to
positive binary fixed-boundary equality is claimed.

No `M₄(3)` undecidability theorem follows from the present corpus. The exhaustive promised
positive overlap-queue source class, the retuned fixed-row closure, the original fixed-ray
formal-plane compiler, and the four-parameter `M4-C04` endpoint architecture are closed. The
original matrix lane retains exterior collision avoidance and syntax-sensitive semantics. The
free-cancellation lane retains the positive binary fixed-boundary compiler and its opposing
fixed-rank decision problem.

## Modules

| File | Responsibility |
| --- | --- |
| `Computability.lean` | primitive-recursive closure lemmas used by the explicit compilers |
| `WordMorphism.lean` | free-monoid morphism laws and consecutive-repeat closure of fixed-boundary equations |
| `FinitePositiveImage.lean` | inverse closure of submonoids in finite groups and collapse of positive closure to group closure |
| `MatrixSemigroup.lean` | shared word semantics, mortality transports, common-image restriction, transposition, and zero padding |
| `LinearRepresentation.lean` | finite Hankel sections and exact-realization state lower bounds |
| `BoundaryTax.lean` | generic finite-witness two-channel boundary tax |
| `ReturnFamily.lean` | split finite-rank return normal form and matrix-valued block-Hankel witnesses |
| `CubicReturn.lean` | pure-cubic arbitrary-word collapse and automatic genericity of the one-singular normal form |
| `CubicReturnNonPure.lean` | non-pure physical endpoint alignment, fixed return recurrence, and exact unselected-wait obstruction |
| `EdgeCompression.lean` | exact adjacent-edge compression for split finite-rank families |
| `TwoPlaneEdges.lean` | compatible two-plane realization of a `2 × 2` edge square and exact rank-two certificates |
| `ReverseEdge.lean` | generic projective-incidence reverse compiler, basis adaptation, and all-path converse |
| `ProjectiveIncidence.lean` | exceptional-source geometry and all-word unit normalization for projective incidence |
| `ProjectiveCollatz.lean` | exact shortcut-Collatz predecessor language, 3-adic malformed-word guard, and normalized GPI₂ reduction |
| `RankTwoPunctuation.lean` | intrinsic generic-incidence reduction of the unique hard one-loop edge stratum |
| `PolynomialPencil.lean` | coefficient support and exact evaluation of words over affine matrix pencils |
| `PrimitiveDivisor.lean` | cyclotomic support, nonprimitive index-prime valuations, and Bang–Zsigmondy above exponent two |
| `ReturnSquare.lean` | exact rank-`(3,2)` laboratory, bridge normal form, and two-return square cage |
| `ReturnSquareDynamics.lean` | homogeneous projective trap and outer negative immortality wall |
| `ReturnSquarePrimePower.lean` | bridge-polynomial root support and finite quotient walls |
| `ReturnSquareClassification.lean` | complete prime-power ReturnSquare parameter classification |
| `ReturnSquareTax.lean` | exact four-state lower bound for literal reversible-stack returns |
| `ReturnSquareNoGo.lean` | quadratic-pencil reversible-squaring obstruction and blind-scaling collapse |
| `ReturnJordan.lean` | parity-Jordan rail rigidity and modular immortality certificate |
| `ReturnConvert.lean` | minimal two-scale return pencil and nonresonant multi-return zero |
| `ProjectiveLine.lean` | total affine-chart presentation of `ℙ¹` and exact unit-word ray action |
| `CongruenceBlindOrbit.lean` | free rational shear orbit, trivial source stabilizer, explicit five-factor bridge, and end-to-end all-modulus CRT closure |
| `PadicValuation.lean` | nonzero rational p-adic shells, unequal-valuation calculus, and the adjacent-unit odd-prime obstruction |
| `PeriodicShell.lean` | exact affine schedule composition, rational all-unit periodic cycles, and the published nonfree benchmark relation |
| `MixedPrimeDebt.lean` | exact wait walls, debt recurrence and predecessor fans, cross-length collision arithmetic, the accepted fixed-source ray, and its forced-exit surface |
| `MixedPrimeDebtBoundary.lean` | same-length collision rigidity and exact saturation of the remaining three-adic carrier orientation |
| `MixedPrimeExit.lean` | universal critical-shell exit classification, two-candidate post-exit length reduction, and translated-letter count for the full fixed-source continuation cone |
| `MixedPrimeRealTrap.lean` | invariant real trap, exterior contraction bounds, guarded backward saturation, and the sharp ternary predecessor nucleus |
| `MixedPrimeRealTrapReset.lean` | full normalized pole branch, its unbounded period-fifty guarded depth-reset family, fixed-source feeder, exact two-/three-adic profile, and target injectivity |
| `MixedPrimeRealTrapAddress.lean` | exact fixed-source trisection into three normalized-mantissa rays and one-candidate membership |
| `MixedPrimeSpectator.lean` | invariant spectator-prime denominator skeleton for every shell prefix and first exit |
| `MixedPrimeFiveCarry.lean` | exact one-step and tail-dependent shell-guard periods, finite residue classifiers, and sharp precision loss through unit zero preimages |
| `MixedPrimeRealTrapDepth.lean` | exact deep target/wait shift, nonempty predecessor-set collapse, and twelve-class guarded target-depth normalization |
| `MixedPrimeRealTrapMantissa.lean` | complete reverse mantissa address, centered lower-branch gcd, exact two-/three-adic cancellation recurrence, and guarded secondary-wall fixed points at every depth at least seven |
| `MixedPrimeRealTrapWall.lean` | finite reduced unit secondary-wall graph, bounded three-adic denominator loss, eventual periodicity, fixed-component recognition, and canonical depth labels |
| `MixedPrimeRealTrapExcursion.lean` | exact upper and middle normalized coordinates, absorbing four-divisible denominator cone, and the complete lower-wall two-adic exit trichotomy |
| `MixedPrimeRealTrapReturn.lean` | exact wall-to-odd two-cycle family, primitive reduced coordinates, guarded return waits, depth-pair uniqueness, strict infinitude, and boundary accumulation |
| `MixedPrimeRealTrapSaturation.lean` | arbitrary finite excursion embedding, wall-anchored periodic certificates, exact valuation guards, and factor-universal schedule language |
| `MixedPrimeRealTrapCentralizer.lean` | fixed-endpoint periodic-point centralizer equivalence and exact slope-kernel/collision-source fibre split |
| `MixedPrimeKernel.lean` | raw mixed-prime affine action, contextual composition, an infinite odd-length kernel family from length 29, and three independent length-30 relations |
| `MixedPrimeNormalization.lean` | exact homogeneous odd-family relations, persistence under independent normalization scaling, and the two-seed cancellative pump |
| `ReturnGuard.lean` | three-mode amalgamated return algebra, split mortality compiler, and exact state lower bound |
| `ReturnGuardDynamics.lean` | permanent trap, ready-tail grammar, and deterministic physical mortality equivalence |
| `ReturnGuardShift.lean` | shifted prefix decoder and affine reciprocal-residual transport |
| `ReturnGuardGauss.lean` | canonical residual coordinate, exact branch spheres, and guarded-step conjugacy |
| `ReturnGuardAddress.lean` | finite inverse-address mortality grammar and branch fixed-point incompatibility |
| `ReturnGuardArithmetic.lean` | primitive-pair recurrence and cyclotomic reset-or-cancellation sieve |
| `ReturnGuardTerminalGate.lean` | squarefree reset witnesses, full primitive cyclotomic absorption, and terminal height gates |
| `ReturnGuardQuotient.lean` | exact-order finite projective automata, swallowed-factor semantics, and safe invariant certificates |
| `ReturnGuardIntegralLift.lean` | canonical rational pairs, decoded-to-integral execution lifting, and quotient certificates of physical immortality |
| `ReturnGuardQuotientCompleteness.lean` | zero-wait terminal kernel, cancellation-reachability completeness, and synchronized-product no-amplification |
| `ReturnGuardDriftCertificate.lean` | exact drift-divisor certificate classification, cyclic subgroup criterion, and executable finite test |
| `ReturnGuardCumulative.lean` | chronological product algebra, pre-final Casoratian localization, content-free cumulative endpoint execution, exact second-order recurrence, reset-ancestry pullback, primitive endpoint projectivization, odd-resultant immortality, and derived primitive content |
| `ReturnGuardContinued.lean` | exact moving-divisor allocation, fixed-cusp complete quotients, primitive prequotient and Jacobi-tail transport, recurrent-boundary reverse persistence, record-ascent content budget, and order-three decoder |
| `ReturnGuardBoundary.lean` | depth-two universal-boundary reset ball, valuation-wall immortality, and primewise reset-resultant necessity |
| `ReturnGuardSmith.lean` | signed content split, positive-cone primitive-height gain, nonmaximal contraction, maximal-step isolation, and diagonalized gauged cocycle |
| `ReturnGuardPeriodicity.lean` | exact denominator recurrence and explicit record-ascent, wait, content, and numerator ceilings |
| `ReturnGuardFiniteOrbit.lean` | bounded primitive endpoint streams, their finite state box, repetition, and eventual periodicity |
| `ReturnGuardFrame.lean` | evaluation-frame coboundary and reset-shell localization of transverse depth |
| `ReturnGuardGap.lean` | exact residual similarity, rational projective gaps, height envelopes, and fixed-macro pumping |
| `ReturnGuardPumping.lean` | arbitrary repeated-factor pumping between decoded orbit checkpoints |
| `ReturnGuardEndpoint.lean` | terminal-centered divisor recurrence, whole-word determinant factorization, complementary forward/reverse contents, and coefficient-prime obstructions |
| `ReturnGuardEndpointCompleteness.lean` | complete positive endpoint language, fixed distinguished-prime flag and reset kernel, and exact endpoint Smith weight |
| `ReturnGuardAdelic.lean` | content-weighted height bounds, strong primitive pressure, complete cyclotomic complement, and exact exterior-product conservation |
| `ReturnGuardResonance.lean` | nonresonant descent, resonance localization, and corrected nested readiness |
| `ReturnGuardRail.lean` | polynomial divisibility and rational affine-wait rail obstruction |
| `ReturnGuardExamples.lean` | mortal and periodic guards, endpoint boundary certificates, and ready order-breaking reset-ball ejection |
| `ReturnGuardCounterorbit.lean` | exact forced continuation and trap termination of the proposed order-breaking counterorbit |
| `ReturnGuardTransverseReservoir.lean` | exact primitive period-three contents and unbounded transverse reverse mass invisible to its fixed reset orbit |
| `ReturnGuardPeriodicShadow.lean` | fixed-reset periodic-shadow family, uniform all-corridor descent obstruction, and fixed-depth unbounded endpoint-height obstruction |
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
| `OverlapQueue.lean` | positive two-frame queue semantics, arbitrary-word causality, exact mortality compiler, and pure-deletion necessity |
| `OverlapLag.lean` | literal binary context-2 Lag kernel, promise translation, mortality composition, and terminal-frame morphism obstruction |
| `OverlapLagDecision.lean` | unconditional syntactic decision of the zero-framed binary context-2 Lag kernel |
| `IndexedExecution.lean` | exact finite relational execution and closure views |
| `TagQueue.lean` | tag steps, indexed execution specializations, and generic history soundness |
| `PrefixResidual.lean` | canonical oriented prefix residuals, generic tag-history paths, and completion semantics |
| `NearyEncoding.lean` | four ordinary tiles, synchronization, source equivalence, and composed reductions |
| `MarkedTerminal.lean` | fresh marker, primitive terminality, and binary recoding |
| `TernaryEncoding.lean` | injective nonzero ternary representation |
| `PCPEncoding.lean` | `3 × 3` word-pair morphism and equality entry |
| `TerminalTile.lean` | arbitrary rank-one chains, fracture at every separator, and fixed-boundary folding into separator rays |
| `SchottkyPunctuation.lean` | four-dimensional integral left--right action and homogeneous first-column incidence coefficient |
| `TerminalReduction.lean` | rational and integer fixed-boundary mortality compiler |
| `TerminalSource.lean` | generic primitive extraction and GPCP bridge |
| `PairedCompression.lean` | reset/toggle specialization, explicit coordinate certificates, and arbitrary-word decoding |
| `ParabolicBlade.lean` | open cube root, nonzero mixed blade, complete atom grammar, annihilator guards, and exact `2 × 2` exceptional-chain contraction |
| `ParabolicResidueWall.lean` | integral residue-{0,1} atom numerators, modulo-three two-ray action, and the necessity of residue two |
| `ParabolicExterior.lean` | complete adjugate exterior state, bridge-wall coordinate, and four normalized safe actions |
| `ParabolicFlag.lean` | valuation relations and the four arbitrary-cancellation atom invariants |
| `ParabolicSafeFlag.lean` | arbitrary safe-word flag, wall orientation, and exact residue-one `b` wound |
| `ParabolicDefect.lean` | complete defect-run residue grammar, exact minimal all-`b`, phase-zero `c`-defect, and three one-`c` endpoint exclusions, pure-defect bridge reset, and consecutive-wall projective fracture |
| `ParabolicSemanticObstruction.lean` | complete-block determinant wall and fixed-ray formal terminal-plane obstruction |
| `ParabolicIncidence.lean` | canonical nonzero right kernel of every regular wall bridge |
| `ParabolicRetuned.lean` | retuned open root, sparse ternary code, determinant pencils, and unique gap-two singular atom |
| `ParabolicRetunedBoundary.lean` | complete-gap semantics, literal physical contexts, fixed terminal minor and row, and complete-gap annihilator obstruction |
| `ParabolicRetunedObstruction.lean` | explicit malformed terminal no-instance defeating the retuned fixed-row and original endpoint closures |
| `SetterShear.lean` | boundary-calibrated side-basis shear, internal separator invariance, and transfer-tail gauge obstruction |
| `SetterJFraction.lean` | exact decimal coefficient boxes and the hyperbolic-block/elliptic-product obstruction |
| `DecimalSetterArithmetic.lean` | decimal setter centered carry, reciprocal recurrence, coupled `2`/`5` target shells, and successive-pole valuation balance |
| `DecimalSetterCarry.lean` | two-reset successive-pole identities, joint depth constraints, exact decimal suffix exhaustion, first-transfer prefix separation, and the ordinary depth-two A/B shell forest |
| `DecimalSetterChamber.lean` | exact decimal pole chambers, both ordinary A-to-A length-two extinctions, and the emitted-body grammar certificate |
| `DecimalSetterResonance.lean` | complete ordinary depth-two A-to-B and B-to-A extinction, phase-word exhaustion, and compiler-envelope specialization |
| `DecimalSetterDepth.lean` | recursive two-unit A-shell carrier, length-two extinction, initial raw-head exclusion, and the exact last-digit two-cycle obstruction |
| `PairedMortality.lean` | common-column mortality converse and exact integer `4 × 4` family |
| `PhaseFracture.lean` | phase normalization and dimension-free projective-identification contradiction |
| `PhaseRigidity.lean` | checked local role algebra, discrepancy commutators, and invariant-pencil rigidity |
| `HistoryFracture.lean` | null-history counterexample, minimum-body base-five encoder, and integral mortality lift |
| `TransverseHistory.lean` | injective mixed-radix history code, transverse rank-two controls, and exact minimum-body zero language |
| `BranchingHistory.lean` | fixed `bcbc` terminal forks and affine positional lower bounds |
| `AffineRecognizer.lean` | generic singular three-state guard-and-carry representation calculus |
| `BranchingRecognizer.lean` | complete `bcbc` residual grammar and rational three-state recognizer |
| `MixedBranchingHistory.lean` | equal-length mixed terminal grammar and exact raw-toggle normal form |
| `MixedBranchingRecognizer.lean` | complete inverse carry graph and integral three-state same-zero recognizer |
| `ExpandingHistoryNoGo.lean` | reset-affine orbit, finite reverse automaton, regularity, and universal computability obstruction |
| `CancellativeProjectiveNoGo.lean` | paired residual conic, finite support-rank closure, cancellative role fractions, and projective commutator rigidity |
| `PairedInverseChamber.lean` | one-turn residual chambers, protected formal inverse states, and positive forward-cone separation |
| `PositiveFreeCancellation.lean` | positive `F₂` cover, finite-fibre pumping, singular quotient absorption, and rank-six syntax wall |
| `DirectedCancellation.lean` | direct finiteness and value/zero-context obstructions to one-way cancellation absorption |
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
| `TernaryClosedBlockNoGo.lean` | paired-Parikh independence, exact erasing macro lower bound, block semantics, and closed-return arithmetic |
| `WordDiscrepancy.lean` | first-mismatch permanence and exact signed free-monoid residual dynamics |
| `PriorityAffineResidual.lean` | exact compilation of priority-affine guards into nested-zero-test counter macros |
| `PriorityTriangularResidual.lean` | exact destructive drain-loop transfer and strict reset separation from finite translations |
| `FunctionalPhaseNoGo.lean` | positive quotient lifting, complete three-functional-phase weighting, cycle products, and the sharp fork |
| `EndpointPrefixCompiler.lean` | prefix-normal traces, endpoint-forcing three-pair compiler, underflow witness, and drift budget |
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
| Fixed data boundaries fold into one rank-one separator with a complete mortality converse | `unitFamily_mortal_boundaryOuter_iff` |
| The four-dimensional left--right coefficient is the determinant of two first columns | `SchottkyPunctuation.equalityCoefficient` |
| Unimodular pairs give multiplicative unimodular left--right actions | `SchottkyPunctuation.leftRight_mul`, `SchottkyPunctuation.leftRight_det` |
| Exact nonerasing Neary role macros require four letters | `ExactNearyMacroFactorization.four_le_card` |
| Exact Neary role macros require four letters even with erasure | `TernaryClosedBlockNoGo.ExactErasingMacroFactorization.four_le_card` |
| Stationary closed-block residuals obey the two discrete case splits | `TernaryClosedBlockNoGo.commonLowerDeletion_cases`, `TernaryClosedBlockNoGo.upperResidualShift_cases` |
| Exact stroke terminal matching is equivalent to `consumed·b=c·produced` | `TernaryClosedBlockNoGo.tileHistory_terminal_match_iff_block_semantics` |
| A positive morphism cannot contribute one lower letter per block across a width-at-least-two upper pulse | `TernaryClosedBlockNoGo.no_fractional_lower_contribution` |
| Equality after arbitrary continuations forces prefix comparability | `WordDiscrepancy.prefixComparable_of_append_eq` |
| An internal free-monoid mismatch cannot be repaired by continuations | `WordDiscrepancy.mismatch_persists` |
| Signed prefix discrepancies obey the exact four transition laws and two terminal tests | `WordDiscrepancy.positive_positive_transition`, `WordDiscrepancy.positive_negative_transition`, `WordDiscrepancy.negative_negative_transition`, `WordDiscrepancy.negative_positive_transition`, `WordDiscrepancy.positive_terminal`, `WordDiscrepancy.negative_terminal` |
| A guarded priority-affine translation is exactly one debit, nested zero test, and credit macro | `PriorityAffineResidual.guardedTranslation_iff_nestedZeroMacro` |
| Nested initial-segment zero tests are monotone in their priority cut | `PriorityAffineResidual.nestedZero_mono` |
| A forward destructive fanout is exactly a VASS drain loop followed by the next nested zero test | `PriorityTriangularResidual.drainTransfer_iff_exitIteration` |
| The nested exit fixes the drain count and natural semantics forbids overdrain | `PriorityTriangularResidual.drainIteration_exit_steps`, `PriorityTriangularResidual.drainIteration_steps_le` |
| Unbounded reset is not a finite union of fixed translations | `PriorityTriangularResidual.reset_not_finite_translation_union` |
| Every loopless functional graph on three phases has one three-cycle or a two-cycle with feeder | `FunctionalPhaseNoGo.exists_routeShape` |
| Every positive functional three-phase quotient induces a strictly positive one-sided symbol drift | `FunctionalPhaseNoGo.exists_positive_symbolWeight_oneSided` |
| Local positive transfers force the corresponding two- and three-cycle product inequalities | `FunctionalPhaseNoGo.twoCycle_product_le`, `FunctionalPhaseNoGo.twoCycle_product_ge`, `FunctionalPhaseNoGo.threeCycle_product_le`, `FunctionalPhaseNoGo.threeCycle_product_ge` |
| The forked two-cycle has both strict drift signs under every positive weighting | `FunctionalPhaseNoGo.forkDrift_mixed`, `FunctionalPhaseNoGo.forkDrift_not_oneSided` |
| Opposite drifts in an additive exponent relation force a positive diagonal edge | `FunctionalPhaseNoGo.IsAdditiveRelation.exists_positive_diagonal_of_mixed` |
| The canonical complete fork sweep obeys its exact linear equations, bounds, residue law, symmetry, and descent | `FunctionalPhaseNoGo.forkSweep_iff_linear`, `FunctionalPhaseNoGo.forkSweep_bounds_mod`, `FunctionalPhaseNoGo.forkSweep_three_dvd_iff`, `FunctionalPhaseNoGo.forkSweep_symm`, `FunctionalPhaseNoGo.forkSweep_double_to_self`, `FunctionalPhaseNoGo.forkSweep_odd_descent` |
| Endpoint prefix forcing makes the aggregate boundary equation equivalent to lawful traced execution | `EndpointPrefixCompiler.endpointEquation_iff_derivesAlong` |
| A locally head-separated output makes every endpoint witness a lawful trace | `EndpointPrefixCompiler.endpointEquation_iff_derivesAlong_of_headSeparated`, `EndpointPrefixCompiler.endpointPrefixForcing_of_headSeparated` |
| The unrestricted endpoint telescope has an explicit false underflow witness | `EndpointPrefixCompiler.underflow_endpointEquation`, `EndpointPrefixCompiler.underflow_not_derivesAlong` |
| Every nonnegative corrected-drift prefix stays within its terminal budget | `EndpointPrefixCompiler.nonnegative_prefix_budget` |
| A nonsingular finite Hankel section lower-bounds every exact realization | `finiteHankel_card_le` |
| Exact diagonal two-channel bridges pay two additional states | `exactDiagonalTwoChannel_card_lower_bound` |
| A split finite-rank binary pair is mortal exactly when one return product vanishes | `ReturnFamily.pairGenerator_isMortal_iff` |
| Finite return block-Hankel sections factor through every exact ambient realization | `ReturnFamily.finiteReturnHankel_factor`, `ReturnFamily.returnHankel_card_le` |
| A pure-cubic split pair is mortal exactly when its three residue returns are mortal | `CubicReturn.pairGenerator_isMortal_iff_residue` |
| Both reverse-compiler scalars of the pure one-singular cubic normal form equal `μ⁻¹` | `CubicReturn.pureOneSingular_reverseEdgeScalars` |
| One non-pure rank-two physical family aligns the actual singular endpoints through selected wait one | `CubicReturn.NonPure.terminalCut_rank`, `CubicReturn.NonPure.terminal_zero` |
| A second non-pure family avoids the kernel on every selected word but has an exact zero made only from strictly unselected positive waits | `CubicReturn.NonPure.falseWaitCut_rank`, `CubicReturn.NonPure.selected_lower_ne_zero`, `CubicReturn.NonPure.falseWaitWord_strictly_unselected`, `CubicReturn.NonPure.falseWait_zero` |
| A split finite-rank family is mortal exactly when one constrained edge path vanishes | `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero` |
| Every compatible two-plane edge square is realized by two rank-two generators | `TwoPlaneEdges.output_mul_input`, `TwoPlaneEdges.generator_rank` |
| Generic projective incidence compiles to two rank-two `3 × 3` generators | `ReverseEdge.isMortal_adaptedGenerator_iff`, `ReverseEdge.adaptedGenerator_rank` |
| Genericity is avoidance of two exact source rays | `ProjectiveIncidence.generic_iff_sourcePoint_not_mem_badSources` |
| At most two source rays are bad in both orientations, and their two transitions exit together | `ProjectiveIncidence.commonBadSources_card_le_two`, `ProjectiveIncidence.commonBadSources_two_transition_iff` |
| Every generic PI₂ instance scales to `α=β=1` without changing its word-zero language | `ProjectiveIncidence.exists_unitNormalized` |
| The inverse predecessor language is exactly shortcut-Collatz reachability | `ProjectiveCollatz.reachesOne_iff_shortcutCollatz` |
| Every malformed Collatz predecessor word remains nonintegral by negative 3-adic valuation | `ProjectiveCollatz.predecessorState_reaches_or_negative` |
| Every nonzero shortcut-Collatz target reduces exactly to normalized GPI₂ | `ProjectiveCollatz.normalizedScalars`, `ProjectiveCollatz.exists_normalizedIncidence_zero_iff` |
| In a finite group, positive monoid closure of a group-generating set is the whole group | `FinitePositiveImage.Submonoid.inv_mem_of_finite`, `FinitePositiveImage.mclosure_eq_top_of_group_closure_eq_top` |
| A free rational shear orbit with trivial source stabilizer misses `[10:13]`, while an explicit five-factor word reaches it projectively modulo every positive integer | `CongruenceBlindOrbit.shearRepresentation_injective`, `CongruenceBlindOrbit.sourcePoint_stabilizer_trivial`, `CongruenceBlindOrbit.targetPoint_not_reachable`, `CongruenceBlindOrbit.bridgeMatrix_idempotent_projective_target`, `CongruenceBlindOrbit.shearRepresentation_bridgeWord`, `CongruenceBlindOrbit.exists_bridgeWord_modular_hit` |
| The raw mixed-prime affine action has a published relation at length 27, an infinite distinct equal-map family at every odd length from 29, and three independent relations at length 30 | `MixedPrimeKernel.cassaigne_ne`, `MixedPrimeKernel.wordAction_cassaigne`, `MixedPrimeKernel.kernelOddFamily_length`, `MixedPrimeKernel.kernelOddFamily_ne`, `MixedPrimeKernel.wordAction_kernelOddFamily`, `MixedPrimeKernel.kernel30_ne`, `MixedPrimeKernel.wordAction_kernel30a`, `MixedPrimeKernel.wordAction_kernel30b`, `MixedPrimeKernel.wordAction_kernel30c` |
| Every odd-family relation is an exact homogeneous matrix relation preserved by arbitrary independent generator scaling, so nonzero unit normalization cannot restore freeness | `MixedPrimeNormalization.kernelOddFamily_count`, `MixedPrimeNormalization.kernelOddFamily_perm`, `MixedPrimeNormalization.scaledAffineGenerator_isUnit`, `MixedPrimeNormalization.wordProduct_scaledAffineGenerator_kernelOddFamily`, `MixedPrimeNormalization.scaledAffineGenerator_not_injective` |
| In any group-valued interpretation, the first two odd-family instances force the whole family by conjugate commutation | `MixedPrimeNormalization.groupPump_eq_of_zero_one`, `MixedPrimeNormalization.wordProduct_kernelOddFamily_of_zero_one` |
| Every nonempty critical-shell wait schedule has a rational periodic `5`-unit at every cyclic phase | `PeriodicShell.shellPeriodicCycle` |
| Repeating a fixed shell schedule subtracts its length from the `5`-adic displacement valuation each period, bounding legal repetition away from its unique periodic point | `PeriodicShell.shellRun_repeat_sub_periodicPoint_value`, `PeriodicShell.shellRun_repeat_unit_bound` |
| Every shell wait has exact two- and three-adic walls; away from equality, the lower valuation survives and the upper valuation resets to zero | `MixedPrimeDebt.shellStep_two_belowWall`, `MixedPrimeDebt.shellStep_two_aboveWall`, `MixedPrimeDebt.shellStep_three_belowWall`, `MixedPrimeDebt.shellStep_three_aboveWall` |
| Every negative-depth target has a complete pairwise-distinct predecessor fan indexed by `0,…,d`; a `5`-unit target carrier makes every predecessor state a `5`-unit | `MixedPrimeDebt.shellStep_debtState_eq_iff`, `MixedPrimeDebt.debtState_fiveUnit`, `MixedPrimeDebt.debtPredecessor_fan`, `MixedPrimeDebt.debtPredecessor_state_injective` |
| Arbitrary uninterrupted debt schedules obey their exact carrier recurrence and Łukasiewicz depth balance | `MixedPrimeDebt.shellRun_debtSafe`, `MixedPrimeDebt.debtRunDepth_balance` |
| Same-length debt bridges with common endpoint depths have one slope, so a collision at one source is a global affine relation | `MixedPrimeDebt.debtSafe_sameLength_collision_global` |
| Unequal nonempty shell schedules have one explicit collision source, which is automatically a `5`-adic unit; target acceptance is exactly a determinant-valuation condition; both three-adic carrier orientations occur at shell-legal cross-length collisions | `MixedPrimeDebt.collisionSource_eq_of_shellRun_eq`, `MixedPrimeDebt.collisionSource_fiveUnit`, `MixedPrimeDebt.collisionTarget_fiveUnit_iff`, `MixedPrimeDebt.positiveOrientation_crossLengthCollision`, `MixedPrimeDebt.negativeOrientation_crossLengthCollision` |
| Adjacent-length debt bridges between common depths have slope ratio `2/5`; target acceptance is exactly cancellation of their cleared offsets to the shorter length and is not automatic | `MixedPrimeDebt.shellOffset_cons`, `MixedPrimeDebt.adjacentDebtBridge_slope`, `MixedPrimeDebt.adjacentDebtBridge_collisionTarget_fiveUnit_iff`, `MixedPrimeDebt.adjacentDebtBridge_targetOvercancellation` |
| The fixed source `43/24` supports an exact adjacent-length collision family at every terminal wait; its targets lie on the complementary two-adic pole, are pairwise distinct, admit an explicit fixed-target membership test, and are accepted whenever the wait is divisible by ten | `MixedPrimeDebt.fixedSourceAdjacentFamily`, `MixedPrimeDebt.fixedSourceAdjacentFamily_target_injective`, `MixedPrimeDebt.fixedSourceAdjacentFamily_targetPole`, `MixedPrimeDebt.fixedSourceAdjacentFamily_target_exists_iff`, `MixedPrimeDebt.fixedSourceAdjacentFamily_ten_mul_numerator_mod`, `MixedPrimeDebt.fixedSourceAdjacentFamily_ten_mul_numerator`, `MixedPrimeDebt.fixedSourceAdjacentFamily_ten_mul_accepted` |
| Every next block from the accepted fixed-source collision ray is a forced valuation-minus-one exit; its surface is injective with a two-candidate target test, and target valuation reduces its full continuation cone to one fixed translated-letter count | `MixedPrimeDebt.fixedSourceAdjacentExitTarget_fiveNegative`, `MixedPrimeDebt.fixedSourceAdjacentExitTarget_displacement`, `MixedPrimeDebt.fixedSourceAdjacentExitTarget_displacement_twoValue`, `MixedPrimeDebt.fixedSourceAdjacentExitTarget_tail_fiveNegative`, `MixedPrimeDebt.fixedSourceAdjacentExitTarget_exists_iff`, `MixedPrimeDebt.fixedSourceAdjacentExitTarget_injective`, `MixedPrimeDebt.fixedSourceAdjacentContinuationSchedule_run`, `MixedPrimeDebt.fixedSourceAdjacentExitTarget_tail_length`, `MixedPrimeDebt.fixedSourceAdjacentContinuation_exists_iff_lengthCandidate`, `MixedPrimeDebt.fixedSourceAdjacentContinuation_translate_count` |
| Every critical-shell exit is zero, valuation-minus-one, or positive; every nonempty suffix to a fixed target has one of two target-derived lengths | `MixedPrimeDebt.shellStep_fiveUnit_exit_cases`, `MixedPrimeDebt.shellRun_fiveUnit_exit_nonempty_tail_value_cases`, `MixedPrimeDebt.shellRun_fiveUnit_exit_nonempty_tail_length_cases` |
| Every shell schedule preserves `[1/5,1/2]`; an exterior target obeys a zero-wait extremal envelope and has an explicit computable schedule-length bound | `MixedPrimeDebt.shellRun_mem_realTrap`, `MixedPrimeDebt.shellRun_above_half_envelope`, `MixedPrimeDebt.shellRun_above_half_length_lt_bound`, `MixedPrimeDebt.shellRun_below_one_fifth_envelope`, `MixedPrimeDebt.shellRun_below_one_fifth_length_lt_bound` |
| Every rational `5`-adic unit target in `(1/5,1/2]` has guarded rational predecessor schedules of every prescribed block length | `MixedPrimeDebt.exists_shellStep_realTrap_predecessor`, `MixedPrimeDebt.exists_shellStep_realTrap_unit_predecessor`, `MixedPrimeDebt.exists_shellRun_realTrap_unit_predecessor_of_length` |
| Every real-trap target has a computable sharp three-wait predecessor window, reducing fixed-source one-step reachability to three equalities | `MixedPrimeDebt.shellStep_realTrap_wait_window`, `MixedPrimeDebt.exists_shellStep_realTrap_iff_three_candidates`, `MixedPrimeDebt.shellStep_realTrap_wait_window_sharp` |
| Every fixed real-trap source has its complete one-step orbit on one normalized-mantissa ray; target depth leaves one exact candidate | `MixedPrimeDebt.shellStep_realTrap_upperRay`, `MixedPrimeDebt.shellStep_realTrap_middleRay`, `MixedPrimeDebt.shellStep_realTrap_lowerRay`, `MixedPrimeDebt.exists_shellStep_realTrap_upper_iff_candidate`, `MixedPrimeDebt.exists_shellStep_realTrap_middle_iff_candidate`, `MixedPrimeDebt.exists_shellStep_realTrap_lower_iff_candidate` |
| Every reduced-denominator exponent away from `2`, `3`, and `5` is invariant through arbitrary shell execution, including first exits | `MixedPrimeDebt.shellRun_spectatorDenominator`, `MixedPrimeDebt.shellRun_spectatorDenominator_of_ne_active`, `MixedPrimeDebt.shellRun_ne_of_spectatorDenominator_ne` |
| At every `5`-adic unit source, one-step shell acceptance depends only on the wait modulo ten; a fixed length-`ℓ` tail has period `2·5^(ℓ+1)`, lowering the precision exponent by one fails at an explicit unit zero preimage, and every fixed modulus identifies opposite guard outcomes at some depth | `MixedPrimeDebt.shellStep_fiveUnit_add_ten_iff`, `MixedPrimeDebt.shellStep_fiveUnit_add_ten_mul_iff`, `MixedPrimeDebt.shellStep_fiveUnit_iff_mod_ten`, `MixedPrimeDebt.shellRun_tail_fiveUnit_add_precisionPeriod_iff`, `MixedPrimeDebt.shellRun_tail_fiveUnit_add_precisionPeriod_mul_iff`, `MixedPrimeDebt.shellRun_tail_fiveUnit_iff_mod_precisionPeriod`, `MixedPrimeDebt.shellRun_shellZeroPreimage`, `MixedPrimeDebt.shellZeroPreimage_fiveUnit`, `MixedPrimeDebt.shellRun_tail_precisionPeriod_sharp`, `MixedPrimeDebt.shellRun_fixedModulus_sharp` |
| Raising a normalized target depth and the final wait by the same amount preserves equality; above depth one, nonempty source reachability is depth-independent and guarded reachability reduces to the twelve canonical depth classes `0,…,11` while retaining exact mantissa | `MixedPrimeDebt.shellStep_realTrapBandPoint_shift_iff`, `MixedPrimeDebt.exists_nonempty_shellRun_realTrapBandPoint_shift_iff`, `MixedPrimeDebt.realTrapBandPoint_fiveUnit_add_ten_mul_iff`, `MixedPrimeDebt.exists_guarded_shellRun_realTrapBandPoint_add_ten_mul_iff`, `MixedPrimeDebt.realTrapDepthRepresentative_decomposition`, `MixedPrimeDebt.exists_guarded_shellRun_realTrapBandPoint_representative_iff` |
| Every normalized target has at most three exact interval-separated predecessor candidates; on the sole unbounded branch, inherited-denominator cancellation is `gcd(10a−9b,b)=gcd(2,b)` and only the wall `b=2c` exposes the secondary residual `5a−9c` | `MixedPrimeDebt.shellStep_realTrapBandPoint_iff_three_predecessors`, `MixedPrimeDebt.lowerCenteredNumerator_gcd`, `MixedPrimeDebt.lowerCenteredNumerator_twoValue_of_oddDenominator`, `MixedPrimeDebt.lowerCenteredNumerator_twoValue_of_four_dvd_denominator`, `MixedPrimeDebt.lowerCenteredNumerator_twoValue_of_exactlyOne_denominator`, `MixedPrimeDebt.lowerNormalizedMantissa_twoValue`, `MixedPrimeDebt.lowerNormalizedMantissa_threeValue`, `MixedPrimeDebt.lowerNormalizedMantissa_twoValue_of_exactlyOne_denominator` |
| Every sufficiently deep normalized source band occurs on the deepest real-trap predecessor branch; a period-fifty subfamily preserves both endpoint unit guards at unbounded depth, is fed from the fixed source `2/9`, has exact two-/three-adic values, and has distinct targets | `MixedPrimeDebt.realTrapMaxPredecessorWait_bandPoint`, `MixedPrimeDebt.shellStep_realTrap_poleBranch_full`, `MixedPrimeDebt.shellStep_realTrap_guardedPoleReset`, `MixedPrimeDebt.shellStep_realTrap_guardedPoleFeed`, `MixedPrimeDebt.shellStep_realTrap_guardedPoleFeed_target_injective`, `MixedPrimeDebt.shellStep_realTrap_guardedPoleReset_twoThreeValues`, `MixedPrimeDebt.shellStep_realTrap_guardedPoleReset_target_injective` |
| Shell phases are all units exactly when the final output is a unit | `PeriodicShell.shellPrefixesUnit_iff` |
| Raw words and shell schedules are conjugate, and every boundary-shifted benchmark schedule is one contextual raw rule | `PeriodicShell.shellRun_eq_wordAction`, `PeriodicShell.shellRawWord_benchmarkRelationShiftLeft`, `PeriodicShell.shellRawWord_benchmarkRelationShiftRight`, `PeriodicShell.shellRun_benchmarkRelationShift` |
| Two distinct length-thirteen benchmark schedules induce the same affine map, preserve all guards in every context, and share a rational all-unit cycle | `PeriodicShell.benchmarkRelation_ne`, `PeriodicShell.shellRun_benchmarkRelationContext`, `PeriodicShell.benchmarkRelationContextGuard`, `PeriodicShell.benchmarkRelationCycle` |
| A compatible one-loop edge square is mortal exactly at loop nilpotence or intrinsic generic incidence | `RankTwoPunctuation.exists_pathProduct_eq_zero_iff_selfBridge_or_incidence` |
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
| Primitive endpoint normalization collapses into one deterministic cumulative recurrence | `ReturnGuard.primitiveIntegralStep_cumulativeEndpointStep`, `ReturnGuard.CumulativeEndpointStep.target_unique`, `ReturnGuard.cumulativeNumerator_recurrence` |
| Every common divisor of a terminal scalar and angular coefficient lies in the determinant support before the final branch | `ReturnGuard.endpointTransfer_casoratian`, `ReturnGuard.terminalCommonDivisor_dvd_previousDet` |
| Every primitive endpoint reduction projectivizes to the corresponding rational guard step | `ReturnGuard.PrimitiveEndpointReduction.guardedStep_endpointState` |
| Primitive content is exactly the gcd of the drift source and the unreduced quotient; reverse content satisfies a wait-free terminal divisor law | `ReturnGuard.PrimitiveEndpointReduction.content_natAbs_eq_gcd_driftSource_prequotient`, `ReturnGuard.PrimitiveEndpointReduction.resetDefect_eq_complement_mul`, `ReturnGuard.PrimitiveEndpointReduction.complement_dvd_terminalBoundary` |
| A reverse-content divisor recurring in the next boundary outside fixed scale-reset support remains wholly reverse | `ReturnGuard.PrimitiveEndpointReduction.recurrentBoundaryDivisor_persists` |
| Outside fixed `pDL` support, a divisor enters forward content exactly at simultaneous endpoint and branch-boundary divisibility | `ReturnGuard.PrimitiveEndpointReduction.divisor_dvd_content_iff` |
| Every positive wait has an exact terminal predecessor, so backward terminal search has no wait bound | `ReturnGuard.terminalPredecessorPair_step` |
| Cumulative endpoints form a generalized continued fraction with one fixed forbidden cusp | `ReturnGuard.cumulativeCompleteQuotient_recurrence`, `ReturnGuard.cumulativeCompleteQuotient_sub_forbiddenCusp`, `ReturnGuard.cumulativeWaitForm_hasValue` |
| At critical depth two, every nondecreasing pair of waits pays an exact two-step content budget | `ReturnGuard.PrimitiveEndpointReduction.twoStep_elimination`, `ReturnGuard.PrimitiveEndpointReduction.twoStep_contentBudget` |
| Consecutive primitive reductions carry a primitive prequotient coordinate through one exact integral generalized-continuant block at every depth | `ReturnGuard.PrimitiveEndpointReduction.prequotient_coprime_denominator`, `ReturnGuard.PrimitiveEndpointReduction.twoStep_prequotient_transport` |
| Consecutive primitive reductions obey the exact generalized Jacobi shell law, whose backward map has an explicit reciprocal difference factor | `ReturnGuard.PrimitiveEndpointReduction.jacobiTail_transition`, `ReturnGuard.jacobiBackward_sub` |
| Every functional primitive endpoint stream of depth at least two with bounded positive denominators is eventually periodic | `ReturnGuard.PrimitiveEndpointReduction.nonDecreasing_waits_le`, `ReturnGuard.BoundedPrimitiveEndpointStream.wait_le`, `ReturnGuard.BoundedPrimitiveEndpointStream.eventually_periodic` |
| The critical decoder is an order-three core followed by a wait-dependent shear | `ReturnGuard.criticalDecoder_factor`, `ReturnGuard.criticalDecoderCore_cube` |
| The Smith decoder is a positive shear followed by one Gauss continuant generator | `ReturnGuard.smithRubanDecoder_continuant_cut` |
| Positive Smith decoding preserves primitivity and strictly raises primitive-pair height | `ReturnGuard.smithRubanQuotient_isCoprime`, `ReturnGuard.smithRubanQuotient_height_gain_of_pos` |
| One fixed rational basis diagonalizes every variable-wait frame gauge | `ReturnGuard.returnWaitFrameChange_diagonal` |
| Every base-coprime cancellation depth is the minimum of the terminal-defect and displacement depths | `ReturnGuard.integralStep_cancel_iff_terminalDefect_and_displacement`, `ReturnGuard.integralStep_commonFactor_padicValInt` |
| Legal waits are logarithmic in primitive height and reduced height is uniformly Lipschitz | `ReturnGuard.integralStep_wait_le_log_height`, `ReturnGuard.integralStep_reduced_height_le` |
| A large primitive cyclotomic radical forces terminality or a surviving exact-order reset | `ReturnGuard.terminalDefect_zero_or_exists_primitive_reset`, `ReturnGuard.primitiveCyclotomicRadical_le_height_of_no_reset` |
| Absent every primitive reset, the full primitive cyclotomic part divides the common reduction with all multiplicities | `ReturnGuard.primitiveCyclotomicPart_dvd_common_of_no_reset`, `ReturnGuard.primitiveCyclotomicPart_le_height_of_no_reset` |
| The swallowed primitive part pays the distinguished wait scale in the same height budget | `ReturnGuard.primitiveCyclotomicPart_mul_wait_le_height_of_no_reset` |
| Above exponent two, every index prime occurring in the cyclotomic value has valuation one | `cyclotomicValue_factorization_eq_one_of_odd_nonprimitive`, `cyclotomicValue_factorization_eq_one_of_two_nonprimitive` |
| The cyclotomic value divides the exponent times its full primitive part, which inherits the elementary totient lower bound | `ReturnGuard.cyclotomicValue_dvd_exponent_mul_primitiveCyclotomicPart`, `ReturnGuard.sub_one_pow_totient_le_exponent_mul_primitiveCyclotomicPart` |
| No-reset branches pay cyclotomic growth and the distinguished wait scale in one formal inequality | `ReturnGuard.strongPrimitivePressure_le_height_of_no_reset` |
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
| Terminal coordinates are a fixed gauge of the primitive residual transfer, not an independent state | `ReturnGuard.endpointTransfer_mul_endpointGauge`, `ReturnGuard.terminalCoordinate_residualStep` |
| A complete endpoint word factors its determinant into base powers and full cyclotomic factors | `ReturnGuard.endpointProduct_det` |
| Every positive endpoint product modulo the distinguished prime is a scalar multiple of one fixed rank-one flag; in a normalized presentation its determinant valuation is the full schedule weight | `ReturnGuard.endpointProduct_mod_prime`, `ReturnGuard.endpointProduct_det_hasValue` |
| At the complete prime-power weight of every nonempty positive cumulative prefix from reset, the endpoint-product kernel is exactly the scalar reset line | `ReturnGuard.CumulativeEndpointExecution.endpointKernel_eq_resetLine` |
| A positive endpoint word is terminal exactly when its inverse address is reset; physical mortality is exactly existence of such a nonempty word and the terminal language is singleton-or-empty | `ReturnGuard.endpointTerminalWord_iff_inverseAddress_eq_one`, `ReturnGuard.physical_isMortal_iff_endpointTerminalWord`, `ReturnGuard.endpointTerminalWord_unique` |
| Forward and reverse primitive contents are complementary, and the whole terminal coefficient is their signed reverse-content product | `ReturnGuard.endpointAdjugate_mulVec_of_complementaryContent`, `ReturnGuard.endpointProduct_first_eq_complementProduct` |
| A prime dividing `A−L` but neither drift nor base excludes every endpoint terminal word | `ReturnGuard.not_endpointTerminalWord_of_prime_dvd_centerDifference` |
| Primitive content and wait depth share one exact Archimedean height budget | `ReturnGuard.integralStep_content_mul_height_le`, `ReturnGuard.integralStep_wait_content_le` |
| The entire part of `pᵃ−1` coprime to forward content survives in the target's reset difference | `ReturnGuard.cyclotomicComplement_dvd_targetDifference` |
| Two reduced trajectories through one branch obey an exact exterior-product conservation law | `ReturnGuard.primitiveSteps_projectivePairCross` |
| Any repeated legal factor at two checkpoints is either an exact cycle or bounded by their rational height envelopes | `ReturnGuard.sharedSchedule_exact_or_power_le_heightEnvelope` |
| Terminal-reaching guards can require two steps and their waits can either decrease or increase | `ReturnGuard.Examples.decreasingMortal_reachable`, `ReturnGuard.Examples.increasingMortal_reachable` |
| A lawful first-hit terminal word has primitive angular primes outside every coefficient and branch-cyclotomic factor | `ReturnGuard.Examples.decreasingMortal_emergentAngularPrimes` |
| One lawful guard has exactly one positive terminal word, the three-return schedule `[1,1,1]` | `ReturnGuard.Examples.threeReturn_endpointTerminalWord_iff`, `ReturnGuard.Examples.threeReturn_physical_isMortal` |
| One fixed guard has arbitrarily long off-reset legal corridors with `v=2`, exact content `−4`, and arbitrarily long rising carried and primitive Smith coordinate runs | `ReturnGuard.Examples.periodicShadow_obstruction` |
| The proposed order-breaking counterorbit has forced waits `[4,1,1,1,1]` and then enters the nonterminal trap | `ReturnGuard.Examples.orderBreaker_candidate_enters_trap` |
| Repeating the lawful period-three cycle fixes reset while accumulating an exact 13-power on a transverse rational eigenline | `ReturnGuard.Examples.cycle_endpointReductions`, `ReturnGuard.Examples.cycle_transverseReservoir` |
| Same-address reset companions do not contract stepwise, even on nonmaximal first-hit terminal steps | `ReturnGuard.Examples.resetCompanion_counterfamily` |
| The former collision ladder and period-three survivor are excluded from terminality by one-prime endpoint coefficients | `ReturnGuard.Examples.collisionLadder_no_endpointTerminalWord`, `ReturnGuard.Examples.cycle_no_endpointTerminalWord` |
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
| Toggle prefixing preserves the paired coefficient and can normalize any suffix to erase phase | `pairedCoefficient_toggle_cons`, `exists_erase_phase_eq_coefficient` |
| An erase-phase `c` prefix never vanishes | `pairedCoefficient_data_c_cons_ne_zero_of_erase` |
| Projectively forgetting erase-`c` excludes every paired zero, in any target dimension | `no_zero_of_erase_c_projective_identification` |
| Phase-local roles, discrepancies, quotient scale, and mixing have their displayed forms | `PhaseRigidity.localRole_eq`, `PhaseRigidity.phase_discrepancies`, `PhaseRigidity.discrepancy_quotient`, `PhaseRigidity.ruleCMixing_ne_zero` |
| The two phase commutators are one constant and one radial translation | `PhaseRigidity.erase_commutator`, `PhaseRigidity.discrepancy_commutator` |
| Every invariant two-dimensional affine pencil forgets the accumulator | `PhaseRigidity.neary_commutator_pencil_forgets_t` |
| Neary role words have an injective nonzero-digit base-five code | `historyCode_injective` |
| Every history-control word reaches its decoded code and suffix-phase sign | `historyProduct_mulVec_column`, `historyCoefficient_eq_code_sub` |
| Width three with body `bcbb` has two distinct terminal role words | `NullHistoryCounterexample.terminal_word_not_unique` |
| A minimum-length body has exactly one terminal role word | `minimalBody_terminal_word_unique`, `minimalBody_terminal_match` |
| The three-state history encoder has exactly the paired zeros on minimum-length bodies | `minimalBody_history_zero_iff_paired_zero` |
| The four integral history matrices are mortal exactly at a history-code zero | `historyMortalityFamily_int_mortal_iff_zero`, `minimalBody_historyMortality_iff_paired_zero` |
| The explicit code `92` family is mortal with decoded witness `ctbbt` | `MinimalBodyExample.terminal_code`, `MinimalBodyExample.witness_decode`, `MinimalBodyExample.mortality` |
| The mixed-radix paired-history code is injective | `TransverseHistory.code_injective` |
| Fixed transverse-kernel controls maintain that code on every raw control word | `TransverseHistory.product_mulVec_column`, `TransverseHistory.data_mulVec_eq_zero_iff` |
| The transverse controls have exactly the paired zeros on every minimum body | `TransverseHistory.coefficient_zero_iff_decode_eq`, `TransverseHistory.minimalBody_zero_iff_paired_zero` |
| The `bcbb` null histories and complete terminal language are one exact periodic ray | `PeriodicHistory.bcbbNull_iff`, `PeriodicHistory.bcbb_terminal_match_iff` |
| The singular positional decoder obeys its all-control affine state equation | `PeriodicHistory.periodicProduct_mulVec_column`, `PeriodicHistory.periodicCoefficient_eq` |
| The `bcbb` affine section has no false zero and matches the paired zero language | `PeriodicHistory.bcbbAffine_zero_iff`, `PeriodicHistory.bcbb_periodicCoefficient_zero_iff_paired_zero` |
| Four explicit integral `bcbb` matrices are mortal exactly at a paired zero | `PeriodicHistory.bcbbIntegralSeparator_cast`, `PeriodicHistory.bcbbIntegralFamily_mortal_iff_paired_zero` |
| The `bcbc` terminal language contains injective equal-length binary forks | `BranchingHistory.bcbcForkRoles_injective`, `BranchingHistory.bcbcTerminalFork_injective`, `BranchingHistory.bcbcTerminalFork_match` |
| No affine positional row section recognizes the complete `bcbc` terminal language | `BranchingHistory.no_affine_positional_section` |
| Local fork equality and two-step erase recovery force a terminal/nonterminal `bcbc` state collision | `BranchingHistory.bcbc_terminal_nearFork`, `BranchingHistory.bcbcNearFork_state_eq_of_local_fork`, `BranchingHistory.no_bcbc_sameZero_of_local_fork` |
| The complete parametric phase-line carry family identifies the terminal prefix with its nonterminal near-fork | `BranchingHistory.phaseLine_terminal_eq_nearFork`, `BranchingHistory.no_phaseLine_bcbc_sameZero` |
| The `bcbc` null and terminal histories have the complete nested-excursion grammars | `BranchingRecognizer.bcbcNull_iff`, `BranchingRecognizer.bcbc_terminal_match_iff` |
| The reported singular recognizer obeys its exact all-control affine recurrence | `BranchingRecognizer.recognizerProduct_mulVec_delta`, `BranchingRecognizer.recognizerCoefficient_eq_guard` |
| Canonical controls decode every `bcbc` terminal history and vanish in both scalar systems | `BranchingRecognizer.terminalControl_decode`, `BranchingRecognizer.recognizerCoefficient_terminalControl`, `BranchingRecognizer.pairedCoefficient_terminalControl` |
| The `bcbcbb` terminal histories are exactly one fixed prefix followed by arbitrary equal-length binary null blocks | `MixedBranchingRecognizer.mixedNull_iff`, `MixedBranchingRecognizer.mixed_terminal_match_iff` |
| Toggle scouring gives the exact two normal spellings of each mixed terminal history | `MixedBranchingRecognizer.decode_eq_terminal_iff_scourToggles` |
| The integral mixed recognizer equals the paired zero language on every raw control word | `MixedBranchingRecognizer.recognizerCoefficient_eq_zero_iff`, `MixedBranchingRecognizer.pairedCoefficient_eq_zero_iff`, `MixedBranchingRecognizer.recognizerCoefficient_eq_zero_iff_paired` |
| Its data maps have one exact common kernel, its toggle is involutive, and no generator product is zero | `MixedBranchingRecognizer.recognizerData_mulVec_eq_zero_iff`, `MixedBranchingRecognizer.recognizerToggle_involutive`, `MixedBranchingRecognizer.recognizerProduct_ne_zero` |
| A matrix square equal to an outer product gives the complete `SS`-free mortality grammar | `SquareRootPunctuation.isMortal_iff_exists_squareFree_zero` |
| The explicit source-uniform Neary punctuation matrix has the required square and rank two | `SquareRootPunctuation.nearySquareRoot_sq`, `SquareRootPunctuation.nearySquareRoot_rank` |
| Exact coefficient preservation on the `R_bR_b`-free subshift forces the `R_b` matrix to be a unit | `SquareRootPunctuation.ruleB_isUnit_of_exact_on_squareFree` |
| Nonzero multiplicative letter weights do not evade the square-free exact-series rigidity | `SquareRootPunctuation.ruleB_isUnit_of_weighted_exact_on_squareFree` |
| Every nondegenerate rank-one square root scales both boundary vectors by one nonzero scalar | `SquareRootPunctuation.squareRoot_boundary_eigenvectors` |
| Prefixing or suffixing an isolated square root preserves scalar vanishing | `SquareRootPunctuation.squareRoot_coefficient_cons_zero_iff`, `SquareRootPunctuation.squareRoot_coefficient_append_zero_iff` |
| Every arbitrary Neary terminal match begins with the `c`-rule role | `terminalMatch_starts_rule_c` |
| An `R_b`-prefixed role word cannot have zero native side coefficient | `SquareRootPunctuation.nearySide_ruleB_cons_ne_zero` |
| Boundary saturation refutes a proposed square-free same-zero decoder on the witness pair | `SquareRootPunctuation.no_ruleB_squareRoot_sameZero_on_boundary_pair` |
| Every reset-affine control word obeys its exact coordinate and target equation | `ResetAffineHistory.wordProduct_mulVec_column`, `ResetAffineHistory.coefficient_eq` |
| A zero and its leading toggle force the affine target to forget phase | `ResetAffineHistory.phaseWeight_eq_zero_of_toggle_pair` |
| A phase-only reset-affine target has the exact two-phase zero test | `ResetAffineHistory.exists_zero_of_left_zero_iff` |
| Every bounded target section of a finite-mode expanding affine history has finite reverse orbit | `ExpandingAffineHistory.reverseOrbit_finite`, `ClearedResetAffineHistory.reverseOrbit_finite` |
| The caged finite automaton recognizes the bounded-target language exactly | `ExpandingAffineHistory.cagedRun_eq_some`, `ExpandingAffineHistory.run_eq_of_cagedRun_eq_some` |
| Every bounded-target expanding affine history language is regular | `ExpandingAffineHistory.targetLanguage_isRegular` |
| Every whole-chart target reduces to a finite-mode regular language | `ExpandingAffineHistory.modeLanguage_isRegular` |
| Universal paired zero existence is exactly code halting and is not computable | `Undecidability.UniversalNeary.universalPairedZero_iff_codeHalts`, `Undecidability.UniversalNeary.universalPairedZero_not_computable` |
| No computable predicate has exactly the universal paired zero answers | `Undecidability.UniversalNeary.no_computable_sameZero_predicate` |
| Prefix-suffix decoding feeds the suffix phase into the left context exactly | `PairedResidual.decodeFrom_append`, `PairedResidual.suffixDecode_append` |
| Positive binary words embed in the binary free group and terminal matching is residual equality | `CancellativeRoleFraction.positiveWord_injective`, `CancellativeRoleFraction.terminal_eq_iff_residual_eq` |
| One rational conic has exactly the complete paired prefix-suffix zero support | `CancellativeRoleFraction.conicCoefficient_zero_iff_pairedCoefficient_zero` |
| Every finite paired support table has a rational realization of rank at most three | `CancellativeRoleFraction.exists_supportMatrix_rank_le_three` |
| Cancellative role fractions contain the displayed independent left and right actions | `CancellativeRoleFraction.leftSeed_eq`, `CancellativeRoleFraction.leftConjugate_eq`, `CancellativeRoleFraction.rightSeed_eq`, `CancellativeRoleFraction.rightConjugate_eq` |
| Projectively commuting invertible rational `3 × 3` matrices commute linearly | `CancellativeProjectiveRigidity.scalar_commutator_eq_one` |
| Every paired suffix and prefix residual lies in its respective one-turn chamber | `PairedInverseChamber.suffixResidual_positiveNegative`, `PairedInverseChamber.prefixResidual_negativePositive` |
| The two protected states are exact formal inverse combinations and have both sign turns | `PairedInverseChamber.leftInverseState_eq_formalCombination`, `PairedInverseChamber.rightInverseState_eq_formalCombination`, `PairedInverseChamber.leftInverseState_not_positiveNegative`, `PairedInverseChamber.rightInverseState_not_negativePositive` |
| Every positive Neary role continuation preserves both forbidden turns | `PairedInverseChamber.leftRoleContinuation_outsideChambers`, `PairedInverseChamber.rightRoleContinuation_outsideChambers` |
| Both formal inverse forward cones miss every actual suffix and phase-aware prefix residual | `PairedInverseChamber.leftRoleContinuation_ne_suffixResidual`, `PairedInverseChamber.leftRoleContinuation_ne_prefixResidual`, `PairedInverseChamber.rightRoleContinuation_ne_suffixResidual`, `PairedInverseChamber.rightRoleContinuation_ne_prefixResidual` |
| The singular positive countermodel has complete integral zero language `{t}` | `PositiveShiftCountermodel.coefficient_int_eq_zero_iff` |
| Every positive countermodel generator has rank exactly two | `PositiveShiftCountermodel.generator_rank` |
| Three reachable columns and three observable rows have nonzero determinant | `PositiveShiftCountermodel.reachableMatrix_det`, `PositiveShiftCountermodel.observableMatrix_det` |
| No positive countermodel matrix word is zero | `PositiveShiftCountermodel.wordProduct_int_ne_zero` |
| The positive `b`-shift collapses distinct reachable states and defeats backward cancellation | `PositiveShiftCountermodel.column_b_eq_bt`, `PositiveShiftCountermodel.column_nil_ne_t`, `PositiveShiftCountermodel.not_backward_cancellative` |
| A projectively full legal prepend cylinder forces its data map to be injective | `PositiveResetNoGo.injective_of_cylinder_span` |
| The two legal rule views of `qb` force the persistent collision `v_q∼v_ε` | `PositiveResetNoGo.positiveReset_collision` |
| A common-kernel route difference is erased by the first later data action | `PositiveResetNoGo.commonKernel_route_erased` |
| Transverse rank-two quotient fibres meet in the bilinear ray `[rv:us:vs]` | `PositiveResetNoGo.sameRay_bilinearFibrePoint` |
| A homogeneous radix prepend cylinder has determinant `B²(B−1)(d_b−d_c)` | `PositiveResetNoGo.radixCylinder_det`, `PositiveResetNoGo.radixCylinder_det_ne_zero` |
| Three positive letters evaluate surjectively onto the binary free group | `PositiveFreeCancellation.triangleEvaluate_surjective` |
| Three positive letters cover every prescribed first-exponent slice exactly | `PositiveFreeCancellation.firstExponent_triangleEvaluate`, `PositiveFreeCancellation.triangleSliceEvaluate_surjective` |
| Positive identity-triangle padding preserves both value and affine weight | `PositiveFreeCancellation.triangle_identity_padding` |
| Quotient-blind boundaries accepting an element and its square admit a nonempty identity witness | `PositiveFreeCancellation.exists_nonempty_identity_witness` |
| Invertible positive transitions carry each spelling-fibre span exactly along the group orbit | `PositiveFreeCancellation.positiveFibreSpan_word_map_eq`, `PositiveFreeCancellation.positiveFibreSpan_word_symm_map_eq` |
| Every nonzero vanished three-dimensional fibre has rank one or two | `PositiveFreeCancellation.positiveFibreSpan_finrank_one_or_two`, `PositiveFreeCancellation.positiveFibreSpan_eq_ker_of_finrank_two` |
| The identity fibre is the seed orbit of its unital identity-word operator algebra | `PositiveFreeCancellation.positiveIdentityAlgebra_map_apply_eq_fibre` |
| Triangle letters and their linear inverses give the exact group-orbit edges on fibre spans | `PositiveFreeCancellation.triangleFibreSpan_letter_map_eq`, `PositiveFreeCancellation.triangleFibreSpan_letter_symm_map_eq` |
| Every injective transition on a finite invariant semantic fibre pumps a positive period | `PositiveFreeCancellation.finiteFibre_identity_pumps` |
| A singular one-coordinate lift has the quotient kernel and absorbs every quotient identity | `PositiveFreeCancellation.singularLift_kernel_eq_quotientKernel`, `PositiveFreeCancellation.singularLift_absorbs_quotientIdentity` |
| The triangle-irreducible Hankel support has six independent rows over every field | `PositiveFreeCancellation.forbiddenTripleSupport_rows_linearIndependent` |
| Every row-column realization of the triangle-irreducible support needs six states | `PositiveFreeCancellation.six_le_card_of_forbiddenTripleSupport` |
| A one-sided inverse in a finite-dimensional algebra is two-sided | `DirectedCancellation.mul_eq_one_reverse_of_finiteDimensional` |
| Complete value-context absorption of one cancellation forces the reverse | `DirectedCancellation.reverse_value_context_cancellation_of_forward` |
| Projectively separating zero-context absorption forces the reverse | `DirectedCancellation.reverse_zero_context_cancellation_of_forward` |
| Asymmetric zero cancellation excludes every nonzero scalar identity and global projective separation | `DirectedCancellation.asymmetric_zero_context_cancellation_not_smul_one`, `DirectedCancellation.asymmetric_zero_context_cancellation_forces_projective_blindness` |
| Every exact diagonal paired-series bridge needs six states | `paired_exact_diagonal_twoChannel_state_lower_bound` |
| Every literal Neary CHHN placement needs six exact states | `chhnNeary_exactRepresentation_six_le_card` |
| Every two-state pushout word obeys its suffix decoder | `twoStateProduct_mulVec_phaseVector`, `twoStateCoefficient_eq_controlled` |
| A two-state reset has rank three; separated destinations have rank four | `twoStateDataMatrix_rank_eq_three_of_eq`, `twoStateDataMatrix_rank_eq_four_of_ne` |
| The integer two-state family is mortal exactly at a nonempty controlled scalar zero | `twoStateMortalityFamily_int_mortal_iff_nonempty_zero` |
| Promised positive overlap-queue acceptance is exactly mortality of three integer `4 × 4` matrices | `OverlapQueue.mortality_iff_accepts` |
| Every long accepted overlap queue has a state-preserving pure-deletion role | `OverlapQueue.pure_deletion_of_accepts_large` |
| Promised zero-framed binary context-2 Lag reachability is exactly mortality of three integer `4 × 4` matrices | `OverlapLag.mortality_iff_accepts` |
| Zero-framed binary context-2 Lag acceptance is exactly `(n=1 ∧ U=ε) ∨ (V=ε ∧ U∈0*)` | `OverlapLag.accepts_iff`, `OverlapLag.mortality_iff_syntax` |
| A fixed morphism cannot identify a terminal with its own compulsory return frame | `OverlapLag.terminal_image_ne_frame` |
| Every regular safe word preserves the oriented `3`-adic exterior flag | `ParabolicBlade.exteriorState_safe_word_flag`, `ParabolicBlade.exteriorState_safe_word_wall_orientation` |
| Every concrete defect skeleton without a bad four-periodic run is nonzero | `ParabolicBlade.defectSkeletonProduct_ne_zero_of_not_bad` |
| Neither shortest opposite-phase bad run closes when all three atoms are `b` | `ParabolicBlade.bridge_bZero_bTwo_bOne_det_ne_zero`, `ParabolicBlade.bridge_bOne_bTwo_bZero_det_ne_zero` |
| The shortest `0|2|1` bad run does not close with a `c` defect and `b` endpoints | `ParabolicBlade.bridge_bZero_cTwo_bOne_det_ne_zero` |
| Every nonempty pure-defect block has an invertible bridge | `ParabolicBlade.pureDefect_bridge_det_ne_zero` |
| A varying wall chain vanishes exactly at one consecutive projective incidence | `ParabolicBlade.bridgeFractureChain_eq_zero_iff` |
| A regular wall bridge has the explicit nonzero annihilating cokernel `(v,-4w)` | `ParabolicBlade.bridgeCokernel_eq_exteriorTail`, `ParabolicBlade.bridgeCokernel_regular_word_ne_zero`, `ParabolicBlade.bridgeCokernel_vecMul_bridge_of_wall` |
| A regular wall bridge has a canonical nonzero right kernel | `ParabolicBlade.bridgeKernel_regular_word_ne_zero`, `ParabolicBlade.bridge_mulVec_bridgeKernel_of_wall` |
| Incidence with a safe right wall forces a strict phase-selected transport chamber | `ParabolicBlade.safeWall_incidence_orients_transport`, `ParabolicBlade.safeWall_rejects_balanced_transport` |
| Every nonempty complete semantic block has a negative original bridge determinant | `ParabolicBlade.bridge_semanticWordMiddle_det_neg` |
| Every nonempty complete original Neary word has a negative bridge determinant | `ParabolicBlade.completeTileProduct_eq_semanticWordMiddle`, `ParabolicBlade.bridge_completeTileProduct_det_neg` |
| A fixed original incidence vanishing on the formal terminal plane vanishes on the whole length plane | `ParabolicBlade.semanticIncidence_terminal_forces_length`, `ParabolicBlade.no_fixed_semanticIncidence_terminal_zero_set` |
| The actual Neary formal terminal plane cannot be recognized by fixed original endpoint rays | `ParabolicBlade.no_fixed_semanticIncidence_neary_terminal_zero_set` |
| The two mixed-gap endpoint equations conditionally compile exact Neary terminal matching | `ParabolicBlade.conditional_semanticBridgeProduct_zero_iff_terminal` |
| Complete semantic contexts miss both conditional-compiler endpoint rays | `ParabolicBlade.no_complete_semantic_left_target`, `ParabolicBlade.no_complete_semantic_right_target` |
| The retuned family has one singular reduced atom, at gap two after `b` | `ParabolicRetuned.atom_det_eq_zero_iff` |
| The retuned bridge determinant is exactly the Neary terminal language | `ParabolicRetuned.bridge_tileProduct_det_eq_zero_iff_terminal_match` |
| One fixed minor of a literal retuned three-generator context recognizes `pairedCoefficient = 0` | `ParabolicRetuned.contextWord_product`, `ParabolicRetuned.physicalMinor_decoded_det_eq_zero_iff_pairedCoefficient` |
| A matched retuned context is nonzero and right annihilation is exactly annihilation of its fixed terminal row | `ParabolicRetuned.physicalContext_ne_zero`, `ParabolicRetuned.physicalContext_mul_eq_zero_iff_terminalRow` |
| Complete-gap continuations cannot annihilate the retuned terminal row | `ParabolicRetuned.terminalRow_vecMul_physicalMiddle_ne_zero` |
| The admissible source `(3,bbcc)` has no genuine terminal word, yet one malformed context is killed exactly by the lawful terminal-row annihilators | `ParabolicRetuned.poison_no_terminal_match`, `ParabolicRetuned.poisonContext_append_zero_iff`, `ParabolicRetuned.poison_fixedTerminalRow_obstruction` |
| Every instantiation of the original conditional endpoint compiler kills a regular gap-thirty pseudo-terminal on the admissible nonhalting source `(3,bbcc)` | `ParabolicRetuned.poison_originalEndpointCompiler_obstruction` |
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

The arbitrary-rational part of `G3-O02` remains an audited function-field theorem, not a formal
dependency. Lean checks its exact finite algebra, invariant-pencil rigidity core, and terminal
consumer, but not yet the dense-orbit extension or arbitrary rational-function rigidity.

The stationary closed-block part of `G3-O08` remains an audited finite-dimensional theorem, not
a formal dependency. Lean checks its erasing exact-macro special case and its integral residual
case splits, but not yet the abstract one-dimensional-kernel assembly or the universal-body
membership corollary.

The rational serializer theorem `G3-O13` and bounded-residual decision theorem `G3-D01` remain
audited paper theorems. Lean checks their canonical block-semantic interface and the final
fractional-contribution throat, but not the generic asynchronous-transducer pumping construction,
three-pulse factor classification, or extracted finite residual decision graph.

The virtually cyclic decision theorem `G3-D02` remains audited. Lean checks the discrepancy
transition calculus on which it acts, but not the two-power eventual-periodicity algorithm or the
one-counter reachability reduction.

The priority-affine atlas theorem `G3-D04` remains audited above its transition seam. Lean proves
the exact guarded-translation macro, while the finite atlas assembly and VASSnz reachability
algorithm are external. The latter is supported by the fully inspected metadata-only synopsis of
Guttenberg, Czerwiński, and Lasota's LICS 2025 theorem.

The priority-triangular extension `G3-D05` has the same external boundary. Lean proves the exact
drain-stage gadget and the strict containment of resets beyond finite translations. The finite
cascade through private modes and the imported VASSnz decision theorem remain audited. No Lean
declaration claims decidability for feedback, cyclic transfer, nonlinear multiplication,
incomparable tests, or changing priority.

The functional phase-transfer theorem `G3-D06` is kernel-checked through construction of the
positive symbol weight. The last step, enumeration of the finite bounded word graph for fixed
endpoints, is audited. No Lean declaration claims that a fork retaining mixed word memory, an
empty-consume pump, or a nonfunctional splitting quotient is decidable or universal.

The pure-phase fork theorem `G3-D07` is kernel-checked at its additive diagonal and canonical-fork
arithmetic core. The regular trace-language construction, effective Parikh projection, residue
grammar, and reduction to one-dimensional GVAS reachability are audited. Bizière and Czerwiński's
Theorem 1 supplies the external decision procedure. The claim is confined to nonempty phase-pure
consumes and outputs with one return word; mixed persistent words, empty consumes, and split
recurrent transport remain outside.

For `G3-O03`, Lean checks the null-history counterexample, minimum-body uniqueness, base-five
encoder, exact same-zero theorem, and integral mortality lift. The statement that both phase graph
closures are full products, with one-dimensional generic fibers, remains an independently audited
Zariski-density calculation rather than a formal dependency.

For `G3-O06`, Lean additionally checks that both periodic data controls have exact common kernel
`ℚ(1,1,0)`, that the toggle sends its generator to `(1,-1,0)`, and that either next data control
recovers `(2,0,0)`. This is the formal non-invariant kernel shuttle promised by the all-word
periodic recurrence; it does not make the fixed boundary constants source-uniform.

For `G3-O18`, Lean proves injectivity of the variable-radix role code, the exact state recurrence
under fixed integral transverse-kernel controls on every raw word, the scalar equality with one
prescribed code, both coordinate kernels, and the complete minimum-body paired equivalence. The
projective blow-up description is not a formal dependency: every actual orbit stays in the
affine chart with homogeneous coordinate one.

For `G3-O20`, Lean proves the free-monoid tail law: if one fixed-boundary equation with stationary
left and right pump blocks holds at exponents `N` and `N+1`, it holds at every exponent `N+k`.
The proof uses only prefix comparability and left/right cancellation. This closes a unary
consecutive-zero Cayley-Hamilton shortcut, not the noncommuting positive-transition lower-bound
lane.

For `G3-O22`, Lean proves the fibre-span transport, inverse group-orbit edge, common-rank,
dimension dichotomy, rank-two kernel equality, and identity-orbit algebra over arbitrary fields.
The group-orbit conclusion is deliberately weaker than a positive-semigroup reduction: the
inverse linear equivalences used for reverse edges need not occur among the positive controls.
The context-free fixed-point algorithm for computing the triangle identity algebra is audited
outside Lean.

For `G3-O23`, Lean proves rank-one factorization, rectangular saturated-language collapse,
rank-two image compression, invertibility of every image sandwich, exact identity interleaving,
rational two-coordinate transport, the empty-language carrier, and the triangle carrier
dichotomy. The triangle's effective rank sieve and its at-most-one rational Borel-coset
formulation for the promised empty-or-singleton fibre are audited consequences, not Lean
declarations.

For `G3-O24`, Lean proves direct finiteness without choosing a matrix basis: multiplication by a
left inverse is surjective, finite dimension makes it injective, and cancellation yields the
reverse identity. Complete two-sided scalar-value contexts therefore cannot retain orientation.
For an arbitrary selected context set, zero equivalence also collapses when those contexts
separate elements up to nonzero scalar. Conversely, any context family distinguishing the
reverse product forces the forward product away from every nonzero scalar identity; an
asymmetric forward equivalence forces failure of global projective separation. The Lean theorem
does not assert that the directed S5 stable cone has this separation property.

For `R32-O22`, Lean proves every algebraic claim in the explicit obstruction: signed shear-word
evaluation, the power-of-three endpoint congruence, the CRT unit over composite moduli, an
all-positive-modulus projective hit, rational chamber inequalities, free-product injectivity,
trivial point stabilizer, and rational nonreachability. The strategic conclusion is confined to
the failure of residue-orbit nonmembership and of the corresponding all-congruence membership
criterion. It does not assert topological density at any local or adelic place, nor decide the
remaining Borel-coset shell.

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

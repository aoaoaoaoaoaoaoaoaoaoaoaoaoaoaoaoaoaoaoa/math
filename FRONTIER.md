# Matrix Mortality Frontier Campaign

Established-result ledger and dimension-two research audit: 2026-07-24. A question mark means
“not resolved by any valid result found in the present literature audit,” not an assertion that
no unpublished argument exists.

Reusable lemmas, obstructions, certificates, and partial mechanisms from unsuccessful attacks
are indexed in [`SALVAGE.md`](SALVAGE.md). Its evidence labels are authoritative; this file
records only their strategic consequences.

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

## Cross-problem consequences

The source representation, paired-role quotient, and shared-channel binary compiler establish
the Pareto-minimal scalar points

```text
Z₃(4), Z₄(3), Z₆(2).
```

CHHN's scalar-to-corner reduction gives

```text
R₃(5), R₄(4), R₅(3), R₇(2).
```

The structured forms `Z̊₃(4)`, `Z̊₄(3)`, and `Z̊₆(2)` have common first column `e₁`. The
six-state binary compiler supersedes the earlier `Z₇(2)` packing consequence; its corner lift
similarly supersedes `R₈(2)`.

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

## The paired-role compiler

In the side-normal word-pair representation, Neary's rule and erasure matrix for a fixed tag
letter agree on the two-dimensional upper-word plane. On two three-dimensional phase spaces,
the anti-diagonal copy of this plane can therefore be quotiented out. Two data generators and
one suffix-phase toggle act on the resulting four-dimensional space. Every control word decodes
to a four-role word, and every four-role word has an encoding.

This gives structured `Z̊₄(3)`. Adding the established outer-product separator gives `M₄(4)`;
the arbitrary-product converse uses the controls' common fixed column instead of nonsingularity.
The machine-checked implementation is in `PairedCompression.lean` and `PairedMortality.lean`.
A public-literature search through 2026-07-22 found no earlier `Z₄(3)`, `M₄(4)`, paired-role
decoder, or common-column mortality converse. The quotient itself and the rank-one separator
are prior art; see `audits/m44-prior-art-2026-07-22.md`.

## The binary compilers

The four-role alphabet factors as a rule/deletion bit and a tag-letter bit. A two-bit decoder
therefore needs one complete three-coordinate state and one partial state. Rule and deletion
share the partial upper channel, reducing the generic partial state to three coordinates. The
resulting two `6×6` integer matrices preserve the source coefficient on every binary word; an
odd final bit preserves the coefficient, and reversed block encoding is surjective. Transpose
and word reversal give structured `Z̊₆(2)`.

A second binary compiler exploits the stroke schedule rather than role factorization. At fixed
deletion width `β`, position modulo `β` determines whether the selected tag letter acts as a
deletion or a rule. Two `(β+2)×(β+2)` integer matrices then preserve the source coefficient on
every binary word. Reversed stroke encoding is surjective, and a zero coefficient forces a
complete tile history; incomplete clock cycles cannot create witnesses. At `β=3`, the native
series has exact rational rank five for every nonempty body. These claims are formalized in
`ScheduledBinary.lean` and `ScheduledBinaryRank.lean`; see
[`MM-C03`](SALVAGE.md#mm-c03-scheduled-binary-compiler) and
[`MM-O05`](SALVAGE.md#mm-o05-width-three-scheduled-rank).

This does not add a frontier point. Neary's universality compiler sets `β=10p`, with `p` the
cyclic-tag program period. The fixed-width audit found no universality theorem for the required
binary deletion-width-three family. At width three the construction would imply `Z₅(2)`,
`M₅(3)`, and `R₆(2)`; at the presently established variable width it gives no fixed matrix
dimension. See `audits/scheduled-binary-fixed-width-2026-07-24.md`.

Full mortality requires coding the four payloads and the rank-one separator. The complete
prefix code

```text
0, 100, 101, 110, 111
```

has four prefix states and gives a `12`-state deterministic matrix transducer. The word `00`
synchronizes all start states. Paired-role agreement supplies two common left annihilators, so
both binary generators have image in one integral `10`-dimensional subspace. Restriction to that
image is exact. If a restricted product is zero, appending `0` gives a zero `12`-state product;
restriction therefore introduces no false mortality witness. This proves `M₁₀(2)`, and zero
padding gives `M_d(2)` for every `d≥10`.

Both compilers and their arbitrary-word converses are machine-checked in `PairedBinary.lean`,
`WeightedTransducer.lean`, and `PrefixMortality.lean`. A public-literature search through
2026-07-24 found no earlier `Z₆(2)`, `R₇(2)`, or `M₁₀(2)`. Binary coding and generic alphabet
reduction are prior art; the priority claims concern the shared-channel and common-image
constructions.

## Current mortality staircase

After terminal absorption, paired-role compression, binary compilation, dimension padding, and
CHHN's generator–dimension trade, the established Pareto-minimal undecidable points are

```text
M₃(5), M₄(4), M₆(3), M₁₀(2).
```

The unknown cells immediately below this staircase are:

| Cell | What would suffice | Automatic reward |
| --- | --- | --- |
| `M₃(4)` | three-active-role fixed-boundary PCP / `GPCP(3)`, or a new same-dimension generator compiler | by CHHN, also `M₉(2)` |
| `M₅(3)` | a five-state binary same-zero root, a toggle/separator fusion, or fixed-width-three scheduled universality | supersedes `M₆(3)`; `M₁₀(2)` is already known |
| `M₉(2)` | a zero-set-preserving compiler not obtained by restricting the exact ten-state binary decoder | improves the two-generator threshold by one |
| `M₂(k≥3)` | a qualitatively different decidability or undecidability argument | settles the dimension-two wall |

The scalar result `Z₆(2)` gives `M₆(3)` after adjoining a separator; that mortality point was
already obtained from `M₃(5)` by CHHN packing.

## Ranked attacks

### 1. Zero-set compression and fused punctuation: `M₅(3)`

The literal CHHN packing has no common invariant line or hyperplane. The all-placement
certificate [`MM-O01`](SALVAGE.md#mm-o01-all-placement-packing-rank) further reports that its
selected coefficient series has exact Hankel rank six. Once audited, this closes exact
minimization of that packing in five states.

The paired four-state scalar system closes a second exact route. Its coefficient series has
uniform Hankel rank four
([`MM-O04`](SALVAGE.md#mm-o04-uniform-rank-four-paired-series)), while the two-channel boundary
tax [`MM-O03`](SALVAGE.md#mm-o03-two-channel-boundary-tax) charges two additional states to an
exact diagonal rank-two bridge. Such a bridge therefore also requires dimension at least six.
Both conclusions concern exact series; neither constrains another series with the same zero set.

Three live routes remain.

1. Construct a five-state binary series with nonsingular letter matrices, the source zero set
   on complete two-bit blocks, and nonzero values on odd words; then adjoin the ordinary
   rank-one separator. The unused identity `(V_b^D,B_b^D)=(V_c^D,B_c^D)` suggests processing
   the common deletion channel before the symbol bit is known. A four-state root would prove
   the stronger `M₄(3)` result.
2. Fuse the paired toggle and separator inside one five-dimensional generator. The
   off-diagonal companion interface
   [`MM-M01`](SALVAGE.md#mm-m01-off-diagonal-companion-interface) supplies a complete bridge
   grammar once a physical control word realizes it. The bordered-toggle mechanism
   [`MM-M02`](SALVAGE.md#mm-m02-bordered-toggle) supplies a rank-two stable third power, but
   mixed `S²` runs and malformed selector placements remain unresolved.
3. Use the scheduled compiler [`MM-C03`](SALVAGE.md#mm-c03-scheduled-binary-compiler).
   A fixed binary deletion-width-three universality theorem would finish the reduction
   immediately. None was located. The constructive alternative is to replace the variable
   phase clock by a constant-state delimiter or punctuation mechanism and prove that every
   malformed placement is excluded by the terminal-match normal form. The width-three
   rank-five theorem [`MM-O05`](SALVAGE.md#mm-o05-width-three-scheduled-rank) shows that five
   exact states are necessary at that width; it does not obstruct a same-zero clock
   compression or delimiter fusion.

The next bounded expert audit targets scheduled delimiter fusion and its all-word converse.
The next internal calculation remains a symbolic classification of fifth-coordinate couplings
and their maximal-run grammar. Further benchmark enumeration cannot settle these routes.

### 2. Two-generator realization: `M₉(2)`

The complete prefix decoder has a common image of dimension exactly ten for the present source:
its common left annihilator has dimension two, and the restricted pair has no common right
kernel. No further image restriction or kernel quotient of this decoder reaches nine states.

The surviving route may preserve only the zero set. It must use a different transducer
skeleton, change nonzero values, or exploit a source identity beyond paired upper-channel
agreement. A literal binary prefix tree for five source symbols has four internal states, so a
nine-state construction cannot retain a complete three-dimensional source state at every
prefix.

### 3. Three-letter correspondence and direct mortality: `M₃(4)`

The public-literature audit through 2026-07-24 found no resolution of `GPCP(3)` or
`M₃(4)`. The two targets should not be conflated.

```text
GPCP(3) undecidable
        ⇒ Z₃(3)
        ⇒ M₃(4).
```

The converse is absent. A direct mortality proof may change every nonzero coefficient, use
singular ideals or projective incidence, or abandon word-pair morphisms altogether. Classical
GPCP must still express equality of two free-monoid morphisms with fixed boundaries. This
strict containment of proof obligations is the sound reason to rank a direct `M₃(4)` attack
above a genuine `GPCP(3)` theorem. The numerical probabilities in the exploratory
pre-mortem are not evidence and are not retained.

The foundational reward points the other way. `GPCP(3)` would immediately yield

```text
Z₃(3), M₃(4), R₃(4), R₄(3), Z₅(2), R₆(2), M₉(2),
```

through the standard scalar, corner, mortality, and packing reductions. A direct mortality
construction certifies only `M₃(4)` and its mortality packing consequences unless it carries
an additional scalar interpretation.

#### Closed exact routes

The present four roles are

```text
R_c = initialization / c-rule,       R_b = b-rule,
D_b = deletion of b,                 D_c = deletion of c.
```

Two broad compressions are now excluded.

The exact nonerasing macro obstruction
[`G3-O01`](SALVAGE.md#g3-o01-four-role-macro-irreducibility) proves that no
fixed rolewise macros over three source letters reproduce these four word pairs exactly.
Unequal macro lengths, noninjective role codes, and failure of prefix-freeness do not help.
A surviving compiler must use erasure, target recoding, boundary or context residuals,
overlap, solvability-only preservation, or a different source.

The body-independent Hankel certificate
[`MM-O04`](SALVAGE.md#mm-o04-uniform-rank-four-paired-series) proves that the
current three-control paired coefficient series has exact rank four already on `{b,t}*`.
Similarity, exact quotient or restriction, and nonzero per-letter rescaling cannot produce a
three-state realization. A surviving matrix route must change the nonzero values and preserve
only the zero language, or replace the compiler.

The fixed-first property also remains useless: `R_c` recurs whenever the `c` rule fires.
Absorbing its initial occurrence does not remove its interior role.

#### Structural lower boundary

The decidable two-letter endpoint is not merely a failed search for universality. Binary
equality sets of non-periodic morphisms are generated by at most two words, with strong
first- and last-letter separation in rank two
([Holub](references/holub-2012-binary-equality-sets.md)). Binary GPCP admits the
beginning-block, end-block, successor, and reduction-tree analysis developed by Halava and
Holub. Marked GPCP is decidable
([Halava–Harju–Hirvensalo](references/halava-harju-hirvensalo-1999-marked-gpcp.md)).

These theorems delimit a ternary construction. It must generate residual ambiguity absent
from the binary successor tree, and it cannot become marked after recoding. Hadravová's
historical account also records regularity of ordinary ternary equality sets as open; that
homogeneous question is not itself fixed-boundary `GPCP(3)`, but it confirms that the jump
from two source letters has resisted the standard equality-set theory.

The conventional few-rule route pays a fixed tax. Nicolas proves

```text
ACCESSIBILITY(k) undecidable ⇒ GPCP(k+2) undecidable.
```

Matiyasevich and Sénizergues supply undecidable three-rule accessibility, hence `GPCP(5)`.
Through this compiler, `GPCP(3)` would require an undecidable one-rule accessibility source.
A useful rewriting attack must therefore either find a tighter compiler or build a
computational source whose certificate has three morphism schemas natively. A machine with
three symbol types but many transition rules does not meet this count.

#### Research lanes

| Lane | Available leverage | Decisive obstruction or obligation |
| --- | --- | --- |
| Shift-equivariant zero incidence | Same-zero dimension three is point-line incidence in `P²`, formalized by [`G3-S01`](SALVAGE.md#g3-s01-shift-equivariant-zero-incidence) | Finite minimum rank is insufficient; all prefixes and suffixes must share three common shift maps over `ℚ` |
| Inverse-transducer discrepancy | Free cancellation performs queue-head deletion and Carvalho proves an all-path fixed-loop converse; see [`G3-M01`](SALVAGE.md#g3-m01-free-group-discrepancy-engine) | The closed-path subgroup has instance-dependent rank; inverses, free reduction, and subgroup control must be compiled into three positive letters |
| Context and sliding-block codes | Adjacent ternary symbols can carry four semantic roles without fixed role macros | GPCP quantifies over the full free monoid; every boundary fragment, phase shift, and invalid overlap must be algebraically harmless |
| Erasure and target recoding | Erasure escapes `G3-O01`; longer target atoms can split the one-letter images used in its proof | Empty contributions and code fragments create new boundary matches unless a global normal form excludes them |
| New three-schema rewriting source | Bi-tag, cyclic-tag, Lag, queue, and small semi-Thue systems separate data motion from finite control | Count transition schemas, not data symbols; the program table must live in boundaries or target words without adding source letters |
| Exclusive stochastic or affine recognition | Zero/nonzero languages can be much smaller than exact coefficient series | Affine normalization, quantum measurement, and finite pair separation are not raw integer scalar-zero representations |
| Direct projective or affine dynamics | Three `3 × 3` controls can encode switched dynamics on two homogeneous coordinates | Unguarded matrix choice demands an irreversible checksum for every illegal branch |
| Semigroup ideals and reset structure | Rees or Brandt incidence can make incompatible phases fall into a zero ideal | Natural representations usually spend dimension on control states; the full arbitrary-product grammar remains mandatory |

The first, sixth, seventh, and eighth lanes principally target direct `M₃(4)`. The third,
fourth, and fifth can produce a genuine `GPCP(3)` theorem. The free-group lane is hybrid:
it supplies the missing deletion semantics but not yet the bounded positive source.

#### Operational program

The highest-yield direct experiment is not another exact minimization. For increasing finite
prefix and suffix sets, solve over `ℚ` for

```text
r_x, c_y ∈ ℚ³,       T_a ∈ ℚ^(3×3),
r_x c_y = 0  ↔  f(xy)=0,
r_{xa}=r_xT_a,       c_{ay}=T_ac_y.
```

The shift equations must be present from the first solve. Persistent solutions may expose a
same-zero compiler; a finite unsatisfiable core may become a genuine zero-language
dimension obstruction.

The highest-yield source experiment is Carvalho's smallest cyclic-tag transducer. Compute
the rank and Stallings graph of its closed-path subgroup, classify the formal inverses used
by the fixed-loop proof, and test whether a rank-three positive basis or boundary-controlled
subgroup language survives. In parallel, search ternary finite-delay codes whose decoder is
total on all words, not merely correct on an intended subshift.

No further local fusion of the four displayed pairs should be attempted without identifying
which escape clause of `G3-O01` it uses.

## The dimension-two wall: `M₂(3)`

### Status and exact hard core

The public-literature audit through 2026-07-24 found neither a decision algorithm nor an
undecidability proof for `M₂(3)`. The case is equivalent to point-to-point reachability on
`P¹(ℚ)` under two rational Möbius transformations; the reusable reduction is
[`D2-S01`](SALVAGE.md#d2-s01-projective-hard-core).

Let `X₁⋯Xₙ=0` be a mortal word of minimal positive length over `2×2` matrices. Its first and
last factors are singular: an invertible endpoint could be cancelled. Every interior factor is
nonsingular. Indeed, if an interior factor is `uvᵀ`, then

```text
0 = P(uvᵀ)Q = (Pu)(vᵀQ)
```

forces either `Puvᵀ=0` or `uvᵀQ=0`, producing a shorter mortal word.

For an input of at most three matrices this leaves one unresolved rank pattern: two
nonsingular matrices `A,B` and one nonzero singular matrix `R=cr`. Every minimal witness then
has the form

```text
R W R,       W ∈ {A,B}*,
```

and

```text
R W R = c(rWc)r.
```

Consequently,

```text
M₂(3)  ≡  given A,B ∈ GL₂(ℚ), r≠0, c≠0, decide ∃W∈{A,B}*: rWc=0.
```

After projectivization this asks whether the submonoid generated by `A,B` sends `[c]` to
`P(ker r)`. If `rc=0`, the empty interior already gives `R²=0`; otherwise a rational change of
basis turns the condition into a zero in one fixed matrix corner. Clearing denominators and
independently rescaling the three generators preserves zero products, so the rational incidence
problem and integer mortality are computably interreducible.

The reduction has only one incidence instance. Multiple endpoint pairs arise for larger
families with several singular generators, not in the hard three-generator case.

### Established and provisional decidable strata

The established baseline consists of two-generator `2×2` mortality, the at-most-one-nonsingular
preprint result, the `GL₂(ℤ)` reachability algorithms, and one-dimensional integral-affine
reachability. The project-derived extensions are indexed with their exact evidence and scope:

- projectively unimodular pairs:
  [`D2-D01`](SALVAGE.md#d2-d01-projectively-unimodular-stratum);
- groups preserving an unordered projective pair:
  [`D2-D02`](SALVAGE.md#d2-d02-invariant-pair-stratum);
- affine maps with a common rational multiplier:
  [`D2-D03`](SALVAGE.md#d2-d03-common-multiplier-stratum);
- rational subsets of one single-base affine group:
  [`D2-D04`](SALVAGE.md#d2-d04-single-base-affine-stratum).

Only `D2-D01` has passed an independent project audit. The remaining three are research stock,
not publication theorems.

Simultaneous triangularization alone is not a solved stratum. It yields rational affine
reachability

```text
z ↦ a_i z+b_i,
```

whose general two-map case remains part of the wall. The provisional common-multiplier and
single-base theorems cover substantial subfamilies but do not settle mixed multiplicative
directions.

### Exact unresolved residue

Two qualitatively different classes remain after the preceding tests.

#### Mixed-prime affine systems

These have a common rational fixed point but genuinely independent multiplier valuations, for
example

```text
z ↦ (2/3)z+1,       z ↦ (3/5)z+1.
```

The slopes are neither integral, equal, powers of one rational base, nor elements of one
`{±qⁿ}` group. This is already a two-map, one-dimensional, virtually solvable residue.

#### Non-elementary projective systems

Here the generators have no common rational eigenline and preserve no unordered pair of
projective points. They are not projectively unimodular and need not generate a free monoid.
The problem becomes intersection of the positive rational subset

```text
⟨A,B⟩⁺
```

with a rational parabolic coset carrying the source point to the target.

These two residues should be attacked separately. A theorem for the affine class need not
touch the non-elementary case.

### False shortcuts

| Temptation | Failure |
| --- | --- |
| Apply fixed-target matrix membership | the incidence variety contains matrices of unbounded determinant |
| Invoke flat rational-subset algorithms | `(A+B)*` permits unbounded alternation and need not be flat |
| Declare triangular systems decidable | rational affine reachability remains unresolved outside special strata |
| Treat arbitrary words as one recurrence | word order is stored by a two-state rational series, not one exponent |
| Use a free subgroup normal form | the input generators may satisfy relations such as `A³=B²` |
| Import the standard PCP encoding | two independent free-word tapes do not embed in `2×2` complex matrices |
| Track only determinant or Smith form | equal arithmetic invariants can have different projective orbits |
| Assume projective height descends | determinant-growing words may act projectively as the identity |

These are exclusion tests for future proposals. Any attack relying on one of them must identify
the additional hypothesis that repairs the failure.

### Pre-mortem: imported structural principles

The following is a research-prior allocation, not evidence for either outcome. Condition on
`M₂(3)` being resolved by an imported structural theorem rather than a local extension of
mortality machinery:

```text
Pr(decidable | imported resolution)   ≈ 0.80
Pr(undecidable | imported resolution) ≈ 0.20.
```

| Primary source of the decisive lemma | Credence | Outcome allocation |
| --- | ---: | ---: |
| `S`-arithmetic geometry, Bruhat–Tits trees, reduction theory | 21% | 20% decidable, 1% undecidable |
| Numeration systems, continued fractions, finite-state transducers | 17% | 12% decidable, 5% undecidable |
| Metabelian groups, Laurent modules, `S`-unit equations | 15% | 13% decidable, 2% undecidable |
| Rational subsets, Bass–Serre theory, parabolic-coset algorithms | 12% | 10% decidable, 2% undecidable |
| `SL₂` trace algebras, character varieties, Markoff descent | 9% | 8% decidable, 1% undecidable |
| Arithmetic dynamics, height gaps, Subspace-Theorem methods | 8% | 7% decidable, 1% undecidable |
| Verification, well-structured systems, affine-loop acceleration | 6% | 5% decidable, 1% undecidable |
| Profinite topology, congruence separation, automatic structures | 5% | 5% decidable |
| FRACTRAN, Collatz systems, automaton-semigroup universality | 6% | 6% undecidable |
| Other structural sources | 1% | predominantly undecidable |

The percentages are coarse hypothesis weights. They are intended to force diversity in the
next prompt battery, not to rank theorem credibility.

### Independent attack lanes

Dispatch each lane as a standalone investigation. It must conduct its own deep literature
review, attack the full incidence problem rather than merely survey it, state the strongest
proved import it finds, and identify an explicit falsifier for its proposed mechanism. Synthesis
comes only after the independent reports return; shared vocabulary must not collapse genuinely
different hypotheses into one generic prompt.

#### 1. Adelic parabolic reduction

Let `S` be the primes appearing in denominators and nonunit determinants. Study the simultaneous
action on the real hyperbolic plane and the Bruhat–Tits trees `T_p`, `p∈S`. The desired theorem
is an effective finite cone-type decomposition relative to a rational parabolic, with the
unbounded part carried by decidable Busemann counters. The critical obstruction is
synchronization across several primes.

The first falsifier is a pair whose simultaneous Busemann coordinates simulate an unrestricted
two-counter system. The first positive certificate is a bounded-cancellation or induction
theorem reducing one bad prime at a time.

#### 2. Redundant projective numeration

Represent rational points by continued fractions, Stern–Brocot addresses, or redundant
signed `S`-adic expansions. Search for a representation in which both Möbius generators have a
common finite carry nucleus. Canonical expansions are not privileged; the single-base pointed
expansion for `BS(1,q)` is evidence that annotation can turn nonregular arithmetic into a
regular language.

The decisive experiment is to compare reachable carry-state growth for ordinary continued
fractions, slow continued fractions, Stern–Brocot paths, and redundant multi-prime expansions.

#### 3. Characteristic-zero affine modules

For triangular systems, express the translation component as a module element over the
multiplicative slope group. The target theorem is decidability of cyclic-coset reachability in
a rank-one characteristic-zero module-by-abelian group generated by two affine maps. Minimal
`S`-unit relations, Laurent-module normal forms, or effective semilinearity are the likely
invariants.

The mixed-prime pair `(2/3,3/5)` is the benchmark. A method that cannot decide it has not crossed
the affine residue.

#### 4. Rational subsets and relative normal forms

Seek an algorithm deciding intersection of a positive rational subset of a two-generated
subgroup of `PGL₂(ℚ)` with a rational parabolic coset. Candidate imports are Bass–Serre
decompositions, relative automatic structures, and rational-subset closure theorems for graphs
of groups with affine edge or vertex groups.

This lane should target arbitrary regular control languages. Success only for bounded
alternation reproduces the existing flat theory.

#### 5. Trace or height descent

Exploit the dimension-four algebra generated by two `2×2` matrices, Fricke trace identities,
and Nielsen transformations. Enlarge trace data by the boundary coefficients

```text
rc, rAc, rBc, rABc
```

and search for a mutation or height that strictly descends for every minimal zero word outside
an elementary locus. Arithmetic-dynamics variants may instead prove a computable bound on
normal-form length.

Raw word length is not a lawful height: relations can make long words represent short group
elements.

#### 6. Exact symbolic saturation and finite obstructions

Run backward saturation from the target using cones, valuation vectors, residue classes, and
affine lattices. A successful well-structured formulation must decide exact reachability, not
only coverability. In parallel, test whether no-instances are separated by a finite congruence
quotient. Congruence separation would provide enumerable finite certificates for “no.”

Persistent local-global failures modulo every tested modulus would falsify the profinite route.

#### 7. Valuation universality

For undecidability, encode configurations in prime valuations or disjoint `p`-adic cylinders.
The two Möbius generators must be total, so illegal instructions require irreversible geometric
traps rather than external guards. A valid proposal must include the arbitrary-word converse:
every accidental incidence must decode to a legal computation.

Single-base affine encodings and common-multiplier digit systems are excluded by the decidable
strata above. A plausible construction must use mixed valuation directions or a non-elementary
projective action.

### Discriminating signals

- Arbitrary regular control favors rational subsets, buildings, numeration, or module automata.
- A theorem for any finite generator set favors adelic or automatic structure over
  two-letter combinatorics.
- A theorem confined to two named generators favors trace descent, continued-fraction
  transducers, or a two-map universality construction.
- Nonelementary complexity with a finite-state core favors building automata, `S`-unit
  equations, or Presburger saturation.
- Semilinear no-certificates favor affine modules or verification.
- Finite-modulus no-certificates favor profinite separation.
- A computable witness bound favors height, Diophantine, or trace descent.
- A virtually-solvable/non-elementary dichotomy favors arithmetic dynamics.
- An undecidability construction with several prime determinants favors valuation storage.

### Composite proof shapes

The modal decidability route combines the adelic, numeration, and rational-subset lanes:

1. encode the action at every bad prime by finitely many cone types, Busemann coordinates, and
   carry states;
2. construct an effective regular or automatic normal form closed under rational control and
   parabolic cosets;
3. recognize the coset of transformations carrying the source point to the target and decide
   intersection.

The principal fallback first solves the mixed-prime affine residue by a characteristic-zero
Laurent-module theorem, then uses a normal-form height or cancellation theorem on the
non-elementary residue. The modal undecidability route instead requires a genuinely multi-prime
`p`-adic transducer with invariant configuration cylinders, irreversible traps for illegal
choices, and a complete arbitrary-word converse.

The highest-value intersection is

```text
S-arithmetic parabolics
+ annotated numeration systems
+ rational-subset automata.
```

The concrete question is whether the pointed-expansion phenomenon for one affine base extends
to a synchronized finite family of primes, or whether that synchronization already supports
universal computation.

## Execution order

1. Audit and formalize `MM-O01`, `MM-O03`, `MM-O04`, and `G3-O01`; keep exact-series and
   exact-macro scope explicit.
2. Attack the three surviving `M₅(3)` routes: a five-state same-zero binary root, a
   five-dimensional toggle/separator fusion with a complete maximal-run grammar, and
   constant-state scheduled delimiter fusion. Treat fixed-width-three universality as a
   separate source theorem, not as an assumed compiler property.
3. Search for a zero-set-preserving `M₉(2)` compiler rather than another invariant restriction
   of the exact ten-state decoder.
4. Run the `M₃(4)` program on three separate tracks: shift-equivariant point-line synthesis,
   the closed-path subgroup of Carvalho's smallest transducer, and total ternary
   synchronization codes. Do not collapse their distinct proof obligations into one prompt.
5. Fan the `M₂(3)` chapter into independent attacks on adelic cone types, redundant
   numeration, characteristic-zero affine modules, parabolic rational subsets, trace/height
   descent, finite-obstruction saturation, and valuation universality.
6. Synthesize the returned attacks by the discriminating signals above; do not average
   incompatible hypotheses into one generic mortality prompt.

These are research programs, not consequences of the present theorem.

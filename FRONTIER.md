# Mathematics Frontier Campaign

Established-result ledger and dimension-two research audit: 2026-07-25. A question mark means
“not resolved by any valid result found in the present literature audit,” not an assertion that
no unpublished argument exists.

Reusable lemmas, obstructions, certificates, and partial mechanisms from unsuccessful attacks
are indexed in [`SALVAGE.md`](SALVAGE.md). Its evidence labels are authoritative; this file
records only their strategic consequences.

## Frankl abundance frontier

The current formal theorem is

```text
t=38234553336670271/10^17,
α=356069804374481/10^16,
ε=10⁻¹⁸.
```

Lean proves both the finite affine Yu inequality and its entropy bridge to every finite
nontrivial union-closed family. The endpoint proof now uses a support-aware analytic contraction
on the whole high-`a` rectangle. The `q=1` edge is dominated analytically by the diagonal
endpoint `q=a`; static replay remains only on the low rectangle. The publication theorem is
`Frankl.unionClosed_exists_abundant_coordinate`.

This is an explicit, fully kernel-checked improvement over the published AHS constant
`(3−√5)/2`. An independently audited centered-endpoint factorization gives an upper wall

```text
0.38234553336670272114599300 < c⋆ < 0.38234553336670272114599301
```

for every affine mixture of the independent and max-entropy couplings. The Lean target lies
between `11×10⁻¹⁸` and `12×10⁻¹⁸` below this wall. Cambie's reported last digits were slightly
high; the corrected obstruction explains his numerical optimizer. Liu's conditional
`0.382709087…` candidate belongs to a stronger conditionally IID architecture. Priority
language must keep the kernel theorem, the audited wall, and conditional numerical values in
their distinct epistemic categories.

The next live attacks are:

1. Import Liu's conditionally IID gain without assuming the infinite-kernel PSD statement or the
   reported optimizer shape. A finite exact positivity decomposition would give genuine room
   beyond the exhausted two-coupling wall.
2. Search for a third coupling or a nonlinear entropy combination whose local objective is
   strictly positive on the wall witness `y⋆`. The exact factorization in `FC-O04` is now a cheap
   falsification test for every proposed extension.
3. Replace the infinite-kernel step by a finite target-dependent certificate: truncate with a
   proved tail bound, derive a sum-of-squares or moment representation, and feed only the final
   finite positivity statement into Lean.
4. Formalize the exact real wall only if it supports one of those attacks. The rational theorem
   already resolves the decimal ratchet to less than `1.2×10⁻¹⁷`; more digits inside the same
   architecture have negligible mathematical value.
5. On the counterexample side, use the exact blocker-pivot normal form `FC-S14`: try to couple
   its local pivot stars to the global deletion-bias inequalities by a double count. The proposed
   inflated-`B₃` picture is only a heuristic and does not merit blind enumeration absent that
   coupling inequality.

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
`MatrixMortality/NearyEncoding.lean`. The fixed universal machine, Cocke–Minsky compiler,
one-hot cyclic compiler, Table 2 implementation, arbitrary-execution converse, primitive-recursive
target constructors, many-one reductions, and no-decider theorems are formalized through
`MatrixMortality/Undecidability/UniversalNeary.lean`. Neary's Lemma 9 is historical provenance,
not a proof premise.

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
dimension. The sparse source stratum is now closed:
[`MM-D01`](SALVAGE.md#mm-d01-sparse-width-three-source-decision) proves that every coupled body
containing at most one `c` halts, so any exact universal family must emit a body with at least
two `c` letters on some rejecting code. This is a necessary condition, not universality of the
two-`c` stratum. The one-`c` shrinking-defect mechanism is sharp for unrestricted queue
dynamics: [`MM-S23`](SALVAGE.md#mm-s23-adjacent-two-c-periodic-pair) constructs two exact
periodic queues for every nontrivial even adjacent-two-`c` body. However,
[`MM-D02`](SALVAGE.md#mm-d02-adjacent-two-c-source-decision) proves that every coupled initial
queue in this adjacent subfamily either halts or enters the lower cycle. The unresolved
two-`c` source boundary therefore begins with separated `c` letters. See
`audits/scheduled-binary-fixed-width-2026-07-24.md` and
`audits/m53-width-three-sparse-source-2026-08-30.md`; the adjacent-cycle proof is in
`audits/m53-width-three-adjacent-cycles-2026-08-31.md`. The separated seam now has one exact
internal boundary: for every `n>0` with
`n mod 3≠2`, the coupled body `bb c bⁿ c bⁿ` enters a periodic nonhalting orbit
([`MM-S25`](SALVAGE.md#mm-s25-separated-two-c-periodic-orbits)). This infinite separated
two-`c` obstruction is not a source classification. The same diagonal family halts throughout
`n≡8 (mod 9)` by [`MM-S30`](SALVAGE.md#mm-s30-separated-residue-eight-drainage). The exact
active-pair quotient in
[`MM-S34`](SALVAGE.md#mm-s34-separated-residue-five-cantor-drainage) proves halting throughout
`n≡5 (mod 9)` by conjugating the live defect to an injective inverse-Cantor map on a finite
interval. [`MM-S41`](SALVAGE.md#mm-s41-separated-residue-two-first-cut) resolves two of the
three subresidues of the last class by an exact six-event macro: `n≡2,20 (mod 27)` halt.
[`MM-S43`](SALVAGE.md#mm-s43-four-c-reproduction-cut) identifies the survivor's canonical
four-`c` reproduction macro and proves `n≡11 (mod 81)` halts.
[`MM-S48`](SALVAGE.md#mm-s48-centered-four-c-extinction) closes its one/two-block dynamics by
an injective centered-division quotient. Thus every diagonal source with `n≡2 (mod 3)` halts,
while `MM-S25` gives periodic nonhalting orbits in the other residues for `n>0`; `MM-S48`
also checks the degenerate `n=0` cycle.
[`MM-S58`](SALVAGE.md#mm-s58-unequal-two-c-cycle-law) then leaves the diagonal: every positive
even body `bᵖ c bʳ c bˢ` with `r≢2 (mod 3)` has the exact canonical cycle
`c b^(s+(p+r+s)/2+1)`. For the sheared plane
`p=3t+2`, `r=n+t`, `s=n`, the coupled initial queue reaches that cycle, so every such source
off middle phase two is nonhalting. This is an exact unequal-run cut, not a classification of
arbitrary triples. [`MM-S70`](SALVAGE.md#mm-s70-sheared-residue-eight-drainage) enters the
excluded phase: when `r≡8 (mod 9)` and `t≢2 (mod 3)`, an exact four-active-`c` history reaches
a head-clean queue, so the coupled source halts.
[`MM-S72`](SALVAGE.md#mm-s72-sheared-residue-twenty-six-drainage) penetrates the remaining
shear phase: `r≡26 (mod 27)` and `t≡2,5 (mod 9)` halt after an exact ten-active-`c` history.
[`MM-S75`](SALVAGE.md#mm-s75-matched-six-c-shear-drainage) gives the complementary short
macro: for `e=0,1`, the matched pair `r=9k+3e+2`, `t=3u+e` halts whenever
`k+2u+2e+2` is nonzero modulo three.
[`MM-S78`](SALVAGE.md#mm-s78-phase-mismatched-six-c-drainage) cuts all four remaining
phase-mismatched residue pairs. The complementary pair `t+e=3u+1` halts when
`k+u≡2 (mod 3)`; the shear-residue-two pair `t=3u+2` halts when `u≡e (mod 3)`. Each failed
class reaches an exact six-event residual with one active `c` pair, but no theorem yet closes
those successors.
All cuts are checked in
`MatrixMortality/SeparatedTwoCShear.lean`. The diagonal audit trail is
`audits/m53-separated-two-c-orbits-2026-08-31.md`,
`audits/m53-separated-two-c-residue-eight-2026-08-31.md`,
`audits/m53-separated-two-c-residue-five-2026-08-31.md`, and
`audits/m53-separated-two-c-residue-two-2026-08-31.md`; the four-`c` refinement and closure are
in `audits/m53-separated-two-c-four-c-2026-08-31.md` and
`audits/m53-separated-two-c-diagonal-complete-2026-08-31.md`.

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

After terminal absorption, paired-role compression, binary compilation, changed-separator return
compression, dimension padding, and CHHN's generator–dimension trade, the established
Pareto-minimal undecidable points are

```text
M₃(5), M₄(4), M₆(3), M₉(2).
```

The unknown cells immediately below this staircase are:

| Cell | What would suffice | Automatic reward |
| --- | --- | --- |
| `M₃(4)` | three-active-role fixed-boundary PCP / `GPCP(3)`, or a new same-dimension generator compiler | replaces `M₃(5)` and `M₄(4)` on the staircase; CHHN's `M₉(2)` corollary is already known |
| `M₄(3)` | an undecidable promised two-state overlap queue with pure deletion, or closure of either parabolic bridge language | by CHHN, also `M₈(2)` |
| `M₅(3)` | a five-state binary same-zero root, a toggle/separator fusion, or fixed-width-three scheduled universality | supersedes `M₆(3)`; `M₉(2)` is already known |
| `M₂(k≥3)` | a qualitatively different decidability or undecidability argument | settles the dimension-two wall |

The scalar result `Z₆(2)` gives `M₆(3)` after adjoining a separator; that mortality point was
already obtained from `M₃(5)` by CHHN packing.

## The hard stratum

The completed improvements all preserve enough exact structure to admit a finite decoder:
boundary absorption, common-channel quotients, fixed-width clocks, prefix transducers, and
common-image restriction. Their arbitrary-word converses assign every free-monoid word a
controlled interpretation. The remaining cells begin where that program pays an unavoidable
state or generator tax.

Three obstructions recur.

1. **Exact behavior costs dimension.** Hankel certificates block further exact minimization;
   shared-channel phase compilers admit only low-period scale signatures; literal prefix
   parsers retain too many live source coordinates.
2. **Closed syntax loses universality.** A finite self-contained token whose output is a word
   of complete tokens induces decidable deletion-one substitution. Constraining witnesses to a
   regular code language is unavailable because mortality quantifies over every word.
3. **The target predicate is weaker than the available representation.** Mortality needs only
   one zero product, scalar reachability only one zero coefficient, and projective incidence
   only one orbit hit. Exact coefficient preservation carries information the target never
   asks for, but discarding it makes malformed-word soundness the central theorem.

The internal-word sandwich compiler [`MM-C04`](SALVAGE.md#mm-c04-internal-word-sandwich-minimization)
qualifies this diagnosis. Exact invariant subquotients do not need a fresh malformed-word
proof when a physical low-rank repair word already exists: wrapping any quotient zero by that
word lifts it upstairs. Their obstruction is instead algebraic saturation. For the present
ten-state pair, [`MM-O08`](SALVAGE.md#mm-o08-full-algebra-prefix-pair) proves that the word
span is already the full matrix algebra.

Outside that exact-repair lane, the common problem remains **unbounded synchronization under
adversarial word choice with no explicit control-state budget**. A successful construction must
store semantic phase outside an ordinary finite closed parser: in an open suffix or tail
residue, free cancellation, a numerical carry, projective incidence, a semigroup ideal, or an
arithmetic normal form. The decidability side of `M₂(3)` asks for the dual result: prove that
this hidden state nevertheless admits an effective finite or semilinear description.

This changes the value of the frontier. The remaining cells are no longer principally missed
packings. They ask whether zero-set semantics, nonlocal residues, or arithmetic structure can
replace exact finite-state simulation.

## Ranked attacks

### 1. Two-state cancellation and open residues: `M₄(3)`

Victory means a checked many-one reduction to mortality of three integer `4 × 4` matrices,
including a nonempty witness, denominator clearing, and soundness for every matrix word. The
frontier now has two live trunks and four independently attackable nodes.

#### Closed source trunk: positive overlap queues

The generic pushout [`M4-C01`](SALVAGE.md#m4-c01-two-state-pushout-compiler) already compiles any
binary deterministic two-state scalar zero into two data matrices and one rank-one separator.
The new positive overlap-queue compiler
[`M4-C02`](SALVAGE.md#m4-c02-positive-overlap-queue-compiler) supplies an exact source seam. A
queue consumes its open head and appends `produce(q,x)`; four local positive frame identities
relate production to cancellation. Empty-state isolation and avoidance of one framed return then
give

```text
promised binary two-state overlap-queue acceptance
    ↔ mortality of three integer 4 × 4 matrices.
```

The converse is genuinely universal over positive words. Prefix causality either reconstructs
the whole queue trace or exposes an earlier genuine empty prefix; no block-language assumption
survives in the theorem.

[`M4-O11`](SALVAGE.md#m4-o11-pure-deletion-necessity) forces every long accepting instance to
spend one role on genuine open-front deletion. The independently audited deletion-scanner
normal form [`M4-S05`](SALVAGE.md#m4-s05-deletion-scanner-normal-form) exhausts the
remaining transition tables. All non-scanning tables are decidable; the framed-return promise
kills one scanner and leaves three kernels:

1. `Lₙ`, zero-framed binary context-2 Lag;
2. `Bₙ`, zero-framed reset scanning;
3. `C`, conjugate scanning with a nonempty periodic rule production.

The principal kernel is formalized at exact strength in
[`M4-C03`](SALVAGE.md#m4-c03-zero-framed-binary-two-lag-compiler). Its four productions are

```text
λ(00)=V,  λ(01)=W0ⁿ⁺¹,  λ(10)=U,  λ(11)=ε,
```

with initial word `10ⁿ`, accepting singleton `0`, isolation of every reachable singleton, and
avoidance of `10ⁿ⁺¹`. Lean proves literal step-for-step equivalence and composes it to `M₄(3)`.

This Lag node is retired by
[`M4-D01`](SALVAGE.md#m4-d01-zero-framed-binary-two-lag-decision). Without either promise,

```text
10ⁿ →* 0 ⇔ (n=1 ∧ U=ε) ∨ (V=ε ∧ U∈0*).
```

The complete backward cone of `10` and a forward `1`-containment invariant prove the formula in
Lean.

The reset node `Bₙ` is also retired by
[`M4-D02`](SALVAGE.md#m4-d02-zero-framed-reset-scanner-decision). If `U₀=0ʳ1V`, zero-run
reduction contracts every postinitial rule boundary to the exact token system

```text
ε ↦ S,     aX ↦ XaS,     bcX ↦ XQ,     b ↦ accept.
```

When `W` contains `1`, only `S=b` accepts. When `W∈0*`, `Q=ε` and pair deletion decides
acceptance by the regular language `(101|11)*10`. This proof also uses neither promise.

The final periodic-conjugate node `C` is retired by
[`M4-D03`](SALVAGE.md#m4-d03-periodic-conjugate-scanner-decision). A finite first-return
calculation eliminates every case except the unary-zero frame. Primitive conjugacy then reduces
that residue to at most `#₁(K)` odd-gap tests in `K²`; a monotone block counter proves that no
later phase can accept first. This theorem uses the promised avoidance of `(R,A)`. All three
kernels in the exhaustive `M4-S05` normal form are therefore decidable, and the positive
overlap-queue source trunk is closed.

The direct Neary morphism is independently dead by
[`M4-O12`](SALVAGE.md#m4-o12-terminal-frame-morphism-obstruction): a morphism cannot send the
common terminal to `0` followed by the image of an initial word which already ends in that
terminal. Any new source compiler must leave the exhaustive positive overlap-queue class rather
than alter or revive one of its scanners.

The exact checks and evidence boundary are in
[`audits/m43-deletion-scanner-2026-08-08.md`](audits/m43-deletion-scanner-2026-08-08.md),
[`audits/m43-overlap-queue-2026-08-08.md`](audits/m43-overlap-queue-2026-08-08.md),
[`audits/m43-overlap-lag-decision-2026-08-10.md`](audits/m43-overlap-lag-decision-2026-08-10.md),
[`audits/m43-reset-scanner-decision-2026-08-10.md`](audits/m43-reset-scanner-decision-2026-08-10.md),
[`audits/m43-periodic-conjugate-decision-2026-08-10.md`](audits/m43-periodic-conjugate-decision-2026-08-10.md), and
[`audits/m43-alternating-defect-literature-2026-08-07.md`](audits/m43-alternating-defect-literature-2026-08-07.md).

#### Matrix trunk: parabolic bridge language

The parabolic blade [`M4-M03`](SALVAGE.md#m4-m03-parabolic-blade-and-bridge-grammar) remains the
live zero-set construction. Lean classifies its unique singular gap atom `R`, proves every zero
needs at least three copies, and contracts every arbitrary exceptional chain exactly to a product
of `2 × 2` bridges. [`M4-O08`](SALVAGE.md#m4-o08-residue-two-necessary-wall) proves that every
zero contains a residue-two gap.

Within the regular residue-zero stratum,
[`M4-S02`](SALVAGE.md#m4-s02-residue-zero-safe-bridge-cone) gives the complementary exact
compression: every nonempty bridge stays in a strict Archimedean cone and has negative
determinant. Any safe bridge zero must therefore use a residue-one atom; this is a local
compression, not a complete safe-return theorem.

The complete safe exterior state is now controlled. The arbitrary-switching flag
[`M4-S04`](SALVAGE.md#m4-s04-arbitrary-switching-three-adic-exterior-flag) proves that every
regular safe word remains in a normalized two-sector `3`-adic flag. The leftmost residue selects
the sector, even after unbounded cancellation. If such a word lies on the bridge wall `u=0`,
residue zero forces `ν₃(w)<ν₃(v)` and residue one forces `ν₃(v)<ν₃(w)`. For a regular
residue-one `b` atom, wall incidence is exactly

```text
(12·3^β−1)(u+w)+2v=0.
```

This is not safe return: both flag sectors contain ambient wall points. It is the correct
replacement for the retired one-coordinate and finite-cone attacks. The scalar state fracture
[`M4-O09`](SALVAGE.md#m4-o09-one-coordinate-exterior-fracture) shows that residue-one `c` needs
both projective coordinates, and the irrational cycle
[`M4-O10`](SALVAGE.md#m4-o10-irrational-rotation-cone-fracture) excludes every finite strict
wall-separated cone or Markov multicone.

The arbitrary grammar [`M4-S06`](SALVAGE.md#m4-s06-arbitrary-defect-bridge-grammar) closes the
defect-count node. Every cleared residue skeleton factors into local incidences; its only possible
zero runs have length `1 mod 4` between opposite phases or length `3 mod 4` between equal phases.
A concrete rational skeleton avoiding those runs is nonzero. More strongly, every nonempty pure-
defect block has an invertible bridge. Every arbitrary bridge zero descends to one incidence
between two consecutive singular bridges, with only invertible transport between them; additional
walls cannot cancel collectively. On a wall `(0,v,w)`, the exact nonzero cokernel is `(v,-4w)`.

A second parabolic family now supplies an exact semantic boundary.
[`M4-M04`](SALVAGE.md#m4-m04-retuned-semantic-boundary) changes the digit functional and the
open root so that gap two after `b` is the unique singular atom. Complete Neary gaps evaluate to
sparse side-normal matrices, and one fixed minor of the literal three-generator context

```text
G_b S² (complete Neary word) G_b S² G_b
```

vanishes exactly on the four-tile terminal equation. Fixed retractions recover its internal
bridge, so the context is nonzero even at a match. There it is a nonzero outer product with fixed
right row

```text
(-1, (15·3^β+3)/2, 28, 24).
```

Complete-gap continuations preserve the first coordinate and cannot annihilate this row. The
fixed-row closure is now retired by
[`M4-O13`](SALVAGE.md#m4-o13-retuned-pseudo-terminal-obstruction). At `(β,B)=(3,bbcc)`, the
legal tag system cycles forever, while one gap-thirty pseudo-production creates a nonzero
malformed context with the same terminal row. Every annihilator of that row therefore creates a
false zero. If no annihilator exists, the intended forward closure fails instead. The two
retuned obligations collapse into this losing fork; `M4-M04` is parked.

The original fixed-ray formal-plane punctuation is also closed.
[`M4-O14`](SALVAGE.md#m4-o14-original-semantic-endpoint-obstruction) places one intact complete
side-normal block between arbitrary fixed endpoint rays. Its bridge determinant is negative for
every nonempty pair of encoded words, so such a block cannot be an endpoint wall. Every fixed
incidence obeys `22c₀-31cX-18cY=0`. Under the correct terminal convention
`Y=tX+m, τ=tσ`, vanishing on the formal terminal plane forces vanishing on the entire length
plane. This does not exclude a coincidence confined to the discrete language.

The conditional identity
[`M4-C04`](SALVAGE.md#m4-c04-original-mixed-gap-endpoint-compiler) recognizes the intended
four-parameter equation if regular contexts `C,D` reach

```text
C(0,−2,1)ᵀ ∼ (4,4,−1)ᵀ,
D A(18,11)ᵀ ∼ ((5·3^β−1)/2,3^(β+1),−1/2)ᵀ.
```

Lean proves the resulting bridge product vanishes exactly on the Neary terminal equation. It
also proves that neither context can consist only of complete gaps.

This architecture is now retired by
[`M4-O15`](SALVAGE.md#m4-o15-original-pseudo-terminal-endpoint-obstruction). On the admissible
nonhalting instance `(β,body)=(3,bbcc)`, one regular gap-thirty pseudo-production yields a
33-tile middle satisfying the same corrected terminal equation. If the endpoint contexts do not
exist, the forward reduction fails; if they exist, that middle is a false zero. Reaching the two
rays is therefore no longer frontier work.

The spare-eigenvalue repair is closed by
[`M4-O16`](SALVAGE.md#m4-o16-one-complement-spectral-checksum-obstruction). Among all rational
roots retaining the paired order-three block and carrying syntax only in its one-dimensional
complement, the cube identity forces a dichotomy: a nonunit eigenvalue removes both wall
couplings and makes every word nonzero, while eigenvalue one restores the affine erase--rule
line and its infinite pseudo-production ladder. The strongest linear interpolation no-go claimed
in the external report is rejected: completeness need not accept every Boolean tile assignment
on a fixed skeleton.

The all-word node has now contracted further. The one-sided orbit normal form
[`M4-S07`](SALVAGE.md#m4-s07-one-sided-wall-orbit-normal-form) supplies a canonical nonzero
right kernel `κ(U)` for every regular left wall. After any invertible bridge transport `T`, put
`adj(T)κ(U)=(a,b)`. A regular right word `V` closes the incidence exactly when

```text
exteriorState(V) ∼ (0,4b,a).
```

The target ray itself forces right wallhood. Together with `M4-S06`, this is equivalent to a
literal zero of the physical three-generator family. The safe-wall transport chamber
[`M4-S08`](SALVAGE.md#m4-s08-safe-wall-transport-chamber) now composes this incidence with the
safe flag. If the right wall begins in residue zero, its transported kernel must satisfy
`ν₃(a)<ν₃(b)`; residue one forces `ν₃(b)<ν₃(a)`. Both coordinates being nonzero with equal
valuation is therefore an exact avoidance certificate. This leaves the bad defect skeletons,
not arbitrary safe right-wall reachability, as the next transport classification.

All-`b` defect runs are now closed uniformly. The invariant-cone theorem
[`M4-S14`](SALVAGE.md#m4-s14-uniform-all-b-defect-run-exclusion) proves that a regular
safe/defect/safe bridge cannot close for any finite run of residue-two `b` atoms, independent of
run length, parity, phases, and waits. This strictly subsumes the shortest exact factorization
`M4-S09` and deletes the former three-defect coefficient expansion. Defect-run length is no
longer a frontier axis until a body-dependent `c` atom enters the run or an endpoint context.

Both `c`-defect orientations with `b` endpoints are now dead. The exact width-three sign theorem
[`M4-S10`](SALVAGE.md#m4-s10-phase-zero-c-defect-exclusion) excludes
`b(3z)c(3x+2)b(3y+1)` for every nonempty body and all regular waits. The opposite orientation is
not coefficientwise signed, but
[`M4-S11`](SALVAGE.md#m4-s11-opposite-c-defect-cylinder-exclusion) excludes it by exact ternary
prefix cylinders.

The mixed sign has now been compressed exactly. The surviving determinant is `−4374z` times

```text
1699776(M−3)(8y+1)x − B_y y − B₀,
```

with `B_y−8B₀=1982448(M−3)`. Hence its rational root in `x`, as `y` ranges from zero to infinity,
moves through one body-dependent interval of fixed width `1059/7264<1`. The all-`c` body and the
five leading-`c`-run cylinders miss every natural root. A shortest bad run with `b` endpoints
must therefore have a `b` defect.

The endpoint alphabet has also contracted. The coefficientwise sign theorem
[`M4-S12`](SALVAGE.md#m4-s12-residue-zero-c-endpoint-exclusion) excludes both shortest bad-run
orientations with a `b` defect when the residue-zero safe endpoint is `c`. Thus a shortest
one-`c` endpoint survivor must place that `c` in residue-one phase. The second sign theorem
[`M4-S13`](SALVAGE.md#m4-s13-residue-one-left-c-endpoint-exclusion) also excludes the residue-one
left endpoint in the `1|2|0` orientation. The sole one-`c` endpoint survivor with a `b` defect is
therefore `b(3z)b(3x+2)c(3y+1)`; its mixed-sign determinant is the next endpoint target.

The first two-`c` endpoint family is also dead. The coefficient theorem
[`M4-S15`](SALVAGE.md#m4-s15-opposite-double-c-endpoint-exclusion) excludes
`c(3z+1)b(3x+2)c(3y)` for every nonempty body and all waits. The simultaneous endpoint-defect
sign theorem [`M4-S16`](SALVAGE.md#m4-s16-phase-zero-left-c-defect-exclusion) also excludes
`c(3z)c(3x+2)b(3y+1)`. The cylinder theorem
[`M4-S17`](SALVAGE.md#m4-s17-opposite-right-c-defect-cylinder-exclusion) further excludes
`b(3z+1)c(3x+2)c(3y)`: its two rational `x` roots occupy one open unit interval on every
leading-`c` code cylinder. Six shortest families remain: the four `0|2|1` forms

```text
b b c,  c b c,  b c c,  c c c,
```

and the two `1|2|0` forms `c c b` and `c c c`, where the positions record endpoint, defect,
endpoint letters. The immediate `c b c` target now has a checked integral trilinear core.
On the all-`c` code ray `L=M−2`, it factors into two linear wait pencils and neither can vanish
at natural waits. Its non-all-`c` digit cylinders remain open. Of the six survivors, four have a
`c` defect; the two `b`-defect survivors are `b|b|c` and this `c|b|c` family.

The phase-zero `b|c|c` survivor now carries an exact parity obstruction
[`M4-S18`](SALVAGE.md#m4-s18-phase-zero-double-c-parity-cylinder). If both the body length and
its number of `b` letters are odd, the primitive determinant core is `2` modulo four for every
triple of waits. Hence any zero in this family must lie in the union of two complementary body
cylinders: even body length or even `b` count. This narrows one survivor but does not remove it
from the six-family list.

The sole surviving one-`c` endpoint, `b`-defect family has a stronger parity cut
[`M4-S19`](SALVAGE.md#m4-s19-phase-zero-right-c-odd-length-cylinder). For
`b(3z)b(3x+2)c(3y+1)`, odd body length alone makes the primitive determinant core `2` modulo
four, with no condition on the body code or waits. Hence every zero in the `0|2|1` `b|b|c`
family must have even body length. The family remains in the six-family list.

The same body-parity obstruction now reaches the other phase-zero `c`-defect survivor
[`M4-S20`](SALVAGE.md#m4-s20-phase-zero-triple-c-parity-cylinder). For
`c(3z)c(3x+2)c(3y+1)`, odd body length and odd `b` count again make the primitive determinant
core `2` modulo four for all waits. Thus `M4-S18` and `M4-S20` remove that parity class from both
phase-zero `c`-defect families, while the six-family count remains unchanged.

The `b|b|c` cut now fills a three-class parity rectangle
[`M4-S21`](SALVAGE.md#m4-s21-phase-zero-right-c-parity-rectangle). Even body length together
with odd `b` count makes its primitive core `4` modulo eight; `M4-S19` already removes both
odd-length classes. Thus a zero requires even body length and even `b` count. A checked exact
factorization on the residual body `bbcc` also shows that, after its content `32` is removed,
the specialization `x=y=0` is affine in `z` with odd leading coefficient. It consequently has
a root modulo every power of two. Higher fixed 2-power congruences cannot remove the residual
rectangle; the live attacks are the fixed-`y` divisor factorization and an archimedean
root-straddling bound.

The first archimedean cut is complete
[`M4-S22`](SALVAGE.md#m4-s22-phase-zero-right-c-all-c-ray-exclusion). On an all-`c` body the
`b|b|c` core factors into a scale-`y` pencil, which cannot vanish for `S>1`, and an `x,z`
pencil whose rational `x` root lies strictly between 214 and 215 for every `z≥0`. The whole
nonempty all-`c` ray is dead. Inside the even/even rectangle this removes every `c^(2k)`, so
`bb` is now its shortest surviving body. The next split is the all-`b` ray versus genuinely
mixed bodies, using `D=S−C−1` as the complement coordinate.

The new shortest residue is also dead
[`M4-S23`](SALVAGE.md#m4-s23-phase-zero-right-c-bb-body-exclusion). The body `bb` has exact
coordinates `(S,C)=(59049,49532)`, where the `b|b|c` core is uniformly `8` modulo `16` for all
waits. Thus no length-two body remains in the even/even rectangle. Any live body there has
length at least four; it is either farther along the even all-`b` ray or contains both letters.

The complete all-`b` ray is now dead
[`M4-S24`](SALVAGE.md#m4-s24-phase-zero-right-c-all-b-ray-exclusion). Small even exponents fall
to exact 2-power residues; from exponent fourteen onward, a bounded `(x,y)` chamber and an
affine-in-`z` resultant make an integral zero impossible. Together with `M4-S22`, both unary
rays have left the even/even rectangle. Every remaining body in this family is genuinely mixed.

The mixed residue now carries a native finite-state blade
[`M4-S25`](SALVAGE.md#m4-s25-phase-zero-right-c-complement-blade). For
`D=S−C−1`, appending `c` sends `D↦3D` and appending `b` sends `D↦243D+39`. Two exact
modulo-sixteen factorizations force every residual zero to satisfy
`D≡length(body) (mod 4)`. This kills the alternating length-four bodies `bcbc` and `cbcb` and
about half of the even/even complement states. The live attack is no longer a generic body
search: factor the complement core as a bilinear SFFT divisor equation, then combine its sharp
prefix cylinders with the remaining complement state.

That divisor equation is now exact
[`M4-S26`](SALVAGE.md#m4-s26-phase-zero-right-c-complement-sfft). After collecting
`H=ayz+by+cz+d`, its discriminant `bc−ad` splits into `D`, `48x−3029`, and one further
linear factor. Hence a zero forces `(ay+c)(az+b)` to equal a completely factored integer, while
the physical complement always satisfies the sharp bound `242D≤39(S−1)`. Fixed bodies are
therefore finite divisor problems, not wait boxes. The remaining uniform task is to turn the
first-`b` complement cylinders into global wait bounds and feed those bounds into the trailing
3-adic constraints.

The thin end of complement space is now dead
[`M4-S27`](SALVAGE.md#m4-s27-phase-zero-right-c-thin-complement-cone). The exact decomposition
`H=FP+DJ` has opposite signs at consecutive `x` values 214 and 215 whenever
`0<D/S<1/2160000`; the order reverses at `y=0`, but the same integral gap excludes a zero.
Thus every mixed survivor has a uniform lower complement density. The remaining body language
must now lie simultaneously in finitely many first-`b` density cylinders and the trailing
3-adic cylinders. Complete that intersection analytically; computational emptiness at bounded
body length is reconnaissance, not a theorem.

The leading direction is now formally finite
[`M4-S28`](SALVAGE.md#m4-s28-phase-zero-right-c-long-leading-c-cylinder). A leading `c` fixes
`D` while tripling `S`; the global complement bound and `3^12` therefore put every mixed body
with twelve leading `c` letters inside `M4-S27`. Any hypothetical survivor has its first `b`
among the first twelve body positions. The exact cylinder analysis should now lower that
coarse formal cutoff and meet the three reduced Hensel residue classes in the middle; do not
infer a trailing-run bound from an unreduced congruence representative.

The exact first-`b` cylinders are now kernel-checked
[`M4-S29`](SALVAGE.md#m4-s29-phase-zero-right-c-first-b-density-cylinder). A first `b` after
`j` leading `c` letters forces
`13/(81·3^j)≤D/S<39/(242·3^j)`. This is the correct compact interface for the finite
analytic classification: prove monotonicity once, check only rational interval corners, and
retain reduced congruence representatives before extracting any trailing consequence.

The zero middle-wait face is now cut by a second density cone
[`M4-S30`](SALVAGE.md#m4-s30-phase-zero-right-c-zero-wait-complement-cone):
`S−1≤585D` makes the core strictly positive. The finite first-`b` classification may therefore
assume `y>0` throughout every sufficiently dense prefix cylinder.

The corrected trailing engine is now exact
[`M4-S31`](SALVAGE.md#m4-s31-phase-zero-right-c-trailing-arithmetic). A last `b` followed by
`c^h` gives `v₃(D)=h+1`; the two primitive `z` pencils have a `2·3^12` factored
cross-resultant; and the core isolates the sole unscaled wait term. Use this representation for
the bounded `3^13` classifier. The earlier lower bound obtained from an unreduced congruence
representative remains invalid and must not reappear.

The middle wait is globally finite
[`M4-S32`](SALVAGE.md#m4-s32-phase-zero-right-c-global-middle-wait-bound). Every zero on a
body containing `b` satisfies `y≤51767`; the proof uses four first-`b` density regimes and no
body census. Future classifiers must use this theorem rather than an experimental search cap.

At outer wait `x=211`, the `cb` chamber now has an exact positive divisor equation
[`M4-S33`](SALVAGE.md#m4-s33-phase-zero-right-c-x211-divisor-chamber). Its two affine divisor
coordinates multiply to `2·3^14·31·229·D·W`, obey reconstruction congruences, and carry four
body-elimination resultants. This is a finite arithmetic interface, not yet an extinction
theorem: close its divisor allocations against the bounded middle wait and trailing cylinders.

The second-first-`b` cylinder is dead
[`M4-S34`](SALVAGE.md#m4-s34-phase-zero-right-c-second-first-b-extinction). Analytic root
envelopes reduce it to 77 outer-wait pairs; exact tail-density rectangles leave one endpoint,
which lies in a certified grammar gap. The final theorem excludes every even-`b` body beginning
`ccb`. With leading positions at least twelve already removed by `M4-S28`, the remaining
first-`b` positions are `0`, `1`, and `3` through `11`. Reuse the root-window and exact-corner
certificate architecture rather than returning to raw bounded word enumeration.

The density grammar now has one uniform separator
[`M4-S35`](SALVAGE.md#m4-s35-phase-zero-right-c-first-b-position-gap). At every threshold
`k`, a physical body lies on one side of
`13S≤81·3^kD` or `242·3^(k+1)D<39S`. Any finite classifier that forces `D/S` into the open
gap between consecutive first-`b` cylinders should terminate through this theorem, not a new
prefix case split. In particular, the two density gaps left by the `x=211` terminal candidates
are its `k=0` and `k=1` instances.

The bounded `x=211` `cb` chamber is now dead
[`M4-S36`](SALVAGE.md#m4-s36-phase-zero-right-c-bounded-x211-extinction). The physical SFFT
product and trailing factorization force an exact two-coordinate 3-adic allocation; the core
equation supplies the density envelope and the global middle-wait interval. Under
`h≤5`, `j≤13`, and `z<3^13`, an exact generated classifier leaves ten triples, all with the
next `b` immediate, and `M4-S35` kills their two terminal density gaps.

The next-`b` position restriction is now eliminated
[`M4-S37`](SALVAGE.md#m4-s37-phase-zero-right-c-x211-position-extinction). If `j≥13`, exact
cancellation contracts the density inequalities to a strip in the common displacement
`k=y−22529≤817`; its eleven possible waits all violate the base 3-adic divisibility from the
valuation envelope. Thus `j<13` is derived, and the S36 classifier applies with no position
hypothesis. The full `cb` chamber still has two honest exits: `h≥6` and `z≥3^13`. Density alone
cannot cap `z`: the formal envelope contains every `z≥394` at `h=j=0` and `y=39726`.

The trailing-run restriction is also eliminated below the inner-wait cap
[`M4-S38`](SALVAGE.md#m4-s38-phase-zero-right-c-x211-run-extinction). Exact run coordinates
give `v₃(U)+v₃(V)=h+16`; `z<3^13` caps the second order, while root congruences and density
extinguish every `h≥6`. Composed with S37 and S36, the physical `x=211` `cb` core is now
nonzero under the sole bound `z<3^13`.

The large-inner exit is now eliminated
[`M4-S39`](SALVAGE.md#m4-s39-phase-zero-right-c-x211-large-inner-extinction). The exact suffix
balance and global complement wall leave 155 affine `(j,y)` chambers when `z≥3^13`; a
kernel-rechecked 231-node decision tree reads at most three suffix letters before reaching a
sign, density, or empty-suffix contradiction. Thus every even-`b` body beginning `cb` has
nonzero bridge determinant at `x=211`, with no remaining wait or body-length bound. This is a
cylinder closure, not a cell closure.

The outer-wait axis is now bounded
[`M4-S40`](SALVAGE.md#m4-s40-phase-zero-right-c-outer-wait-cap). The first-`b` density bound
and exact core slopes prove that every physical `cb` zero has `x≤211`; S39 removes the endpoint,
so only `x≤210` remains. The next accepted ratchet must classify the exact suffix envelope
uniformly over that full lower range and eliminate every surviving arithmetic chamber. A finite
search through sampled suffix positions does not discharge the uniform reduction.

Two original-family nodes survive, and they must not be conflated.

1. **Exterior collision avoidance.** Use `M4-S06`--`M4-S15` to classify the transported kernel
   across the two bad defect-run classes. A safe right endpoint can close only after the
   transport enters its leftmost-phase chamber. Uniform avoidance proves this family immortal;
   one hit gives an exact physical zero word. Do not rebuild a grammar for the right walls.
2. **Syntax-sensitive semantics.** Construct a nonlinear legality invariant inseparable from
   the resonant wall incidence, use a genuinely different root family, or restrict to a
   computable universal source image on which pseudo-terminal side normals are impossible. It
   must prove both the forward zero and the arbitrary-word converse. Fixed endpoint statistics,
   the spare rational eigenvalue, and another restatement of the terminal plane are dead.

An ontology guard applies to both nodes. The exterior dynamics act by the conjugated
adjugate-transpose `exteriorTransition(C)`, while endpoint contexts act by the primal matrix
`C`. A conic invariant of the former does not constrain `C u*∼k`; the regular primal atom
`atom 3 bbcc b 0` already sends a conic-null vector to conic value `24`.

The dead subtrees remain dead: literal Neary role fusion (`M4-O01`, `M4-O02`, `M4-O05`), finite
queues of complete tokens (`M4-O03`), exact internal/final block codes (`M4-O04`), closed
finite-order roots (`M4-O07`), one-coordinate exterior dynamics (`M4-O09`), and finite strict
cone separation (`M4-O10`). The annihilator guard [`M4-O06`](SALVAGE.md#m4-o06-punctuation-image-annihilator)
is discharged. Finite gap catalogues, bare rank-one incidence, defect-count casework, collective-
wall cancellation, pure-defect endpoints, fixed-ray complete-block semantics, spare-eigenvalue
checksums, and unproved flatness are not frontier work.

#### Orthogonal trunk: free cancellation and homogeneous punctuation

The Carvalho route no longer depends on compressing its high-rank Stallings presentation.
The audited fixed-program specialization
[`G3-M01`](SALVAGE.md#g3-m01-free-group-discrepancy-engine) reduces source halting to one
positive sequential-transducer equation:

```text
∃τ∈{0,1,H,p}*, n≥0: τ p H^n=d_e Ψ(τ).
```

First-letter cancellation gives a converse for every positive `τ`. The natural closed-path
subgroup nevertheless has rank `648b+7≥655`, and
[`M4-O17`](SALVAGE.md#m4-o17-positive-nielsen-basis-obstruction) proves that the positive
monoid on its explicit all-positive Nielsen basis intersects the equalizer only in the identity.
Basis compression is not a live node.

The matrix end of the route is now complete. The homogeneous punctuation mechanism
[`M4-M05`](SALVAGE.md#m4-m05-boundary-guarded-homogeneous-punctuation) embeds a pair of binary
free-group homomorphisms into two unimodular `4 × 4` left--right actions. If fixed binary
boundaries `L,R` disagree at the empty interior, one rank-one boundary separator gives

```text
three integer 4 × 4 matrices mortal
  ↔ ∃w∈{0,1}*: α(LwR)=β(LwR),
```

with a converse over every physical matrix word. The fifth affine coordinate is unnecessary.

The cyclic-side stratum is now closed. [`M4-D04`](SALVAGE.md#m4-d04-cyclic-side-binary-fixed-boundary-decision)
reduces any instance with one cyclic-image homomorphism to rational-subset membership in
`F(Δ)×ℤ`, which is decidable. A noninjective homomorphism from `F₂` to a free group has cyclic
image, so every hard binary instance must make both homomorphisms injective.

The endomorphism-extendable stratum is also closed.
[`M4-D05`](SALVAGE.md#m4-d05-endomorphism-extendable-fixed-boundary-decision) proves that if
`α=Φ∘β` for an ambient free-group endomorphism, then the boundary equation is ordinary
endomorphism-twisted conjugacy restricted to the rational positive trace of `β`. Its solution set
is a computable fixed-subgroup coset, so rational intersection decides the restriction. Extension
existence is decidable by equations in a free group. Swapping the sides gives the symmetric cut.
Thus a hard instance must be mutually nonextendable; in its minimal instance subgroup neither
coordinate image can be a retract or a free factor. Equivalently, the surviving problem is
positive-basis-constrained partial twisted conjugacy for a nonextendable rank-two partial
endomorphism.

Two free-cancellation nodes survive and should be raced against each other.

1. **Constructive binary compiler.** Compile the four-letter marker-tail equation into positive
   binary fixed-boundary free-group equality, preserving solvability in both directions over the
   complete binary free monoid, forcing an empty-interior mismatch, and making both maps
   injective and mutually nonextendable. A solution closes `M₄(3)` immediately through `M4-M05`.
2. **Nonextendable fixed-rank classification.** Decide the remaining mutually nonextendable
   injective/injective binary fixed-boundary problem, or prove a structural obstruction to
   carrying the Carvalho equation.
   [`Logan`](references/logan-2022-equalizer-rank-two.md) bounds injective equalizers from `F₂`
   by rank two but gives no general triviality algorithm;
   [`Ciobanu--Logan`](references/ciobanu-logan-2021-free-group-pcp-variations.md) use hypotheses
   and a two-generator overhead to remove boundaries. A decision theorem kills this trunk and
   must be sought as aggressively as the compiler.

The two trunks cross-pollinate only at the master problem. The parabolic route is arithmetic
projective reachability inside one explicit family; the Carvalho route is positive coding in a
free group followed by a finished rank-one separator. Neither is supporting infrastructure for
the other, and failure of one does not weaken the other.

### 2. Zero-set compression and fused punctuation: `M₅(3)`

The literal CHHN packing has no common invariant line or hyperplane. The all-placement
certificate [`MM-O01`](SALVAGE.md#mm-o01-all-placement-packing-rank) now formally proves that
its selected coefficient series has exact representation dimension six for every placement.
This closes exact minimization of that packing in five states.

The paired four-state scalar system closes a second exact route. Lean certifies a uniform
nonsingular four-by-four Hankel section
([`MM-O04`](SALVAGE.md#mm-o04-uniform-rank-four-paired-series)), while the two-channel boundary
tax costs two additional states in every exact diagonal bridge. Their composed theorem
`paired_exact_diagonal_twoChannel_state_lower_bound` therefore requires at least six states.
Both conclusions concern exact series; neither constrains another series with the same zero set.

The internal-word sandwich compiler
[`MM-C04`](SALVAGE.md#mm-c04-internal-word-sandwich-minimization) initially offered a way
around every parser obligation. It is now closed on the canonical paired-binary mortality
family: [`MM-O11`](SALVAGE.md#mm-o11-full-algebra-paired-binary-family) proves that its word
span is `M₆(ℚ)`, so every nonzero sandwich has exact dimension six. All 120 literal CHHN
packings are likewise full-algebra at the benchmark, although that finite modular sweep is not
a uniform theorem. The sandwich compiler becomes live again only with a different physical
six-state family.

Three live routes remain.

1. Construct a five-state two-letter scalar series whose nonempty zero existence is equivalent
   to a source terminal match, then adjoin the ordinary rank-one separator. The letter matrices
   may be singular, and odd words need only avoid zeros on source no-instances. The stronger
   wordwise same-zero interface remains sufficient. Processing the common deletion channel
   `(V_b^D,B_b^D)=(V_c^D,B_c^D)` before the symbol bit cannot merge the unchanged exact lower
   fibres: [`MM-O15`](SALVAGE.md#mm-o15-deletion-first-fibre-fracture) forces the unequal rule
   scales to coincide. A survivor must change the nonzero series, use nonlinear or
   history-sensitive state, or weaken to the existence-only interface. A four-state root would
   prove the stronger `M₄(3)` result.
2. Fuse the paired toggle and separator inside one five-dimensional generator. The
   off-diagonal companion interface
   [`MM-M01`](SALVAGE.md#mm-m01-off-diagonal-companion-interface) supplies a complete bridge
   grammar once a physical control word realizes it. Pure delimiter powers cannot supply
   punctuation while preserving the exact isolated toggle
   ([`MM-O06`](SALVAGE.md#mm-o06-pure-power-punctuation-obstruction)). Nor can a bordered
   compiler make every delimiter pair contextually invisible:
   [`MM-O16`](SALVAGE.md#mm-o16-exact-delimiter-pair-obstruction) proves that exact parity-pair
   cancellation forces immortality. Its cubic companion calculation also excludes pure and
   fixed-context cubic projections for the full paired series. Absorbing the forced initial
   `R_c` does not reopen that exact route: [`MM-O18`](SALVAGE.md#mm-o18-forced-rule-companion-toggle-wall)
   proves that the derivative still has rank four on isolated-toggle words, and its compulsory
   constant companion channel forces the physical toggle to be invertible. This contradicts
   the required rank-two cube regardless of fifth-coordinate data couplings. The exact
   bordered-companion branch is therefore closed before any `S²/S³` fracture grammar can help.
   This exact obstruction has no finite sourcewise-existential residue:
   [`MM-O21`](SALVAGE.md#mm-o21-sourcewise-finite-probe-blindness) constructs a changed series
   with the same zero existence whose entire `MM-O18` probe section is constant one. It also
   proves that a source-computable complete finite probe cutoff would decide halting. Any weaker
   no-go must therefore use an arbitrary-word consequence of a stated architecture; any weaker
   construction must realize its changed series in five states.
   The guard itself fails that constructive obligation:
   [`MM-O22`](SALVAGE.md#mm-o22-six-guard-parser-rank-wall) extracts, from any original zero
   witness, a `7×7` Hankel section `J₇-I₇` of the six-guard changed series. Every wordwise exact
   realization on a yes-source therefore has at least seven states. This does not restore a
   fixed probe certificate: the minor depends on the potentially unbounded witness whose
   existence the weak criterion asserts.
   The setter candidate
   [`MM-M03`](SALVAGE.md#mm-m03-five-state-setter-punctuation) instead uses the mixed word
   `S²A_cS³=λC̃L̃`. It proves the regular decoder and halting-to-mortality implication.
   Its entire malformed-word converse is the projective avoidance problem
   [`MM-S01`](SALVAGE.md#mm-s01-square-run-projective-normal-form): rational Möbius maps
   `Φ_z` must avoid their poles from the reset values `0` and `1/μ`, except for a genuine
   terminal match. The source boundary fixes `r=t/μ`
   ([`MM-O07`](SALVAGE.md#mm-o07-setter-parameter-rigidity)); generic parameter selection is
   not a live escape. Nor is the remaining side-basis shear: after physical boundary
   calibration, [`MM-O12`](SALVAGE.md#mm-o12-boundary-calibrated-setter-shear-is-gauge)
   proves that it disappears from both the mixed separator and the projective transfer.
   Reversing the two nonzero ternary digits is lawful and strictly sharper:
   [`MM-M04`](SALVAGE.md#mm-m04-swapped-digit-setter) preserves the regular decoder and mixed
   separator while moving the common projective center below zero and making every transfer
   orientation preserving. The radix-ten specialization
   [`MM-M05`](SALVAGE.md#mm-m05-decimal-swapped-setter) preserves the compiler and removes the
   remaining real elliptic corridor:
   [`MM-S11`](SALVAGE.md#mm-s11-decimal-setter-hyperbolicity) proves every transfer strictly
   hyperbolic. This does not imply a common invariant cone; finite positive-ray systems are
   excluded by [`MM-O13`](SALVAGE.md#mm-o13-finite-positive-ray-setter-obstruction).
3. Use the scheduled compiler [`MM-C03`](SALVAGE.md#mm-c03-scheduled-binary-compiler).
   A fixed binary deletion-width-three universality theorem would finish the reduction
   immediately. None was located. The constructive alternative is to replace the variable
   phase clock by a constant-state delimiter or punctuation mechanism and prove that every
   malformed placement is excluded by the terminal-match normal form. The width-three
   rank-five theorem [`MM-O05`](SALVAGE.md#mm-o05-width-three-scheduled-rank) shows that five
   exact states are necessary at that width; it does not obstruct a same-zero clock
   compression or delimiter fusion. Exact deletion-width-three source substitution remains a
   separate open problem: the theorem needed by `MM-C03` must compute the variable rule body
   and its coupled suffix input from the same source, not merely supply a fixed width-three
   machine with an arbitrary input. [`MM-D01`](SALVAGE.md#mm-d01-sparse-width-three-source-decision)
   excludes every zero- or one-`c` source image, and
   [`MM-D02`](SALVAGE.md#mm-d02-adjacent-two-c-source-decision) decides every adjacent-two-`c`
   coupled image. The next genuine source boundary is two separated `c` letters or at least
   three `c` letters. [`MM-S23`](SALVAGE.md#mm-s23-adjacent-two-c-periodic-pair) remains the
   unrestricted-queue warning that a second `c` already permits balanced reproduction.
   [`MM-S25`](SALVAGE.md#mm-s25-separated-two-c-periodic-orbits)
   supplies an explicit periodic obstruction for the diagonal separated bodies
   `bb c bⁿ c bⁿ` in residues zero and one modulo three, while
   [`MM-S30`](SALVAGE.md#mm-s30-separated-residue-eight-drainage) proves halting in residue
   eight modulo nine and
   [`MM-S34`](SALVAGE.md#mm-s34-separated-residue-five-cantor-drainage) proves halting in residue
   five by a finite injective defect quotient, and
   [`MM-S41`](SALVAGE.md#mm-s41-separated-residue-two-first-cut) proves halting in subresidues
   two and twenty modulo twenty-seven.
   [`MM-S43`](SALVAGE.md#mm-s43-four-c-reproduction-cut) then proves residue eleven modulo
   eighty-one halts, and [`MM-S48`](SALVAGE.md#mm-s48-centered-four-c-extinction) closes both
   surviving tail phases. [`MM-S58`](SALVAGE.md#mm-s58-unequal-two-c-cycle-law) proves a
   canonical cycle law for every nontrivial even body off middle phase two and proves coupled
   entry on the unequal plane `p=3(r-s)+2`, `r≥s`.
   [`MM-S70`](SALVAGE.md#mm-s70-sheared-residue-eight-drainage) then proves halting in the
   middle-phase-two wedge `r≡8 (mod 9)`, `r-s≢2 (mod 3)`, while
   [`MM-S72`](SALVAGE.md#mm-s72-sheared-residue-twenty-six-drainage) proves halting in the
   surviving-shear subwedge `r≡26 (mod 27)`, `r-s≡2,5 (mod 9)`.
   [`MM-S75`](SALVAGE.md#mm-s75-matched-six-c-shear-drainage) further drains two thirds of the
   matched `r≡2,r-s≡0 (mod 3)` and `r≡5,r-s≡1 (mod 3)` pairs.
   [`MM-S78`](SALVAGE.md#mm-s78-phase-mismatched-six-c-drainage) then drains one joint
   subphase in each of the four phase-mismatched pairs and identifies the exact surviving
   active pair. The next source-level cut is that finite successor nucleus or coupled triples
   outside the sheared plane, not another diagonal or adjacent-`c` example.

The decimal setter is now the sharpest constructive route. The ternary swap remains useful
because its suffix and divisor-ray theory is mature; the decimal instance has stronger real
length separation and an exact two-prime carry. Its next experiment is not another
five-dimensional word search: propagate the one-dimensional projective state exactly and seek
a finite invariant separating every nonterminal orbit from every pole. Congruence quotients,
valuations with pulse phase, signed interval partitions, and self-synchronizing suffix states
are the first candidates. A first peeling theorem for the ternary instance
[`MM-S02`](SALVAGE.md#mm-s02-reset-zero-projective-peeling) now excludes every false pole
after one transfer from the ordinary reset. It also shows why valuation alone is insufficient:
all poles occupy two `3`-adic shells, while bounded malformed orbits rapidly saturate their
finite residue classes. The next abstraction must retain mismatch depth together with pulse or
suffix history. The centered carry theorem
[`MM-S03`](SALVAGE.md#mm-s03-centered-setter-carry) supplies that interface:

```text
X'=3^mY,      Y'=(RP−HV)Y+RHμVX.
```

Away from equal valuations, the valuation gap updates by
`d'=m−min(d,s)` with `s∈{1,β}`. It reduces the first possible two-transfer
collision to three rigid all-`c`/single-`D_b` block families. From the
distinguished boundary, the resonant carry is exactly the longest common
suffix of the upper terminal spelling and the lower spelling.
[`MM-S04`](SALVAGE.md#mm-s04-reverse-suffix-discrepancy) gives its exact
right-to-left machine. It is a word-valued PCP discrepancy queue, not a finite
pulse state. At either dangerous gap, however, the unprocessed left fringe has
upper length at most `β+2` or `2β+1`. The next proof must therefore quotient
the internal discrepancy queue semantically while preserving these bounded
targets; a larger residue modulus or phase-only automaton cannot suffice. The
first target is now gone:
[`MM-S05`](SALVAGE.md#mm-s05-distinguished-boundary-beta-shell) proves that
the `d=β` branch at boundary `1` cannot reach either single-erasure pole. Only
the valuation-one target survives there. Its distinguished normalized value
`Δ=H` is exactly a genuine terminal match. The divisor normal form
[`MM-S06`](SALVAGE.md#mm-s06-valuation-one-divisor-normal-form) writes every
other integral target on one of finitely many rays indexed by
`q∣(ρ+1)` and `a₀∣Hμ`; only one positive parameter remains unbounded. The
digit swap removes that unbounded parameter:
[`MM-S07`](SALVAGE.md#mm-s07-swapped-digit-finite-slope-reduction) makes the
centered coefficient strictly negative and forces every integral
valuation-one pole into a finite set of primitive slopes. The common scale of
the two code integers remains unbounded, so this is not yet a finite word
search. [`MM-S08`](SALVAGE.md#mm-s08-swapped-distinguished-boundary-beta-shell)
now formally excludes the residual value `2μ`, so the complete
distinguished-boundary `β` shell is safe at its exact physical witness
interface: common-suffix cancellation leaves equal upper and lower prefixes
of length `2β+1`. The later `D_c^(β+1)→singleton` branch has a different
two-transfer incoming projective state and is not an instance of this
theorem; its direct algebraic extinction belongs to `MM-S50`.
[`MM-S09`](SALVAGE.md#mm-s09-canonical-swapped-residue-cannot-hit-a-pole)
also excludes the unavoidable all-`D_c` valuation-one residue at every
compiler-emitted width.
[`MM-S10`](SALVAGE.md#mm-s10-swapped-target-suffix-sieve) fixes the last
`β+2` digits of every pole-compatible lower word and excludes the recurrent
nonhalting residue `Δ=ρ−1`.
The decimal specialization [`MM-M05`](SALVAGE.md#mm-m05-decimal-swapped-setter) removes the
ternary balanced corridor: [`MM-S11`](SALVAGE.md#mm-s11-decimal-setter-hyperbolicity) proves
every individual transfer strictly hyperbolic. Real dynamics stops there.
[`MM-O13`](SALVAGE.md#mm-o13-finite-positive-ray-setter-obstruction) excludes every finite
family of positive invariant rays, and
[`MM-O14`](SALVAGE.md#mm-o14-decimal-setter-elliptic-product) gives two individually
hyperbolic emitted-body blocks with an elliptic product. The decimal branch must therefore use
its exact joint `2`/`5`-adic carry, while the ternary branch retains the mature suffix sieve.

For the decimal instance,
[`MM-S12`](SALVAGE.md#mm-s12-decimal-two-prime-carry) gives the exact charts

```text
Z′=(G/E)(μ10^m−P+VZ)/(P−VZ),
W′=EGμ10^m/(T−VW),       T=EP+GV.
```

Every iterated block ends in an erasure. Multi-role targets have joint shell `(1,1)`; either
singleton erasure has shell `(β+1,β)`. A prospective next pole forces

```text
ν_p(T_target)+ν_p(X′)=m+ν_p(X),       p∈{2,5}.
```

The `(1,1)` shell preserves the cross-prime gap and shares normalized first unit `3` with the
distinguished reset. Gap pairs and one decimal unit therefore cannot separate it. The immediate
depth-one question is nevertheless closed:
[`MM-S13`](SALVAGE.md#mm-s13-decimal-first-transfer-extinction) proves that neither reset reaches
a false pole after one completed transfer. Exact two-depth exhausts the lower decimal code as a
complete suffix; the remaining prefix is either terminal or lies in a rational interval disjoint
from every target. [`MM-S14`](SALVAGE.md#mm-s14-ordinary-depth-two-shell-forest) then classifies
the ordinary depth-two shell forest. A/A survives only at a two-role middle block (apart from the
already peeled one-digit entry); A/B survives only at all-`c` lengths `β+1` and `β+2`; B/A
survives only as an all-`c` length-`β` block followed by `D_b`; B/B is impossible. The immediate
question is whether exact pole intervals or normalized suffixes kill the remaining resonances
and the distinguished-reset corridor, or whether one contains an explicit false pole.

The A-to-A resonance is now closed. [`MM-S15`](SALVAGE.md#mm-s15-ordinary-a-to-a-length-two-extinction)
puts `D_cD_c` images in the open gap `(961/1000,963/1000)` between the two target-pole
chambers. For `R_cD_c`, the compiler-emitted body forces enough lower weight that a `c`-leading
source maps below zero and a `b`-leading source above one; every positive pole lies between.
[`MM-S16`](SALVAGE.md#mm-s16-complete-ordinary-depth-two-extinction) now kills the remaining
A-to-B and B-to-A families. An exact all-deletion/first-rule split handles every phase word in
both long all-`c` blocks, while the `β`-`c`/`D_b` image factors strictly above one. No ordinary
false pole survives through two transfers. The distinguished reset is now the sole depth-two
front and remains an unbounded normalized-suffix problem.

That front now has an exact recursive state.
[`MM-S17`](SALVAGE.md#mm-s17-recursive-decimal-carrier) represents every consecutive A-shell
resonance by decimal units `(N,D)` with `t=N/(10μD)`. A block replaces the numerator by
`R=NT−10μGVD`; a following A pole forces `R=10^(m−1)N'`, and the next pair is `(N',EN)`.
The initial raw-head grammar excludes the leading-`b` head and reduces the nonterminal entry to
the two-`c` head. It does not recur: `N'` is a generalized product residual. For `m≥3`, the
forced last digits form a lawful period-two cycle. The apparent `m=2` escape is now closed:
[`MM-S18`](SALVAGE.md#mm-s18-length-two-carrier-extinction) proves that two equal-depth
`2`-adic summands cancel beyond depth one, contradicting the shell forced by a following
multi-role pole. Every surviving non-singleton transition therefore has `m≥3`, and the unit-digit
law applies without an exceptional branch. At the initial raw head only,
[`MM-S19`](SALVAGE.md#mm-s19-all-deletion-raw-head-extinction) now removes every all-`D_c`
block of upper length at least three by an exact mixed-prime suffix split. Combined with
`MM-S18`, no all-`D_c` block remains at any admissible non-singleton length. The live initial
grammar consists of rule-bearing phase words and all-erasure words containing `D_b`.
[`MM-S20`](SALVAGE.md#mm-s20-singleton-carrier-classification)
now resolves the separate singleton seam at the carrier level. A singleton-current block cannot
reach any later multi-role or singleton pole. A multi-role block can reach a singleton pole only
at upper length `m≥β+3`, and this bound is sharp for unrestricted decimal-unit rational carriers:
an explicit carrier exists at every such length. A fixed bounded suffix quotient cannot supply a
global descent on the surviving generalized multi-shell residuals:
[`MM-S21`](SALVAGE.md#mm-s21-bounded-decimal-suffix-cycles) proves that every
emitted multi-role block has a compatible projective carrier self-loop modulo `10^k` for every
fixed `k`. These are not exact rational cycles and need not be reachable from the distinguished
entry. The master residual is therefore encoded reachability of the long multi-to-singleton
carrier together with intersection of the encoded-entry orbit and an unbounded inverse-limit
suffix language. Local valuations, the abstract two-unit carrier, and acyclicity of a finite
congruence graph cannot close these questions alone.

[`MM-S22`](SALVAGE.md#mm-s22-gap-factor-quotient-gate) now cuts the long singleton branch with
the denominator ancestry absent from the unrestricted abstraction. Set `q=2·10^β−7` and
`G=9g`. For a primitive integral carrier with `D=EN₋` and `gcd(q,N)=1`, a singleton pole forces
both `V₂=qW` and `P₂+gW≡μ10^m (mod q)`. The fixed lift `G` and singleton lower digit `7` are
automatically coprime to `q`. Thus the gap-clean branch is an exact compiler-code congruence
problem; the remaining escape is either a numerator sharing a proper factor with the generally
composite `q` or an emitted code passing both gates. This does not settle `M₅(3)`.

[`MM-S24`](SALVAGE.md#mm-s24-factorwise-gap-ancestry) resolves that composite-factor seam. For
every `r∣q`, a recursive multi-shell step satisfies `r∣N' ↔ r∣NV`; prime support can first enter
the carrier only through a lower code and is then permanent. The initial two-`c` raw numerator
is not divisible by the full gap. More importantly, writing `q=rs`, every factor with
`gcd(r,N)=1` retains a localized singleton gate: `V₂=rW` and
`s(P₂−μ10^m)+gW≡0 (mod r)`. The residual is therefore a prime-support reachability problem,
not a binary clean/contaminated branch. The gates themselves are not sufficient: a
computationally certified physical all-`D_c` word at the compiler width `β=10` passes both
full-gap congruences, so encoded suffix semantics beyond these modular conditions remain
necessary.

[`MM-S26`](SALVAGE.md#mm-s26-exact-raw-head-prime-support) removes the initial support opacity.
If the unit two-`c` raw head `H` has terminal run length `s`, then every `r∣q` is automatically
coprime to nine and

```text
r∣H  ↔  r∣2·10^s+1743,       1≤s≤β−1.
```

Thus the initial set of contaminated gap primes is exactly an exponential divisibility set,
not an arbitrary compiler-code support. The remaining task is to classify that set and the
support installed later by reachable lower words; this theorem does not close `M₅(3)`.

[`MM-S27`](SALVAGE.md#mm-s27-reciprocal-raw-head-support) makes that exponential arithmetic
reciprocal and periodic. With `t=β−s`, every `r∣q` satisfies

```text
r∣H  ↔  r∣249·10^t+1.
```

Once `r` occurs, both later gap widths and later reciprocal exponents occur exactly when
`r∣10^k−1`. Proper-factor contamination is real: the physical width-five raw head
`H=5555557` and `q=199993` share `43`. Since ten has exact order `21` modulo `43`, the same
terminal-run-one support occurs exactly at widths congruent to five modulo `21`. The initial
gap-clean shortcut is therefore false; a closure must track this periodic support through the
lower-code ancestry and singleton gates.

[`MM-S28`](SALVAGE.md#mm-s28-arbitrary-history-gap-support-saturation) closes the support
bookkeeping and kills static missing-prime invariants. Along any exact recursive carrier
history, a prime `p∣q` divides the final numerator exactly when it divides the initial numerator
or one emitted lower code. Hence final support is saturated precisely when every gap prime is
initial or installed somewhere in the history. But the physical lower-code language itself has
no permanently missing gap prime: for `n=φ(|q|)`, the block `D_cⁿ` has lower code divisible by
the full `q`, not merely by `rad(q)`. This does not make that block reachable from the
distinguished carrier. The live seam is encoded-entry reachability with upper-code and complete
suffix data retained; support projection alone is exhausted.

[`MM-S32`](SALVAGE.md#mm-s32-entry-support-saturator-extinction) makes the first encoded-entry
cut. Replace the Euler width by `n=3φ(|q|)`: the all-`D_c` lower code remains divisible by the
full gap and now has `n≥3`. The raw-head extinction theorem `MM-S19` therefore forbids this
universal saturator from taking any lawful two-`c` raw head to another multi-role pole. The
remaining first-step saturation grammar is rule-bearing or contains `D_b`; later all-`D_c`
saturation from generalized product residuals also remains open. The distinction between source
language membership and carrier reachability is now formal rather than advisory.

[`MM-S33`](SALVAGE.md#mm-s33-leading-d_b-support-saturator-extinction) cuts the first
`D_b`-bearing family. The physical word `D_bD_c^(n−1)` has exactly the same lower code as
`D_c^n`, hence still contains the full gap, while its punctuated upper code is
`P_b=P_c+μ10^(n+β+1)`. A strengthened arbitrary-width theorem proves
`5^(n+β)∤R_c` for the all-`D_c` raw residual, including the exceptional first raw head. The
leading-`D_b` perturbation is too deep to change that obstruction, so the required
depth-`n+β` target shell is impossible. Other `D_b` positions, rule-bearing first blocks,
singleton targets, and later product-residual carriers remain open.

[`MM-S39`](SALVAGE.md#mm-s39-second-position-d_b-raw-head-extinction) first extended that cut to
the second position. [`MM-S40`](SALVAGE.md#mm-s40-first-beta-plus-one-position-d_b-extinction)
subsumes it by sharpening the baseline: every all-`D_c` raw residual of width `n` already fails
divisibility by `5^(n+1)`, with the regular and exceptional raw heads proved separately. A sole
`D_b` after `a` leading `D_c` roles changes the upper code only above a common suffix of depth
`t+β+2`; for `a≤β` this is at least `n+1`. Thus every one-`D_b` all-erasure word whose `D_b`
lies in positions `1,…,β+1` misses the next multi-role pole. Its lower code remains the all-zero
code and retains full-gap support whenever its total width is the entry saturation width. Late
positions, multiple `D_b` perturbations, rule-bearing words, and generalized carriers remain.

[`MM-S45`](SALVAGE.md#mm-s45-exceptional-late-one-d_b-boundary) closes every remaining regular
raw head. Its all-`D_c` residual already fails divisibility by `5^β` at every width, while even
a final-position `D_b` changes the upper code only at depth at least `β+2`. Hence a one-`D_b`
all-erasure survivor must satisfy both `prefixWidth>β` and the exceptional raw-head identity
with terminal run `s=β−1`. The entire one-marker branch is now the exceptional-late tail; the
theorem neither proves that tail nonempty nor controls multiple `D_b` or rule-bearing words.

[`MM-S47`](SALVAGE.md#mm-s47-global-one-d_b-raw-head-extinction) kills the exceptional-late
tail. The exceptional all-`D_c` residual and the exact positioned perturbation reduce to three
five-adic depths with fixed unit coefficients. Every strict depth order is impossible, and the
two equality arms have leading residues `4`, while their common corner has residue `1`.
Consequently no one-`D_b` all-erasure word carries the initial two-`c` raw head to a second
multi-role pole, in any position. The live erasure frontier begins with at least two `D_b`
roles; rule-bearing first blocks and later generalized carriers also remain.

[`MM-S49`](SALVAGE.md#mm-s49-nonempty-marker-all-erasure-extinction) removes that apparent
multi-marker frontier entirely. Every nonempty marker word has a unique rightmost `D_b`; after
factoring its common suffix, all earlier markers lie inside one coefficient that remains `2`
modulo `5`. A word `w` with `k≥1` markers has exact physical shell depth
`|tagEncode_β(w)|-1=|w|+k(β+1)-1`; this shell supplies every shallower divisor used by the
S47 analysis. Hence every all-erasure word containing at least one `D_b` misses the next
multi-role pole. Pure all-`D_c` words belong to the earlier length cuts. The decimal first-entry
search is now confined to rule-bearing blocks and later generalized carriers; no ternary
cylinder classification is being imported.

[`MM-S53`](SALVAGE.md#mm-s53-complete-all-erasure-first-entry-extinction) finishes the
first-entry erasure assembly. A pure two-role `D_c²` trace has shell `(1,1)`, while its two
two-adic unit summands cancel to greater depth; longer pure-`D_c` words are already excluded by
`MM-S19`, and every word with `D_b` is excluded by `MM-S49`. Thus every surviving
non-singleton first block from the distinguished decimal raw head contains at least one rule
tile. This conclusion remains raw-head-specific: later generalized carriers retain the
`m≥3` multi corridor and the reachable `m≥β+3` multi-to-singleton question.

[`MM-S54`](SALVAGE.md#mm-s54-rightmost-rule-phase-toggle-trichotomy) now fractures the surviving
rule-bearing raw-entry grammar at its rightmost rule. Its phase-erased companion has identical
upper spelling, and the lower perturbation is `10^sK` after an erasure tail of width `s`. The
three prefix classes `|u|=0`, `|u|=1`, and `|u|≥2` force respectively `K≡550,480,780
(mod 1000)`, giving exact outer shells `(s+1,s+2)` and `(s+2,s+1)` and exact middle
five-depth `s+1`. The first class kills every `R_cD_c^s`, `s≥1`, because its perturbation is
deeper than the prospective `(s,s)` pole and would make the forbidden all-erasure companion
share that shell. The live raw-entry grammar now begins with a later rightmost rule or contains
`b`; those branches must meet the displayed off-diagonal companion resonances.

[`MM-S56`](SALVAGE.md#mm-s56-exact-rule-resonance-grammar) solves those companion depths.
For all-`D_c` width `n`, the exact five-depth is `min(n,h+1)` at a regular head with
final-seven width `h`, and `min(n,2β−1)` at the exceptional head. A `b`-bearing rule block is
the sum of this comparison residual, a rightmost-`b` upper perturbation at depth `t_b+β+2`,
and a rightmost-rule phase perturbation. A physical pole forces a repeated minimum among these
three depths. Solving the regular equations leaves only `s=h`; all-`c` words additionally retain
the position-two boundary, while the exceptional head retains the phase frontier `s=2β−2` and
two explicit rightmost-`b` relative-position resonances. The next cut is coefficient-level
cancellation on those exceptional arms and the position-two boundary.

[`MM-S60`](SALVAGE.md#mm-s60-complete-b-bearing-rule-entry-extinction) executes that coefficient
cut and removes the entire b-bearing branch. At the exceptional head, the three scaled leading
coefficients are `2 or 4`, `2`, and `2`; every possible minimum-depth subset is nonzero modulo
five. At a regular head, the two tied arms both normalize to `2^h`, and the marker arm is
strictly deeper. The complete S56 positional grammar therefore has no b-bearing survivor.

[`MM-S62`](SALVAGE.md#mm-s62-all-c-position-two-rule-extinction) removes the all-`c`
position-two boundary. If the block width lies before the regular or exceptional raw-head
frontier, the phase perturbation and its all-erasure companion are both divisible by the next
power of two. Beyond that frontier, the companion has strictly shallower exact five-depth than
the phase perturbation. Either case contradicts the physical equal-depth shell. The surviving
distinguished raw-head rule grammar is now confined to the later all-`c` frontier: tail width
`h` at a regular head or `2β−2` at the exceptional head.

[`MM-S65`](SALVAGE.md#mm-s65-complete-all-c-rule-entry-extinction) extinguishes those final
all-`c` frontiers. At a regular head, the `81`-scaled companion and phase coefficients are both
`2^h`, so their equal-depth sum remains nonzero modulo five. At the exceptional head, the
`45`-scaled coefficients are `2 or 4` and `2`, whose sum is likewise nonzero. Both collisions
remain strictly shallower than the physical target. Leading and position-two rules were already
removed by `MM-S54` and `MM-S62`; no all-`c` rightmost-rule first entry survives. Generalized
carriers and singleton targets remain outside this assembly.

[`MM-S66`](SALVAGE.md#mm-s66-complete-rule-bearing-first-entry-extinction) closes the complete
rule-bearing branch. Factoring at the rightmost rule leaves an alphabet word that either
contains `b` or is entirely `c`; `MM-S60` kills the first arm and `MM-S65` the second. The sole
remaining distinguished raw-head first-entry class is all-erasure, already classified by
`MM-S53`.

[`MM-S67`](SALVAGE.md#mm-s67-complete-distinguished-first-entry-extinction) performs the final
phase split. Every physical role word is either the letterwise all-erasure block or factors at
its rightmost rule with an erasure tail. `MM-S53` and `MM-S66` kill these two arms. No
non-singleton physical block carries the distinguished two-`c` raw head into another multi-role
pole. The next audit must connect this empty first-entry language to the outer setter
projective-avoidance and mortality compiler, rather than reopening the grammar.

[`MM-M06`](SALVAGE.md#mm-m06-formal-decimal-setter-compiler) now owns that outer algebraic
surface. Lean checks the explicit decimal `5 × 5` matrices, delimiter ranks `3,2,1`, regular
role decoder, mixed rank-one separator, forward rational and integer compilers, and arbitrary
fracture at delimiter cubes.

[`MM-S74`](SALVAGE.md#mm-s74-triple-free-bridge-frontier) closes the formerly missing outer
parser and converse. A delimiter cube factors its bridge coefficient multiplicatively, so every
zero word contains a cube-free zero chunk. After boundary trimming, every such chunk parses into
`S²`-separated role blocks; all but the rightmost end in erasure, and the rightmost ends in rule.
The exact three-state execution excludes a lone root block. Mortality is therefore equivalent to
one erasure-ended block hitting a square-reset pole, with exactly three branches: singleton
target, non-singleton over one root block, or non-singleton over a deeper history. The live
mathematical seam is no longer word grammar: it is the adapter from an arbitrary square-reset
state to the physical shell hypotheses consumed by `MM-S67` and the separate singleton/deep
extinctions. Primitive-recursive emission of the cleared integer family remains independently
unproved.

[`MM-S77`](SALVAGE.md#mm-s77-shallow-generalized-raw-head-adapter) now closes that adapter's
algebraic and unit-shell half for a one-block root. If `H` is the full punctuated source upper
code and `Δ=μ·10^|upper|−H`, the shallow pole is exactly
`gap(10^β)·P·H=lift(10^β)·V·Δ`; parser law forces `H` and `Δ` to be decimal units, ending in
digits seven and three. The remaining shallow seam is structural rather than shell-theoretic:
`MM-S67` assumes a peeled two-`c` head and complement `10μ−H`, while the arbitrary parser root
has neither form. Prove a genuine ancestry normalization or attack the generalized equation
directly; do not silently substitute one head for the other.

[`MM-S79`](SALVAGE.md#mm-s79-minimum-body-lawful-shallow-pole) proves that the generalized
shallow equation has genuine physical solutions and therefore cannot be killed globally. On the
minimum slice `|body|=β−1`, `target=R_c::body.map D` has `P=V`, while `source=[R_c]` has
`9H=lift` and `9Δ=gap`; the parsed shallow pole follows identically. This is the unique lawful
terminal spelling of an immediately halting source, not a malformed witness. The universal
compiler remains separated because its emitted length is strictly larger than `β−1`. The next
shallow attack must use that length surplus or finer compiler grammar while preserving this
lawful normalization.

The ternary and decimal branches now separate at their first multi-transfer front.
[`MM-S37`](SALVAGE.md#mm-s37-decimal-three-shape-frontier-extinction) substitutes each of the
three role shapes left by the swapped ternary gate into the decimal carrier equation. All are
empty: [`MM-S18`](SALVAGE.md#mm-s18-length-two-carrier-extinction) kills the two-`c`
multi-to-multi step; [`MM-S20`](SALVAGE.md#mm-s20-singleton-carrier-classification) makes a
`(β+1)`-`c` multi-to-singleton step two digits too short; and its singleton-current theorem
kills `D_b` followed by any singleton independently of the preceding two-`c` block. This does
not make the ternary trichotomy a decimal classification. The decimal survivors remain the
longer generalized-carrier branches `m≥3` and `m≥β+3`, whose encoded reachability is the live
problem.

[`MM-O20`](SALVAGE.md#mm-o20-decimal-first-cylinder-collision) gives the unbounded suffix
language an exact metric: a backward word gains the sum of its shifts in both decimal valuations,
and one block maps the unit domain onto one exact suffix cylinder. But first-cylinder decoding is
not injective. The lawful blocks `R_bR_cD_b` and `D_bR_cD_b` have identical depth-`2β+3`
cylinders for every compiler-emitted body; their long common lower suffix hides the first phase.
The live cut is therefore the intersection of the encoded-entry orbit with complete composed
inverse branches, or a proved reachability-sound quotient of those branches. Neither a fixed
congruence graph nor the first unbounded cylinder retains enough information.

[`MM-S31`](SALVAGE.md#mm-s31-gcd-saturated-singleton-gate) removes the artificial choice of a
numerator-coprime factor. Set `c=gcd(q,N)` and `r=q/c`. Exact common-factor cancellation proves

```text
V₂=rW,       c(P₂−μ10^m)+gW≡0 (mod r).
```

Thus every partial contamination pattern retains one canonical strongest modulus. The
singleton gate disappears only after the complete gap divides the carrier numerator. The live
front is now whether reachable lower codes can install that full gap, or otherwise pass the
canonical quotient congruence together with the remaining suffix semantics.

[`MM-S36`](SALVAGE.md#mm-s36-complete-hidden-branch-separation) sharpens the first-cylinder
collision. The complete `R_bR_cD_b` and `D_bR_cD_b` inverse branches cannot collide at a common
tail: their difference has exact shell `(ℓ+4,ℓ+5)`, and every common outer word shifts both
depths equally. Equality with different later tails forces their difference into the unique shell
`(ℓ−2β+1,ℓ−2β+2)`. Emitted bodies have `ℓ≥2β`, so every hidden-phase switch injects a
positive-depth cross-prime gap. The live cut is the intersection of this exact shell with pairs
of suffix carriers reachable from the encoded entry, or an explicit branch-switch cascade
realizing it.

The swapped ternary first multi-transfer branch is no longer unrestricted.
[`MM-S35`](SALVAGE.md#mm-s35-first-multi-transfer-trichotomy) proves that every expected-shell
pole after the first transfer passes through one of three exact role shapes: `cc` into a
multi-role target, `c^(β+1)` into a singleton, or `cc` then the literal singleton `D_b` into a
singleton. The only equal-depth singleton branch is impossible by an exact normalized-unit
calculation. These are necessary shapes, not witnesses; attack their complete suffix equations
before extending the carry to greater depth.

[`MM-S38`](SALVAGE.md#mm-s38-two-c-singleton-b-extinction) kills the last of those three shapes
for both singleton targets. The two pole expressions factor into strictly negative cubic and
quintic products after the shift `ρ=t+27`; the result is independent of the initial two `c`
phases and of the compiler body. The first swapped-ternary multi-transfer front now has two
letter branches: `cc→multi` and `c^(β+1)→singleton`.

[`MM-S44`](SALVAGE.md#mm-s44-compiler-envelope-rule-bearing-extinction) collapses their phase
grammar. Under the exact compiler envelope `|body|≥β−1`, `head(body)=b`, any middle occurrence
of `R_c` forces the normalized second-transfer discrepancy outside the target-pole interval:
`Δ≤0` for a `c`-leading first block and `Δ>3μ` for a `b`-leading one, whereas every physical
target requires `0<Δ<3μ`. Combined with `MM-S35` and `MM-S38`, the first multi-transfer front
then consists only of the literal blocks `D_c²→multi` and `D_c^(β+1)→singleton`.

[`MM-S50`](SALVAGE.md#mm-s50-long-all-erasure-singleton-extinction) kills the long branch.
For `D_c^(β+1)`, the exact codes `V_m=3ρ−1` and `2P_m=9ρ²+ρ−2`, together with the universal
incoming bound `q<1`, force `Δ>12`. Either singleton target forces `Δ<12`. The sole first
multi-transfer survivor is therefore `D_c²→multi`.

The remaining carrier is not the integral raw-fringe state consumed by the positive depth-one
classifier: its discrepancy `(14ρ−1)/3−8Hq/(3(ρ−2))` is generally rational and depends on the
preceding punctuated upper cylinder. [`MM-S52`](SALVAGE.md#mm-s52-double-deletion-raw-ancestry-obstruction)
proves that this is a real interface failure. For a first block of upper length `m` and
punctuated code `P`, integrality after `D_c²` forces `P∣8Hμ`; the locally physical repeated
`D_c²` state has `P=14ρ−1` and violates that divisibility for every `β≥3`. Hence no local splice
can follow from the carrier shape and recurrence alone. The same record proves the sharp positive
statement: for a nondegenerate rational carrier, the next-block pole equation is exactly the
rational depth-one equation, and an integral normalization specializes exactly to
`PositiveDepthOnePole`. A lawful `MM-S42` splice must still derive integrality, a raw digit-code
difference, and common-suffix ancestry from the global orbit. The repeated state is not claimed
reachable from the distinguished entry and does not kill the actual first-transfer survivor;
its separate direct ratio-cylinder extinction is `MM-S51`.

The positive depth-one ternary question is now closed at its exact witness interface.
[`MM-S42`](SALVAGE.md#mm-s42-swapped-positive-depth-one-extinction) reduces every regular
valuation-one fringe after one positive distinguished-boundary transfer to four pairs. The two
outer discrepancies are the impossible `Δ₁` and `Δ₃` Neary residuals; both middle discrepancies
equal `H`, so the exact pole forces equality of the upper and lower swapped codes and hence source
halting. The compiler width `β=10·period` lies safely above the analytic threshold `β≥6`.

This does not construct a `PositiveDepthOnePoleWitness` from an arbitrary raw orbit. The witness
retains physical target-suffix provenance, while the terminal proof consumes only its target
grammar, pole congruence, exact factorizations, and exact pole. The surviving ternary questions
therefore begin at genuinely multi-transfer carriers, not at another refinement of the four
one-transfer fringe candidates. The separate distinguished-boundary singleton `β`-shell is now
formally closed by `MM-S08`; the later `D_c^(β+1)` singleton branch remains a different carrier
and is handled algebraically in `MM-S50`.

[`MM-S51`](SALVAGE.md#mm-s51-double-deletion-ratio-chamber-extinction) kills that final
survivor without an integral fringe splice. The exact `D_c²` discrepancy and the full incoming
upper cylinder force any following physical pole to have target ratio

```text
2/3 < V_t/P_t < 3/4.
```

No physical role block emitted against a body beginning in `b` occupies this chamber. Generic
nonzero-ternary bounds reduce a hypothetical target to two adjacent word-length cases; the
leading swapped prefixes exclude each case, with exact induction through an initial `D_c` run.
Thus `firstMultiTransfer_pole_false` empties the expected-shell first multi-transfer interface
for `β≥6`.

[`MM-S55`](SALVAGE.md#mm-s55-physical-role-block-shell-completion) proves that the shell
hypotheses are automatic. Every physical role block supplies its expected depth, exact
coefficient valuation, and lower-code unit; every first role block except literal `D_c` has
upper length greater than one. Consequently `physicalFirstMultiTransfer_pole_false` needs only
three physical role blocks, the compiler envelope, and the exact centered two-step pole
equation.

[`MM-S57`](SALVAGE.md#mm-s57-centered-history-defect-transport) isolates the exact history
constructor. A physical step lands on its canonical raw-head ray if and only if its incoming
state lies on the ordinary-reset ray. The distinguished reset already misses that ray by `R²`,
so sliding the first-multi window is formally invalid. For arbitrary first, middle, and target
blocks, the prospective pole is the canonical `MM-S55` residual plus one explicit multiple of
the incoming ordinary-reset defect. A genuine ordinary-ray return therefore activates `MM-S55`
and is impossible at the next nontrivial first-multi pole.

[`MM-S59`](SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry) supplies the suffix invariant
that remains valid off the ordinary ray. If `(n,d)` represents the normalized projective defect,
a target pole satisfies `dP=nV`. Least-significant swapped digits produce an exact balanced
carry in the finite interval `[-(|n|+|d|), |n|+|d|]`; reversed Neary erasure and rule blocks are
explicit affine contractions. For a target ending in `β` erasure tiles, the shared terminal
suffix forces `3^β ∣ d−n`. Hence `|d−n|<3^β` makes the pole terminal and invokes the checked
decoder.

[`MM-S61`](SALVAGE.md#mm-s61-primitive-carrier-gap-no-go) proves that reachability alone cannot
supply that last inequality. The exact integral update is

```text
n'=H((P−μA)d−Vn),      d'=R(Pd−Vn),
d'−n'=μ(HAd−3(Pd−Vn)).
```

One literal `D_c` from the distinguished reset has a primitive gap `μ>3^β`; two have primitive
gap `3^βμ`, already a nonzero multiple of the suffix modulus. Both pairs and their centered
reachability are Lean-checked. Thus both the universal height bound and bare modular
nondivisibility are dead.

[`MM-S63`](SALVAGE.md#mm-s63-full-tail-last-step-resonance) recovers an exact target-coupled
constraint. If the last raw update is `s(n',d')` and primitive `(n',d')` reaches a nonterminal
full-erasure-tail pole, then

```text
upperLength(last block)=v₃(s)+1.
```

Primitivity and the target congruence automatically make both adjacent carrier denominators
units. The equality follows by comparing the required deep output gap with the two summand
depths in the `MM-S61` raw gap factorization.

[`MM-S64`](SALVAGE.md#mm-s64-unique-predecessor-cylinder) spends that equality rather than
refining it. If `E=P_zd−V_zn` and `a=upperLength(z)`, the same full-tail pole forces

```text
3^(a+β−2) ∣ E−3^(a−1)Hd.
```

Thus the last block selects one predecessor cylinder to precision `a+β−2`. For literal `D_c`
this is `3^(β−1)∣n`. The constraint is sharp on the distinguished deletion spine, whose first
primitive numerator already contains that power; it is a backward-ancestry interface, not a
contradiction.

[`MM-S68`](SALVAGE.md#mm-s68-backward-numerator-resonance) pulls the selected numerator
cylinder through the preceding physical block. If its nonzero primitive successor numerator
contains `3^(β−1)` and the preceding upper length is `a`, the preceding normalization discards
exactly `a` powers of three and the antecedent satisfies

```text
3^(a+β−1) ∣ (P_we−V_wm)−μ3^a e.
```

For literal `D_c`, this cylinder is exactly `3^β∣e−m`. The zero-numerator fork is terminal.
Hence two final literal deletions before a full-tail pole either expose a genuine source halt or
toggle the carrier before them into the full-gap cylinder.

[`MM-S69`](SALVAGE.md#mm-s69-sequential-double-deletion-zero-gap-extinction) removes the
toggle's zero-gap survivor. The explicit distinguished carrier after two sequential singleton
`D_c` transfers gives, after stripping the common target tail,

```text
d₂U−n₂L=μ(3^β−1).
```

Modulo three forces the lower prefix code `L` to vanish; the remaining equation contradicts
`d₂>μ(3^β−1)`. Thus the consuming two-block theorem now returns a genuine halt or a **nonzero**
full-gap predecessor. This is distinct from `MM-S51`: sequential singleton transfers retain a
square-run boundary and are not one `[D_c,D_c]` role block.

[`MM-S71`](SALVAGE.md#mm-s71-three-block-backward-frontier) now performs the next pullback with
every primitive normalization boundary explicit. Let the physical block `w` immediately before
the two singleton deletions have upper length `a`, discarded scale depth `g`, and predecessor
residual `E=P_we−V_wm`. A nonterminal full-tail pole either halts or forces

```text
a=g+1,      3^(g+β−1) ∣ E−3^gHe.
```

The first non-`D_c` ancestor is therefore isolated as one exact cylinder of precision
`a+β−2`; no normalization or sequential boundary remains implicit in that local node.

[`MM-O27`](SALVAGE.md#mm-o27-reachable-predecessor-cylinder) shows that this cylinder cannot be
emptied locally. For `β=3`, body `bbcc`, the ordinary-reset history `[R_c,D_c]²` reaches a
primitive carrier for which a third `[R_c,D_c]` normalizes at the required depth and produces a
nonzero gap divisible by `27`; the exact predecessor residual is also divisible by `27`. This is
not a pole. It kills a block-grammar-only extinction and forces the next argument to retain the
target carry or an earliest-pole ancestry condition.

[`MM-S73`](SALVAGE.md#mm-s73-live-three-block-charge-frontier) retains both. The reachable
cylinder quotient `k₀`, the nonzero gap quotient `q₀`, the intervening deep-numerator quotient
`k₁`, and the peeled target charge `q₂` satisfy

```text
μk₀=−u₀q₀,      u₁k₁=H(2q₀−d₀),      u₂q₂=2μk₁,
```

where every `uᵢ` is a three-adic unit. The prospective target's balanced carry after its matched
`β`-erasure tail is exactly `(3^β−1)q₂`. The same survivor forces the origin and both intermediate
product boundaries to be live, so local earliestness does not empty it; earliestness can act
only before the three-block window. Eliminating the two interior charges yields the single
braided identity

```text
u₀u₁u₂·((3^β−1)q₂)=−2μH(3^β−1)·(2μk₀+u₀d₀),
```

which converts the target-blind congruence into one exact target-carry ancestry equation.

[`MM-S76`](SALVAGE.md#mm-s76-primitive-target-multiplier-braid) identifies that charge with the
physical target prefixes. Primitivity gives a unique three-adic-unit multiplier `λ` with
`P=λn₂`, `V=λd₂`, and `Δ=L−U=λq₂`. Hence

```text
u₀u₁u₂Δ=−2μHλ(2μk₀+u₀d₀).
```

The last unequal discarded digit makes the literal discrepancy a unit unconditionally, and the
braid forces the predecessor residual to be a unit. Pulling that digit backward gives the exact
fork

```text
front=[] => 3∣k₀,       front≠[] => k₀≡e₋₁ (mod 3).
```

The required carrier residues in both arms occur on reachable width-three local chains, so the
first non-`D_c` block grammar does not finish the argument. The empty arm has
`V=3^β−1=λd₂`, hence `λ∣(3^β−1)` and a bounded primitive denominator, but all eight width-three
erasure targets survive the exact local shell equations. The nonempty arm requires a
higher-prefix ancestry invariant.

The remaining ternary obligation is now the **nonzero history-defect branch** of the global
earliest-pole reduction. In the normalized coordinate `δ=D/y`, the complete physical recurrence
is

```text
δ'=[R(P−μA)−HVδ]/[RP−HVδ],      pole at δ=(R/H)(P/V).
```

The distinguished coordinate `R/H` is a target threshold exactly for terminal equality `P=V`.
The first `D_c` and `D_b` images lie on opposite sides of zero, so a one-sided real trap is
already impossible. On the full-erasure-tail branch, backward ancestry now has an exact
two-state numerator/gap toggle through literal `D_c`, and its zero-gap return is dead. The live
local question is the target prefix preceding the matched erasure tail. `MM-S73` exhausts local
earliestness and `MM-S76` exhausts the terminal residue without a contradiction; any remaining
earliestness input lies before the three-block window. More
importantly, this branch is not the global target grammar: a physical role block ends in only one
erasure tile, not `β` of them. A complete proof must either force the long tail at an earliest
false pole or extend the carry/cylinder invariant to arbitrary physical target suffixes. Fixed
residue and unit projections are empirically saturated, and the exact carry window grows with
carrier height. None of `MM-S51`, `MM-S55`, `MM-S57`, `MM-S59`, `MM-S61`, `MM-S63`, `MM-S64`,
`MM-S68`, `MM-S69`, `MM-S71`, `MM-O27`, `MM-S73`, or `MM-S76` alone proves projective avoidance.
Exact bidirectional diagnostics for the ternary swap at `β=3`, body `bbcc`, exclude every
false-pole word of at most six projective blocks when each regular block has
role length at most three; this is computational evidence only.
A single explicit nonterminal pole orbit kills this family; a closed invariant proves
`M₅(3)`. The same-zero binary root and fixed-width-three source remain independent fallbacks.

### 3. Two-generator realization: `M₉(2)`

The canonical prefix-pair obstruction is complete. The physical word `000` in the restricted ten-state
pair is rank one, but its scalar sandwich has exact Hankel rank ten. More strongly, the word
products of the pair span `M₁₀(ℚ)`
([`MM-O08`](SALVAGE.md#mm-o08-full-algebra-prefix-pair)). The pair therefore has no nonzero
proper invariant subspace or quotient, and every nonzero internal-word sandwich has exact
realization dimension ten. Common-image restriction, kernel quotient, reachable/observable
minimization, and internal punctuation cannot reach nine states from this pair.

The successful construction changes the physical pair and its nonzero values while preserving
zeros. A literal binary prefix tree for five source symbols has
four internal states, while a literal two-state ternary tree cannot obtain a five-state
common-image restriction ([`MM-O09`](SALVAGE.md#mm-o09-two-state-ternary-prefix-image)).
The stronger factorized cross-ratio wall
([`MM-O17`](SALVAGE.md#mm-o17-factorized-binary-cross-ratio-wall)) now closes both natural exact
nine-state escapes. Arbitrary invertible edge factors, state-fibre gauges, and independent
nonzero source scalings cannot compress any five-leaf binary prefix transducer to a
nine-dimensional common image: dimension nine forces the four ordinary roles onto one
factorized rectangle, but all three Neary cross-ratios fail. A native three-phase `3×3` cyclic
cube fails for the same reason. Its rank-one separator forces the four invertible roles onto the
opposite cube face. Pure width-three comma-free coding carries at most two symbols, and the one
exact positional four-role cube admits a checked false terminal witness on the nonhalting source
`(3,bbcc)`.

Thus neither another exact prefix layout nor an exact three-phase block factorization survived.
Before `MM-C05`, the remaining routes were a changed zero series, a nonfactorial state-dependent
decoder, another invariant quotient not induced by the generators' common image, or a nonlinear
reduction; `MM-C05` takes the first route. A different singular same-zero/history family is
governed by [`G3-O27`](SALVAGE.md#g3-o27-projective-toggle-line-atlas): if both data stages are
singular and the absorbed trailing toggle is projectively involutive, its projective history
remains in a six-carrier line atlas. That obstruction remains relevant below rank nine.
`GPCP(3)` is the independent stronger ancestor.

[`MM-O19`](SALVAGE.md#mm-o19-trailing-toggle-exact-prefix-tax) tests one changed-source seam.
Because the paired toggle satisfies `T²=I`, moving one toggle into the terminal column preserves
existence of a nonempty zero for every source body and every control word. The shifted separator
then shares the data generators' three-dimensional image plane. This reaches an exact
variable-fibre comb with profile `4+3+3=10`, but the same rank profile is a lower bound for every
direct-sum exact four-role prefix layout: the rank-four toggle taxes its root path and a
rank-three deep data leaf taxes both remaining fibres. Balanced layouts cost at least eleven.

This closes code reassignment, variable prefix-fibre dimensions, and exact boundary-orbit
factorization for the paired four-state source. It does not touch overlapping fibres or
cross-path sums. The sharp next experiment is therefore a singular, history-sensitive compiler
which preserves only existential zero reachability; exact internal-role products are already too
rigid. See
[`audits/m92-trailing-toggle-prefix-tax-2026-08-30.md`](audits/m92-trailing-toggle-prefix-tax-2026-08-30.md).

[`MM-O23`](SALVAGE.md#mm-o23-consecutive-transfer-moment-tax) now reaches the first genuinely
overlapping architecture. Write the binary pair as `(A,UV)`, with a four-dimensional cut. Runs
between cuts are decoded by `Mᵣ=VAʳU`, so every path shares the same ambient coordinates and may
interfere with every other path. A finite transfer Hankel section still factors through that
ambient space. For the width-three body `bb`, if three consecutive moments are nonzero
rescalings of `T,D_b,D_c` in any order and every later moment is the absorbed separator, an exact
`10 × 10` minor is nonsingular in all six orders. Thus this cross-path architecture also needs at
least ten states.

[`MM-O24`](SALVAGE.md#mm-o24-sparse-transfer-moment-tax) removes nonconsecutive placement as an
escape within the same exact moment family. If the last of the three distinct role positions is
at least three, four reversed time blocks expose a nonsingular `12 × 12` section after
subtracting the rank-one separator tail. Restoring that tail costs one coordinate, so the
ambient space has dimension at least eleven. Otherwise the positions are exactly `0,1,2`, and
`MM-O23` gives ten. Thus every distinct placement of the unchanged roles with a constant `P′`
tail misses nine states.

[`MM-O25`](SALVAGE.md#mm-o25-moving-tail-transfer-tax) charges a nonconstant comparison tail by
its own exact realization dimension. If two exact series of dimensions `n,h` agree after time
`m` and their last difference has a rank-three minor, all `m+1` reversed blocks give
`3(m+1)≤n+h`. Thus a tail with `h≤2` cannot hide a late paired role inside nine ambient states;
more generally nine states require `h≥3(m+1)−9`.

[`MM-O26`](SALVAGE.md#mm-o26-geometric-tail-transfer-tax) closes the missing one-state tail at
the consecutive positions. Replacing the constant separator by `τP′,τ²P′,…` for any `τ≠0`
multiplies the six `MM-O23` determinant certificates only by nonzero powers of `τ`. Every order
of `T,D_b,D_c` therefore still needs ten states.

[`MM-C05`](SALVAGE.md#mm-c05-tilted-separator-rank-nine-transfer) breaches and closes that wall
by changing the separator row. Explicit rational functions give moments
`T,D_b,D_c,ux,sux,s²ux,…` with an audited nine-state `3+3+2+1` realization. The row ratio
`q=(K−3V)/(K−3)` is below `−3/2`; Lean proves that the tilted code
`ternaryCode(w)+q·3^|w|` remains injective. Hence the changed row preserves the scalar zero set
for every paired control word and both phases, including trailing-toggle absorption. This is the
first exact rank-nine same-zero transfer core, not another finite-depth candidate.

Lean now checks the entire rational chart and its mortality semantics. The first three returns
are exactly the toggle and two data roles; every later return is a nonzero geometric multiple of
the tilted separator. A nonzero tail eigenline excludes pure transition zeros. The generic
singular-return theorem sandwiches any physical zero by the output and input, retaining both
exterior waits as returns; no splitting or exterior-kernel classification is required. Every
return is a nonzero scaling of one of the four tilted roles, and a right-inverse relabelling
reduces their mortality exactly to the paired scalar zero language.

The integer emitter evaluates the chart in primitive-recursive unreduced fractions and clears
each `9 × 9` generator by one certified nonzero common denominator. Its entries are primitive
recursive without rational normalization or gcd computation. Cook–Neary bodies carry the checked
leading-`b` invariant required by the chart. Consequently
`UniversalNeary.codeHalts_reduces_mortality92` is a primitive-recursive many-one reduction from
code halting, and `UniversalNeary.mortality92_not_computable` proves `M₉(2)` undecidable. Zero
padding gives `M_d(2)` for every `d≥9`.

[`MM-O28`](SALVAGE.md#mm-o28-tilted-geometric-tail-rank-nine-wall) proves that this benchmark
series has exact transfer rank nine uniformly over every rational tail amplitude and eigenratio
and every tilted-row parameter `q<−3/2`. Four sparse `9 × 9` minors cover zero tail, generic tail
scale, and both exceptional-pivot branches. Thus `M₈(2)` cannot follow by retuning the one-state
tail or the tilted separator while retaining `T,D_b,D_c` as the first three exact returns. The
next contraction must change an early return, use a non-geometric or multi-mode mechanism, or
preserve only the existential zero language.

See
[`audits/m92-run-length-transfer-hankel-2026-08-31.md`](audits/m92-run-length-transfer-hankel-2026-08-31.md),
[`audits/m92-sparse-transfer-hankel-2026-08-31.md`](audits/m92-sparse-transfer-hankel-2026-08-31.md),
[`audits/m92-moving-tail-transfer-hankel-2026-08-31.md`](audits/m92-moving-tail-transfer-hankel-2026-08-31.md),
[`audits/m92-geometric-tail-transfer-hankel-2026-08-31.md`](audits/m92-geometric-tail-transfer-hankel-2026-08-31.md),
[`audits/m92-tilted-geometric-tail-rank-nine-2026-08-31.md`](audits/m92-tilted-geometric-tail-rank-nine-2026-08-31.md),
and [`audits/m92-changed-separator-transfer-2026-08-31.md`](audits/m92-changed-separator-transfer-2026-08-31.md).

### 4. Three-letter correspondence and direct mortality: `M₃(4)`

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
Z₃(3), M₃(4), R₃(4), R₄(3), Z₅(2), R₆(2),
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

Several broad compressions are now excluded.

The exact nonerasing macro obstruction
[`G3-O01`](SALVAGE.md#g3-o01-four-role-macro-irreducibility) proves that no
fixed rolewise macros over three source letters reproduce these four word pairs exactly.
Unequal macro lengths, noninjective role codes, and failure of prefix-freeness do not help.
A surviving compiler must initially leave exact nonerasing role factorization. Lean checks the
obstruction as `ExactNearyMacroFactorization.four_le_card`.

The paired-Parikh obstruction
[`G3-O08`](SALVAGE.md#g3-o08-erasing-and-stationary-closed-block-obstruction) closes the obvious
escapes. The four role pairs have four independent additive bit-count channels whenever the body
contains `b`; hence fixed exact macros still require four physical letters when either target
morphism erases and the macro words are empty, coincident, or nonuniquely decoded. Lean checks the
complete factorization theorem. An audited extension permits arbitrary fixed boundary fragments
and output overlap, requiring only that one rule plus `β−1` deletion spellings return to a common
residual. It excludes every such stationary closed-block ternary encoder for `β≥4` and a mixed
body; Lean checks its complete integral case reduction. The universal Neary family satisfies
these hypotheses.

[`G3-O13`](SALVAGE.md#g3-o13-rational-serializer-pumping) now closes the finite-control escape.
An asynchronous transducer encoding arbitrarily large powers of four explicit blocks pumps to a
stationary physical return, even with state-dependent and nonunique spelling, nonfactorial
overlap, erasure, fixed contexts, and unbounded side lag. Three `b`-head pulses consume all three
physical letters with lower image in `b*`; the mixed `c`-head pulse then contradicts them. The
checked block equation includes arbitrary null histories. Separately,
[`G3-D01`](SALVAGE.md#g3-d01-bounded-prefix-residuals) makes any supplied computable bound on
accepting prefix discrepancy decidable. A live ternary compiler must therefore use a
solution-sensitive or nonrational domain and an unbounded, non-effectively bounded word residual,
preserving final solvability without exact side transport.

[`G3-D02`](SALVAGE.md#g3-d02-virtually-cyclic-prefix-discrepancy) cuts further into that global
leaf. Even if only one computably selected witness per yes-instance is normal, a finite union of
capped periodic residual rays reduces exact discrepancy evolution to one-counter reachability.
The arbitrary-word converse then makes search within that decidable subclass sound. Fixed caps,
orientation changes, overlapping rays, erasure, regular modes, and an indefinitely open carrier
do not help. The residual must retain at least two independent unbounded factors, unbounded word
order at fixed length, or a halting-dependent normal form unavailable to the reduction.

[`G3-D04`](SALVAGE.md#g3-d04-priority-affine-residual-atlas) closes every finite-dimensional
fixed-priority affine-counter enlargement of that normal form. Modes, arbitrary counter
reversals, recurrent exact tests, and any computable number of independent factors remain
decidable whenever updates are translations guarded by constants on one nested initial segment.
The reduction is to VASS with nested zero tests; Lean checks the exact debit-test-credit macro and
the finite atlas theorem is audited against the LICS 2025 reachability result. A surviving global
residual must therefore use incomparable or changing-priority tests, transfer/reset/copy
operations, genuine word order, or a halting-dependent atlas unavailable to the reduction.

[`G3-D05`](SALVAGE.md#g3-d05-priority-triangular-transfer-atlas) removes the first apparent
escape. Reset, destructive transfer, fanout, and arbitrary fixed multiplication remain
decidable when each operation drains the current priority frontier and deposits only into later
counters. Lean proves that the nested exit forces exactly the old counter value many loop
iterations and that reset strictly exceeds every finite union of translations. The audited
cascade still reduces to the same VASSnz theorem. The live global mechanisms are now feedback or
backward transfer, source-preserving copy, cyclic reuse of priorities, counter products,
incomparable or changing tests, literal word order, or a noncomputable atlas.

The body-independent Hankel certificate
[`MM-O04`](SALVAGE.md#mm-o04-uniform-rank-four-paired-series) proves that the
current three-control paired coefficient series has exact rank four already on `{b,t}*`.
Similarity, exact quotient or restriction, and nonzero per-letter rescaling cannot produce a
three-state realization. A surviving matrix route must change the nonzero values and preserve
only the zero language, or replace the compiler.

The rational phase-fracture obstruction
[`G3-O02`](SALVAGE.md#g3-o02-rational-phase-fracture) closes the next same-zero route. On every
mortal paired instance, the compressed suffix point cannot be a rational function of the checked
local suffix point and phase. This includes linear projective gluing, rational gauges, Cremona
identifications, and rational collapses to a curve or line, even with singular target controls.
The terminal contradiction and invariant-pencil rigidity core are Lean-checked; the general
function-field rigidity is independently audited. A surviving paired compression must retain
word history absent from the four-state suffix vector.

[`G3-O03`](SALVAGE.md#g3-o03-history-sensitive-minimal-body-fracture) realizes that escape and
closes the proposed instancewise response. Pro's claim that every admissible mortal instance has
one terminal role word is false: width three with body `bcbb` has two distinct Lean-checked
terminal histories. For every minimum-length body, however, the unique terminal word
`R_c :: body.map E` has an injective base-five code recognized by three explicit states on every
control word. The rank-one lift gives four integral `3 × 3` matrices with a complete
arbitrary-product converse. Their phase graph closures are audited full products with
one-dimensional generic fibers. Thus generic single-valuedness of all three-state phase graphs is
false. The data maps are singular but retain an injective decoded-history code, so rank drop alone
cannot force a positive residual collision. The construction is not a reduction: its target code
is a terminal witness, and the report supplied no total source-computable replacement on arbitrary
bodies.

[`G3-O04`](SALVAGE.md#g3-o04-expanding-affine-history-no-go) closes the first uniform
replacement class. One source-dependent expanding affine history coordinate, any finite mode
graph, and finitely many affine target fibers have an exact finite reverse automaton after
denominator clearing. Mixed signed radices, arbitrary digits, collisions, rational conjugacy,
and an instance-dependent number of modes do not help. Lean checks the all-word normal form,
reverse box, exact caged DFA, regularity, and noncomputability of universal paired zero
existence. The finite-chart claim requires one shared affine coordinate; arbitrary rational curve
reparameterizations remain outside it. A surviving history compiler must use genuinely
two-dimensional projective dynamics, an infinite target section, nonexpanding or
denominator-generating arithmetic, or a singular ideal without effective affine normalization.

[`G3-O05`](SALVAGE.md#g3-o05-cancellative-projective-state-tax) separates static projective
incidence from dynamics. Lean constructs one rational conic factorization of the complete paired
prefix-suffix zero support, so every finite support submatrix has rank at most three. No
support/minrank certificate can prove a four-state same-zero lower bound; common shift maps must
carry the contradiction. The governing representation principle is
[`G3-S01`](SALVAGE.md#g3-s01-shift-equivariant-zero-incidence): same-zero dimension is
shift-equivariant projective incidence dimension. Conversely, if a two-coordinate construction
extends the upper and lower word sides to independent inverse actions and preserves the target
law on every formal inverse state, its role group contains a freely acting `F₂×F₂`. Such a
saturated projective recurrence needs at least four vector dimensions. The surviving projective route must therefore
be intrinsically one-way: inverse states or their target law must fail, or a singular map must
destroy the cancellative orbit.

[`G3-O11`](SALVAGE.md#g3-o11-positive-shifts-do-not-force-saturation) proves that this escape is
real, not a missing lemma. Three explicit rank-two integral matrices have complete zero language
`{t}`, full reachable and observable context matrices, no zero product, and an injective positive
semantic labeling into a group containing `F₂×F₂`. Yet the `b`-shift identifies the columns of
`ε` and `t`. Positive shift equations therefore do not imply inverse saturation.

[`G3-O17`](SALVAGE.md#g3-o17-paired-inverse-chamber) now closes the paired-specific repair.
Every actual suffix residual has reduced sign form `+*−*`, and every phase-aware prefix residual
has form `−*+*`. Two explicit formal inverse states required by the independent left and right
free factors contain both sign turns. Every Neary upper role ends in `z` and every lower role ends
in `x`, so no positive role continuation cancels either protected turn. Lean proves both complete
forward cones disjoint from every actual residual. Grammar-intrinsic inverse cofinality and every
Ore/common-future version of the saturation leaf are therefore false. A lower bound must use a
finite positive projective transition diagram with actual ranks, kernels, images, and base loci;
formal group completion is no longer a raceable argument.

[`G3-O06`](SALVAGE.md#g3-o06-periodic-ray-completion-and-branching-fracture) closes the concrete
`bcbb` lane completely. Its null histories are exactly `(bbb,cbb)^k`, its terminal language is
one periodic ray, and a singular three-state affine decoder recognizes it on every control word.
The resulting four explicit integral matrices have a complete arbitrary-product mortality
converse. The adjacent body `bcbc` is the first certified branching wall: two distinct
equal-length null blocks concatenate according to arbitrary bit words, producing `2^n` terminal
words at one length. Lean consequently excludes every single affine row section of the injective
positional decoder. Lean now also proves the complete null grammar `(X(DZ)*F)*` and terminal
grammar `FD(X(DZ)*F)*` from a canonical residual path.

[`G3-O07`](SALVAGE.md#g3-o07-near-fork-carry-collision) closes the next attempted consumption of
that branching. One terminal `bcbc` prefix and one same-length nonterminal near-fork collide
whenever the internal stroke paths obey `DZ=FX` on a witness recoverable through two erase-`b`
steps. Lean proves this without dimension or invertibility assumptions. For the proposed
one-projective-coordinate phase-line controls, the two full physical products are equal matrices
for every rational parameter away from the denominator pole. Thus rational contraction and
singular phase reset do not rescue a scalar stroke carry. The unproved step is now internal:
arbitrary three-state fork zeros need not identify partial-factor images before their common
return to the terminal plane.

[`G3-C02`](SALVAGE.md#g3-c02-fixed-bcbc-singular-recognizer) reverses the local verdict. A
different singular three-state system uses one expanding integer carry and a transient first
coordinate. Lean checks its all-control recurrence and every canonical terminal zero; an audited
finite reverse graph gives the arbitrary-control converse. Thus `bcbc` has rational same-zero
dimension at most three and cannot support the desired lower bound. The construction is
instance-fitted and regular: a source-uniform finite-target version remains excluded by
`G3-O04`. The paired route's live obstruction is now uniformity across bodies, not the state
dimension of this fixed branching language.

[`G3-C05`](SALVAGE.md#g3-c05-equal-length-mixed-branching-recognizer) sharpens that verdict on
the body `bcbcbb`. Its complete grammar is `P₀(A₀|B₀)*`, with two distinct equal-length null
blocks and therefore `2ⁿ` terminal histories at every block depth. Lean proves an explicit
integral three-state recognizer equal to the paired zero language on the entire raw control
monoid. The proof scours arbitrary toggle pairs and kernel-checks the complete inverse
congruence graph, including both dead competing branches. Equal-length branching, exponential
same-level growth, finite return flowers, and common-kernel guard refresh are therefore not
positive projective obstructions. Any surviving lower bound must obtain incompatible shifts
uniformly from an unbounded terminal section; another fixed finite flower is closed.

[`G3-O12`](SALVAGE.md#g3-o12-positive-reset-dimension-tax) removes the residual-local response.
If both legal prepend cylinders of a reverse-queue code span the three-state space, their data
maps are invertible. At the wholly legal queue `qb`, the `b`- and `c`-rule equations then force
the persistent states of `q` and `ε` onto one projective ray. The standard two-coordinate radix
code has nonzero cylinder determinant `B²(B−1)(d_b−d_c)`, even with denominator growth or a trap
outside the legal locus. A surviving uniform constructor must be history-sensitive and singular
on legal inputs: at least one full cylinder must lie in a plane, while a transient coordinate
remembers enough route information to police the forced persistent collision.

[`G3-S02`](SALVAGE.md#g3-s02-rank-two-kernel-bifurcation) splits that singular escape into two
real architectures. With one common data kernel preserved by the toggle, a difference in that
kernel is erased by the first later data action, so the computation factors through the quotient
between data controls. Toggle invariance is not forced: the exact `bcbb` compiler moves its common
kernel out and recovers it nontrivially at the next data action. The live common-kernel mechanism
is therefore a non-invariant shuttle, not persistent refresh. With transverse data kernels, the
two quotient fibres meet in the exact bilinear ray `[rv:us:vs]`. Neither architecture is yet a
source-uniform recognizer.

[`G3-S04`](SALVAGE.md#g3-s04-symmetric-square-collision-and-fork-obstruction) identifies the
canonical irreducible three-coordinate alternative and then cuts its direct fork use. The
covariant `Sym²` action carries `(x,y)` to `(x²,xy,y²)` and turns one projective incidence into
the integral scalar `Δ(u,v)²`, with zero exactly at collision and a gap of at least one otherwise.
But three Veronese columns have determinant
`Δ(u,v)Δ(u,w)Δ(v,w)`. In conjunction with `G3-S03`, every complete-fork Sym² orbit in the forced
line or plane contains at most two projective rays. Hence a direct non-elementary Sym² fork is
impossible; only the already elementary invariant-point or invariant-pair dynamics survive.
Sym² consumes all three states and provides no malformed-word guard or directional inverse law,
so an extra insertion must justify its state budget rather than remain implicit.

[`G3-S05`](SALVAGE.md#g3-s05-fixed-full-rank-symmetric-square-leakage-no-go) removes the
full-rank version of that insertion. For arbitrary fixed `3×3` leakage `L` between binary
coordinate changes `P,Q`, Lean factors the transported three-ray determinant as
`det(P)³det(L)det(Q)³Δ(u,v)Δ(u,w)Δ(v,w)`. Three distinct rays cannot enter the planar
`G3-S03` carrier through nonsingular `P,Q,L`. Any fixed word-independent leakage must therefore
be singular; word-dependent, source-dependent, and explicitly rank-dropping mechanisms remain.

[`G3-S07`](SALVAGE.md#g3-s07-fixed-rank-two-symmetric-square-leakage-is-elementary) now kills
the rank-two fixed branch when it supports one quotient action on three distinct source rays.
Those Veronese rays span, so pointwise compatibility is a global intertwiner. Its one-dimensional
kernel is a common Sym² eigenline. A degenerate kernel tensor gives a common rational fixed ray;
a nondegenerate tensor gives a traceless twist `T` with `T²=δI`, and every binary generator
commutes or anticommutes with `T`, hence preserves or swaps its two algebraic eigendirections.
Thus no genuinely non-elementary binary pair survives this fixed equivariant rank-two seam.
Rank at most one, dynamically varying leakage, and nonspanning orbits remain open.

[`G3-S09`](SALVAGE.md#g3-s09-fixed-symmetric-square-leakage-taxonomy) closes rank one and
packages the full fixed taxonomy. Transposing a rank-one intertwiner makes its row line a common
dual Sym² eigenline. The resulting rational quadratic covector either has one rational root ray
or a nondegenerate algebraic root pair normalized by every generator. Rank zero is the zero map.
Hence every singular fixed Sym² intertwiner is zero or elementary. With three distinct source
rays, pointwise quotient equations become global and a dependent leaked image forces
singularity, so `G3-S05`, `G3-S07`, and `G3-S09` eliminate every fixed rank. Two rays do not
determine a three-state map: Lean exhibits the surviving middle-coordinate projector. The live
escape is therefore nonspanning pointwise behavior without global equivariance, or leakage
varying with the word/source, not another fixed-rank case.

[`G3-O18`](SALVAGE.md#g3-o18-transverse-minimum-body-countermodel) proves that transverse
geometry itself is no obstruction. A variable-radix code with four distinct residues is carried
by fixed integral rank-two data controls with kernels `ℚe₁` and `ℚe₂`. Lean checks the exact
state recurrence on every raw control word and an exact paired recognizer for every minimum body.
Its terminal row selects one computable history code, so it does not handle arbitrary bodies with
several or infinitely many terminal histories.

[`G3-O26`](SALVAGE.md#g3-o26-transverse-terminal-row-obstruction) closes the proposed row
extension of that orbit. The two `bcbc` terminal histories require zeros at both phases of two
distinct codes, forcing every exact row to vanish; the checked near-fork is then a false zero.
This holds even for an arbitrary source-dependent row family. The live transverse problem is
therefore a different orbit, not more parameters in the terminal row.

[`G3-O27`](SALVAGE.md#g3-o27-projective-toggle-line-atlas) sharply restricts that escape. For
arbitrary source-dependent controls and column, singular data maps together with
`T²=sI`, `s≠0`, confine the complete raw orbit to two boundary subspaces of vector dimension at
most one and four data-image subspaces of vector dimension at most two. Every terminal row cuts
each carrier in the whole carrier or a subspace of vector dimension at most one. Hence this
branch has only a finite projective-line atlas, not genuinely two-dimensional projective
dynamics. `G3-O04` decides it only when those charts share its finite-mode expanding affine
normalization. The exact internal survivor is point reachability in a finite rational `P¹` atlas,
potentially the joint `M₂(3)` core. A nonprojectively-involutive toggle and a full-rank data map
remain separate structural escapes.

[`G3-O29`](SALVAGE.md#g3-o29-one-chart-projective-hard-core) proves that “potentially” is already
an exact hardness statement. Every two-generator rational projective-incidence instance embeds
in one common invariant plane by `A↦diag(A,0)`, with identity toggle and row/column extended by
zero. Deleting raw toggles preserves the coefficient word-for-word, and the toggle-free embedding
is a section. Thus the one-chart atlas subfamily is instancewise equivalent to the `D2-S01` core;
a general atlas decision algorithm would decide `M₂(3)`. This is not an undecidability result,
and arbitrary multi-chart instances are not reduced back to one `M₂(3)` instance.

[`G3-O30`](SALVAGE.md#g3-o30-nonprojective-infinite-carrier-orbit) proves that the other
structural escape is real. The diagonal toggle `diag(1,2,3)` and an exact rank-two data map with
source-parameter image normal `(1,1,s)` produce the literal raw-prefix carriers
`im(TⁿD_s)`. Their normals are `(6ⁿ,3ⁿ,s·2ⁿ)`, and `(1,−2ⁿ,0)` separates the `n`th plane from
every later plane. Thus the carrier orbit is injectively infinite for every `s∈ℚ`. Singularity
and rational diagonalizability do not recover a finite atlas once the toggle ceases to be
projectively involutive. No terminal row or paired recognizer follows from the counterexample.

[`G3-O31`](SALVAGE.md#g3-o31-whole-carrier-terminal-row-obstruction) removes the simplest use of
that infinity. If one row annihilates the whole carrier planes at two depths `n<m`, the first
spanning columns force `a=b2ⁿ=b2ᵐ`, hence `a=b=0`; the second forces `c=0`. Thus a nonzero row
contains at most one whole plane in the `G3-O30` orbit. Every remaining depth contributes only a
proper moving line section. The live problem is now the arithmetic of those lines and the
complete malformed-word converse, not selecting an unbounded set of depths wholesale.

[`G3-O32`](SALVAGE.md#g3-o32-terminal-point-incidence-dichotomy) computes that arithmetic for
every fixed point. For arbitrary `λ=(a,b,c)`, `γ=(x,y,z)`, and `s∈ℚ`, the terminal scalar is
`A−B2ⁿ−C3ⁿ`, with `A=a(x+sy)`, `B=bx`, and `C=cy`. A positive generalized-Vandermonde
minor shows that three distinct zero depths force `A=B=C=0`. Thus a fixed point test accepts all
depths or at most two. The bound is sharp, but there is no row-independent horizon:
`(2ᴺ,1,0)` on `γ=e₁` accepts exactly depth `N`. The exact survivor is therefore source-computed
delayed singleton or two-depth targeting, not richer zero arithmetic in one fixed point.

[`G3-O33`](SALVAGE.md#g3-o33-uniform-terminal-coefficient-section) closes the tempting algebraic
attack on that survivor. The pole-free column `(s²+1,1,0)` and row
`(A/(s²+s+1),B/(s²+1),C)` realize every coefficient triple `(A,B,C)` at every rational source.
Thus any source-indexed target `N` can select exactly depth `N` through `(A,B,C)=(2ᴺ,1,0)`.
Source-to-row fitting is universal; the live obstruction is now history-to-depth word dynamics
and the arbitrary-word converse.

[`G3-O34`](SALVAGE.md#g3-o34-letter-blind-infinite-carrier-collision) then kills the literal
generator. It sends both data labels to `D_s`. The certified `bcbc` terminal prefix and
nonterminal near-fork have identical toggle positions, hence identical matrix products under this
letter-blind map. No row or column can separate them. A surviving infinite-carrier constructor
must use distinct data maps and re-establish the orbit, terminal section, and all-word converse.

[`G3-C06`](SALVAGE.md#g3-c06-distinct-data-infinite-carrier-candidate) supplies that first repair.
Keep `D_b=D_s` and set `D_c=P D_s` for one fixed matrix `P` of determinant `−4`. Both maps are
distinct and rank two; every `tⁿb` product, infinite carrier, and delayed-depth section remains
unchanged. The `bcbc` terminal/near-fork product difference has entry
`6(2s²−5s+4)>0` for every source, so the exact collision is gone without exceptional fibres.
That local repair does not survive the complete terminal fork.

[`G3-O35`](SALVAGE.md#g3-o35-distinct-data-terminal-fork-obstruction) closes the `G3-C06` monoid.
For `s≠0`, the flat and nested null blocks induce two quotient matrices with nonsingular
commutator; three certified terminal forks force the boundary row, then the fixed prefix row, to
vanish. The prefix without its final toggle is a false zero. Mod-`7` and mod-`13` rational-root
certificates remove every nonzero exceptional parameter. At `s=0`, the terminal word
`ctbcbtcbt` and nonterminal `ctbcbcbbb` have the same target product. No row or column repairs
the candidate at any rational source.

[`G3-S03`](SALVAGE.md#g3-s03-terminal-fork-invariant-core) extracts the general cut. For arbitrary
rational three-state controls, all flat/nested terminal-fork states span a common invariant
subspace annihilated by the transported prefix row. Same-zero correctness makes both boundary
vectors nonzero, so this fork carrier has dimension one or two. Thus an irreducible three-state
fork is impossible independently of rank, kernel, or quotient coordinates. If the fork blocks
are invertible, their terminal action is a `GL₁` or `GL₂` restriction; the two-dimensional
branch is the joint positive `M₂(3)` projective-incidence seam.

[`G3-C07`](SALVAGE.md#g3-c07-persistent-guard-rank-escape) shows that reducibility does not force
two singular data maps. The exact `bcbcbb` recognizer remains exact after changing its data-`b`
guard update to `g↦mg+2k+1` for any even integer `m`. For `m≠0`, data `b` has determinant
`5m` and rational rank three, while singular data `c` retains the original accepting-carry reset.
Lean proves the complete arbitrary-word zero equivalence. The live architecture is therefore one
singular syntax gate feeding a persistent full-rank action, not a common-kernel pair. This remains
fixed-body and does not evade the uniform finite-target cut `G3-O04`.

[`G3-C08`](SALVAGE.md#g3-c08-guarded-two-state-lift) extracts the complete compiler interface.
For arbitrary integral two-state core matrices, a core column `q`, and gate row `g`, one guard
coordinate makes every `b`-headed word nonzero under an odd-coordinate invariant and makes every
`c`-headed zero exactly an incidence `gA_wq=0`. The persistent `b` control has determinant twice
the core determinant; `c` is the sole singular gate. Lean proves that a source-indexed family of
these lifts is same-zero exact if and only if `gA_wq=0` agrees with the paired coefficient on the
single family of `c`-headed words. Width positivity discharges the empty, toggle, and `b`-headed
cases from the native terminal converse. The third state, rank escape, and malformed-word guard
are therefore finished; the exact remaining equation is the non-elementary two-state
scalar-orbit problem shared with `D2-S01`. The `G3-S03` terminal core does not supply this equation:
its boundary vanishes on the whole fork orbit, so rejection must occur through ambient leakage.

[`G3-S06`](SALVAGE.md#g3-s06-guarded-mixed-prime-endpoint-bridge) crosses this interface with the
mixed-prime benchmark. Any block code from paired controls to words in `D(z)=2z/3` and
`T(z)=3z/5+1` gives an integral parity-preserving core automatically, but its scalar gate is
exactly fixed rational endpoint reachability for the concatenated code word. `D2-S08` does not
automatically descend from unrestricted guarded shell schedules to this regular raw-word image;
guard semantics and shift closure are additional obligations. It also retains the exact
normalized mantissa, so its twelve labels do not close the gate. The `bcbc` fork forces the three
induced core matrices and endpoint affine actions to be pairwise distinct, killing every
letterwise three-control-to-two-letter relabeling. The remaining mixed-prime branch needs genuine
macros and remains the joint `M₂(3)` mantissa problem.

[`G3-S08`](SALVAGE.md#g3-s08-mixed-prime-macro-fork-rigidity) forces the first global relation on
those macros. Cancelling the fixed terminal prefix on three accepted forks makes both encoded
flat/nested blocks fix the toggled source. Their control Parikh vectors coincide, so their affine
slopes coincide; the two blocks therefore induce the same affine action and commute globally.
Every exact code must realize either a literal substituted word equation or a distinct equal-map
pair in the mixed-prime kernel. The three control macros cannot share an affine fixed point, since
that would force source and target to it and accept a certified rejected suffix. The live macro
branch is now a non-common-fixed solution of one exact fork relation, not an unconstrained search.

[`G3-S10`](SALVAGE.md#g3-s10-mixed-prime-literal-fork-extinction) kills the literal alternative.
Literal flat/nested equality cancels to `yzxyx=xzyxy`, whose equal-length split gives
`yzx=xzy` and `yx=xy`. A fixed-point and two-point affine-rigidity argument then forces all three
macros to share one rational fixed point, contradicting `G3-S08`. Every exact code must therefore
produce distinct flat/nested raw words inducing one affine map. Their common length is
`4(2|κ(b)|+|κ(c)|+|κ(toggle)|)`. The sole surviving specialization is a non-common-fixed genuine
mixed-prime kernel decomposition satisfying the full endpoint converse.

[`G3-S11`](SALVAGE.md#g3-s11-reduced-fork-kernel-gauntlet) removes the common bijective macro
context and forces the shorter collision `yzxyx=xzyxy` at the action level, of reduced length
`N=2|x|+2|y|+|z|`. All three macros are nonempty; the data actions have unequal slopes and fixed
points. An exact positive balance makes the toggle fixed point lie beyond the more contracting
data fixed point, away from the other. Exhaustive rational search finds no required pairwise-
distinct, non-common-fixed triple for `N≤36`. Thus every live code has `N≥37`; this bound is
computational, while the reduction and fixed-point geometry are Lean-checked.

[`G3-S12`](SALVAGE.md#g3-s12-fork-crossing-transport-and-address-ambiguity) factors the reduced
collision through two canonical crossings: the toggle must carry the crossing of `XYX,YXY` to
the crossing of `X,Y`. Lean classifies the resulting five-point order for all physical
contractions. This does not yield a raw leading-run descent: prefixing Cassaigne's relation by
`Tⁿ` gives two distinct equal-action words with leading runs `n` and `n+2` for every `n`, even
inside the exact slope-conditioned fixed-point cylinders. The live obstruction must therefore
classify the fork in an oriented quotient of the mixed-prime word monoid.

[`G3-S13`](SALVAGE.md#g3-s13-contextual-kernel-fork-classification) finds and kills the first
quotient survivor. The first Cassaigne critical pair embeds into a distinct equal-action fork of
reduced length `312`, but its macro actions are exactly `F,F²,F⁴` and share one rational fixed
point, so the endpoint converse rejects it. Lean proves the generic reason: every full-triple
conjugacy lift leaves a commuting core `RˢK=KRˢ` and collapses onto the common-fixed diagonal.
Audited bounds plus exact assignment search eliminate every other placement of one base or first
critical relation. Only multi-step quotient derivations or new kernel relations remain.

[`G3-S14`](SALVAGE.md#g3-s14-finite-convergent-mixed-prime-presentation) closes the completion
question for that quotient. The five rules plus their `45` first critical branch pairs form a
finite convergent `50`-rule presentation: there are no inclusion ambiguities and all `450` proper
overlaps join. Unique normal forms decide every fixed congruence query, replay the length-`312`
fork in four versus five reductions, and prove that every positive-depth odd-family relation lies
outside the quotient. Confluence does not decide the remaining existential word equation: the
live quotient branch is to find or exclude a non-common-fixed solution of `YZXYX≡XZYXY`; the
orthogonal branch is a new affine-kernel relation outside the presentation.

[`G3-S15`](SALVAGE.md#g3-s15-uniform-mixed-prime-contextual-cut-collapse) closes the first two
one-context continuations. Lean kills every off-centralizer placement of the infinite odd family
at every depth by its unique balanced prefix and suffix cuts. Exact cut census and
`799,088,198` assignment-complete geometries then eliminate all `405` new second-critical pairs,
after contracting them to the internal bound `N≤171`. Thus the quotient branch now requires a
genuinely multi-window solution of `YZXYX≡XZYXY`; the external-kernel branch requires a new
family rather than the odd relation.

[`G3-S16`](SALVAGE.md#g3-s16-cayley-hamilton-pump-census-and-free-macro-address) finds that new
kernel structure. Exhaustive length-`32` census yields `23` boundary-reduced cores, each extending
to an infinite `DT`- or `TD`-pump schema by a formal two-seed Cayley-Hamilton theorem. All remain
outside the finite quotient. More importantly, the derived macros `{DT,TD}` generate a free
binary affine submonoid with exact left-mod-`2` and right-mod-`5` decoding. The `23` contexts are
only unary readers: every alternate-pump test is nonzero. The positive external-kernel node is now
to make the `bcbc` fork compare general stack addresses; the matching no-go is to prove its forced
two-state core cannot upgrade unary reading.

[`G3-M02`](SALVAGE.md#g3-m02-square-root-punctuation-fracture) supplied a complete direct-mortality
grammar. The source-uniform rational rank-two matrix `S` satisfies

```text
S²=(γ/(λγ))λ.
```

Lean proves a stronger source-independent fracture: whenever `S²=uvᵀ`, the family
`{X₁,X₂,X₃,S}` is mortal exactly when `vᵀH_zu=0` for some word `z` avoiding `SS`. This is a
complete free-monoid theorem; every malformed isolated `S` remains in the residual language.
The remaining zero-set-only completion is now closed by
[`G3-O10`](SALVAGE.md#g3-o10-square-root-boundary-saturation). Every nondegenerate root of a
rank-one separator scales both boundary vectors by the same nonzero scalar, so prefixing or
suffixing one isolated `S` preserves scalar vanishing. The arbitrary-word Neary converse instead
forces every terminal match to begin with `R_c`; an `R_b` prefix is never a native zero. A legal
terminal history and its `S`-prefix are both `SS`-free. Hence direct identification `S↦R_b`
contradicts same-zero reflection on the very fracture domain required by the mortality theorem.
Changing the square root, similarity, letter weights, or nonzero values cannot evade this
dimension-free boundary invariant.

[`G3-M01`](SALVAGE.md#g3-m01-free-group-discrepancy-engine) remains a genuinely different
deletion mechanism, but its rank interpretation is now settled. For an `m`-appendant cyclic tag
system, Carvalho's complete closed-path subgroup is free of rank `3m+1`; its accepting fixed
subgroup is nevertheless trivial in a no-instance and cyclic in a yes-instance. The induced
free-group PCP equalizer is promised rank zero or one. Thus the full Stallings basis stores
synchronization, while the accepting generator is halting-dependent and cannot be chosen from a
computable finite menu.

Three positive letters already surject onto `F₂`: with `z=y⁻¹x⁻¹`, all three inverses have
positive length-two spellings. [`G3-O09`](SALVAGE.md#g3-o09-quotient-blind-positive-boundary-collapse)
formalizes the resulting trap. Fixed group boundaries which accept an element and its square also
accept the identity; a surjective positive spelling then supplies a nonempty false witness. This
kills all-loop-complete Nielsen or Schreier compression followed by quotient-blind boundaries.

[`G3-O14`](SALVAGE.md#g3-o14-positive-cancellation-spelling-dichotomy) closes both finite-state
repairs proposed after that result. An injective lift over a finite semantic fibre pumps every
positive identity loop. A singular one-coordinate lift of a two-dimensional invertible quotient
instead absorbs every later quotient-identity factor as an equality of complete products.
[`G3-O15`](SALVAGE.md#g3-o15-triangle-normal-form-rank-six) independently proves that a standalone
same-zero detector for the triangle-irreducible language needs six states. Finite spelling,
transient singular spelling, and a separate three-state syntax guard are all dead.

The surviving target no longer selects a spelling. Carvalho's `p`-exponent homomorphism and the
equalizer identification give the audited equivalence

```text
C halts  ↔  ∃u, g(u)=h(u) and κ(u)=1.
```

Exponent one excludes the identity and the square while allowing arbitrary positive identity
padding of a genuine witness. The remaining compiler must carry this affine equalizer slice through
three positive controls using an everywhere-invertible infinite fibre or semantics which do not
retain the two-dimensional invertible cancellation quotient.

[`G3-M03`](SALVAGE.md#g3-m03-three-positive-affine-exponent-cover) removes positive spelling,
domain recognition, and identity padding from that obligation. The three positive letters

```text
x↦a,       y↦b,       z↦b⁻¹a⁻¹,       ω(x,y,z)=(1,0,−1)
```

surject onto every prescribed `a`-exponent slice of `F₂`, with `ω` equal to that exponent on
every arbitrary positive word. A Nielsen-Schreier embedding transports Carvalho's primitive
exponent to one slice, so halting is exactly a graph-correlated equalizer together with one
affine weight equation over three positive controls. Positive identity padding preserves both
conditions. The remaining problem is joint detection and extension from the correlated subgroup,
not a normal-form parser.

[`G3-O16`](SALVAGE.md#g3-o16-full-augmented-pair-dimension-tax) excludes the brutish completion:
a homomorphic detector for all independent triples in `F×F×ℤ` would contain two commuting
faithful free groups and needs at least four dimensions. This does not exclude the program-
correlated graph. The live compiler must preserve that correlation throughout a graph-specific
cocycle; first representing two arbitrary group values and an independent counter is dead.

[`G3-O19`](SALVAGE.md#g3-o19-correlated-affine-slice-density) blocks a subtler overreach. The
actual Carvalho maps do share the `p`-character globally, but injective `h`, a shared primitive
character, cyclic equalizer, and even a singleton exponent-one slice do not force an algebraic
dimension drop. A synthetic graph with all these promises has every fixed-character slice dense
in `PSL₂×PSL₂`, so every algebraically extendable carrier using both coordinates needs four
dimensions. Its language nevertheless has a two-state same-zero detector. Thus neither the
promise-level carrier obstruction nor its rank-four Hankel minor is a language lower bound, and
neither may be attributed to the actual program graph.

[`G3-O21`](SALVAGE.md#g3-o21-actual-carvalho-slice-density) now computes the missing actual
geometry. On the kernel of Carvalho's `p`-character, the two coordinate projections contain
explicit noncommuting marker subgroups. Algebraic Goursat leaves the full product or an
automorphism graph. The transducer fixes `H` and `pHp⁻¹`, forcing any such automorphism to be
conjugation by the initial discrepancy; the loop `0ᵐ`, whose output is `Hᵐ`, contradicts that
graph. Hence every fixed-character slice of the actual program graph is Zariski dense in
`PSL₂×PSL₂` under a faithful Schottky embedding. This closes algebraically extendable
dimension-three compression for the actual source, but remains neither a language-rank lower
bound nor an obstruction to spelling-sensitive or nonalgebraic dynamics.

[`G3-O22`](SALVAGE.md#g3-o22-invertible-fibre-span-rigidity) now resolves the internal geometry
of every everywhere-invertible scalar carrier on the positive cover. For each group element
`q`, the span `C_q` of states reached by all positive spellings has one common positive dimension,
and every transition maps it exactly onto the group-translated fibre. A nonzero scalar boundary
vanishing on one fibre in dimension three forces `dim C_q∈{1,2}`. The identity fibre is the seed
orbit of a computable finite operator algebra. Thus the invertible branch is a line or plane
group-orbit incidence problem, rather than an arbitrary infinite spelling memory. This does not
yield positive `M₃(2)`: the reverse orbit edges use inverse linear maps which need not be positive
controls.

[`G3-O23`](SALVAGE.md#g3-o23-singular-triangle-carrier-collapse) removes the formerly separate
singular branch. A rank-at-most-one semantic identity loop makes every saturated scalar zero
language rectangular and therefore trivial. Hence a singular triangle identity in a nontrivial
three-state recognizer has rank two, and sandwiching every letter through its image gives three
invertible two-state transitions recognizing exactly the same language. The rational image basis
and every empty-word boundary case are effective. Thus every saturated three-state triangle
carrier is either everywhere invertible in dimension three or equivalent to an everywhere-
invertible dimension-two carrier. For Carvalho's singleton yes-language, the latter is a faithful
`PGL₂(ℚ)` group orbit with `[T_z]=[T_y]⁻¹[T_x]⁻¹`. It is not positive `M₂(3)`: the inverse
edges remain group operations rather than positive controls. Exact rational rank tests decide
every preliminary obstruction; the sole survivor is intersection of the two-generated
projective group `Γ` with one rational Borel coset `g₀B`, promised to contain at most one
element. Conditional on a hit, the singleton semantics force `Γ∩B={1}` and faithfulness.

[`D2-D08`](SALVAGE.md#d2-d08-rational-affine-group-orbits), together with the audited
invariant-pair algorithm `D2-D02`, decides every elementary branch of this group orbit. A common
rational fixed point reduces to an affine translation-kernel quotient; an invariant pair reduces
to multiplicative-subgroup membership in `ℚ` or a quadratic field. The exact survivor is

```text
UCB₂(S):  ⟨A,B⟩ ∩ g₀B_S ≠ ∅,     promised cardinality at most one,
B_S=Stab(∞)∩PGL₂(ℤ[S⁻¹]).
```

[`R32-O22`](SALVAGE.md#r32-o22-congruence-blind-free-orbit) closes the finite-congruence escape
from this residual shell. The free subgroup generated by the step-three upper and lower shears
has trivial stabilizer at `[1:1]` and misses `[10:13]` over `ℚ`, yet an explicit five-factor
word reaches that target modulo every positive integer, up to unit scaling over the composite
residue ring. Lean now replaces every signed shear syllable by a positive residue-length power,
so the modular hit uses an actual positive `{A,B}` word. Hence neither one modulus nor any finite family supplies a residue-orbit
nonmembership certificate, and the all-congruence membership criterion is false. This does not
exclude a global algorithm, prove local density, or settle the Borel-coset intersection.

[`G3-O28`](SALVAGE.md#g3-o28-ambient-profinite-blindness-of-the-unique-coset) strengthens this at
the exact group-cover boundary. For a second rational gap target, the complete target matrix lies
in the shear group's congruence closure modulo every integer prime to nineteen. After conjugating
the source to infinity, the instance lies in `Γ₀(3;ℤ[1/19])`. Serre's exact congruence-subgroup
theorem upgrades the modular identities to closure in every finite quotient of that ambient
group. The actual Borel coset remains empty and the source stabilizer remains trivial. Thus even
noncongruence finite ambient quotients cannot certify every promised no-instance. Syntax, height,
Archimedean geometry, and infinite normal forms remain available.

[`D2-D09`](SALVAGE.md#d2-d09-step-three-shear-height-decision) now supplies the missing infinite
invariant for this entire fixed-source shear family. A reduced `k`-syllable witness to a primitive
target of height `H` satisfies `2^k≤H`, and every signed exponent has absolute value at most `H`.
Finite enumeration therefore decides the orbit, including the profinite-blind target. `G3-O28`
survives as a sharp obstruction to finite certificates, but its displayed family is not a hard
`UCB₂(S)` instance.

[`D2-O05`](SALVAGE.md#d2-o05-promised-empty-free-orbit-inverse-cycle) blocks the direct extension
of that primitive-height proof. For `D(z)=5z` and one transverse parabolic, strict ping-pong makes
the source orbit free, while the nonidentity positive word `UD` fixes a primitive target outside
that orbit. Chamber-directed inverse stripping then repeats the exact height cycle `5→3→5`.
The instance is itself easy to reject from the target stabilizer; the obstruction is to greedy
well-founded descent. Any general normal form must quotient recurrent target stabilizers, retain
richer cycle state, or replace primitive Archimedean height.

[`D2-O06`](SALVAGE.md#d2-o06-bounded-inverse-recurrence-forces-a-stabilizer) closes the proposed
harder bounded-cycle variant. Along any injective sequence of group prefixes, bounded primitive
height forces two orbit representatives to coincide; the quotient of those distinct prefixes is a
nonidentity element of the target stabilizer. Thus every free normal-form inverse path at a
trivial-stabilizer target has unbounded height. The frontier splits into effective target-stabilizer
recognition and control of the unbounded-height paths left after that component is removed.

[`D2-O10`](SALVAGE.md#d2-o10-finite-bounded-prefix-horizon) makes that split effective on the
bounded side. The explicit integer square contains `(2H+1)²` possible representatives, so
`(2H+1)²+1` distinct prefixes bounded by height `H` already produce a stabilizer witness. At a
trivial-stabilizer target, every such finite window escapes above `H`; no separate bounded
aperiodic branch remains.

[`D2-O11`](SALVAGE.md#d2-o11-bounded-branch-nonreachability-certificate) converts the finite
collision into the certificate needed by the unique-coset problem. Under trivial source
stabilizer, any nonidentity target stabilizer forbids a source-to-target transporter by
conjugation. Thus every explicit prefix window either escapes above `H` or certifies that the
target is unreachable; target-stabilizer recognition is unnecessary on the bounded branch.

[`D2-O12`](SALVAGE.md#d2-o12-exact-prefix-height-rate) quantifies the survivor. At a
trivial-stabilizer target, `N` distinct prefixes whose primitive states have height at most `H`
satisfy `N≤(2H+1)²`; equivalently, `(2H+1)²<N` forces a state above `H`. Reachability from the
promised trivial-stabilizer source transfers triviality to the target. This constrains the maximum
height in every finite prefix family but does not make the height sequence monotone or prevent
later returns.

[`D2-O13`](SALVAGE.md#d2-o13-proper-height-escape) closes infinite low-height return behavior.
At a trivial-stabilizer target, the primitive-state map along injective prefixes is injective, so
the indices below any fixed height ceiling form a finite set. Primitive height therefore tends to
infinity: every fixed cube has a last visit. What remains is an effective last-return bound or a
place-sensitive escape direction, not another recurrent bounded-height mechanism.

[`D2-O14`](SALVAGE.md#d2-o14-proper-false-inverse-ray) shows that properness is not yet a pruning
law. The same free dilation--parabolic group has a promised-empty target with both endpoint
stabilizers trivial, while unguided inverse search follows the irrelevant ray `D⁻ⁿq` through
primitive pairs `(11,5^(n+2))`. Its height tends to infinity exactly as `D2-O13` requires. The
remaining invariant must therefore orient escape by chamber, place, or another lawful normal-form
direction; raw divergence cannot certify rejection.

The ordinary mortality lift is likewise no longer part of the paired obstruction. For arbitrary
controls `H_a`, column `γ`, and row `λ` over a field, adjoining `γλ` gives mortality exactly when some
`λH_yγ` vanishes. A zero product without the separator is already a scalar-zero witness; after
fracturing a product with separators, every internal scalar or zero exterior factor supplies one.
Thus a rational three-state same-zero recognizer immediately yields four rational mortality
generators, and generator-wise denominator clearing yields integral generators. The surviving
direct route is the uniform paired recognizer; the `SS`-free square-root variant is closed.

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

[`G3-C03`](SALVAGE.md#g3-c03-endpoint-prefix-compiler) gives the exact tighter interface. A
three-production prefix normal system compiles directly to `GPCP(3)` when its terminal equation
forces every intermediate rule prefix. Lean proves both directions and checks that the
unrestricted telescope admits a false underflow witness. The known three-rule semi-Thue source
rewrites arbitrary substrings, so its rule-name trace omits redex contexts and does not satisfy
this interface without a new context transporter.

[`G3-C04`](SALVAGE.md#g3-c04-head-separated-endpoint-debt) makes arbitrary-trace soundness local
for a broad subclass. If every produced word is nonempty and its head symbol occurs nowhere in
the corresponding consumed word, the first illegal prefix creates an unrepairable debt; Lean
proves every aggregate endpoint equality is then a lawful derivation and discharges the complete
`G3-C03` forcing hypothesis. The live source problem is therefore to obtain undecidability with
three head-separated productions while retaining an open unbounded word residue. It is no longer
a simultaneous source-and-compiler correctness problem.

[`G3-O24`](SALVAGE.md#g3-o24-directed-dyck-absorption-collapse) closes the apparent shortcut
through the published three-rule Matiyasevich–Sénizergues system. Those rules rewrite arbitrary
substrings, and the final deletion `xx̄→ε` performs directed decoder work: one deletion can move
the greatest-lower-bound source state down a nontrivial path. Every faithful finite-dimensional
absorption `XX̄=I` forces the reverse identity, as do complete scalar-value saturation and
projectively faithful zero saturation. The surviving possibility is narrower but real: a
singular, order-sensitive action confined to the directed stable cone may use nonprojective zero
contexts to distinguish cancellation positions. No source theorem currently realizes that
action with three states.

[`G3-O25`](SALVAGE.md#g3-o25-stable-cone-rank-fork) splits that survivor by the `y`-separator.
Because the stable cone is `B*y`, every stable matrix word factors through `im M_y`. Rank one
loses block order; rank two is exactly a two-state block carrier; only invertible `M_y` retains
genuine three-state block memory. Conversely, explicit positive rank-two `X,X̄` matrices realize
strict cancellation monotonicity, noncommuting `u₁,u₂`, and every A4 cover in three states. Their
zero language is trivial. Thus a fourth-state obstruction must use zero-sensitive GLB fibres,
not directed order or positional noncommutation alone.

[`G3-D03`](SALVAGE.md#g3-d03-one-sided-corrected-drift) closes a broad source class before
compilation. If some positive target-symbol weighting and finite-state potential make every trim
transition drift in one direction, terminal equality bounds every accepting residual and exact
finite reachability decides solvability. A surviving source must keep an unbounded word residual
and recurrently expand and contract under every positive weighting. A finite parser, bounded
delay, equal-height tableau, or acyclic verification tail cannot be its computational store.

[`G3-D06`](SALVAGE.md#g3-d06-functional-phase-transfer-guillotine) now removes the natural
three-chamber repair. If rule `i` consumes positive projected charge from phase `i` and sends all
net charge to one different phase `τ(i)`, the loopless functional graph has one cycle. Lean
constructs positive phase weights with a common drift sign in every labeled topology and lifts
them through any positive quotient to symbol weights; fixed-endpoint reachability is then finite.
Arbitrary balanced payload and an open word residue do not help. The sharp surviving topology is
two competing forward schemas `P→Q` and one return `Q→P`, with the two cycle products straddling
one. Empty-consume pumping and genuinely phase-splitting transport are separate boundaries.

[`G3-D07`](SALVAGE.md#g3-d07-pure-phase-fork-closure) closes that fork whenever every completed
return erases the boundary to one fixed-word power. Complete cycles form an effective semilinear
additive relation `R⊆ℕ²`. One-sided drift gives finite search; mixed drift gives a positive
diagonal, a finite residue quotient, and an exact one-dimensional GVAS grammar. Published
one-dimensional GVAS reachability decides `R*`. This kills the canonical `pp/p/q` fork and every
finite pure two-chamber refinement on pure endpoints. A live fork must retain an unbounded mixed
or neutral word across the return, use an empty consume, or split recurrent output.

#### Research lanes

| Lane | Available leverage | Decisive obstruction or obligation |
| --- | --- | --- |
| Common-kernel shuttle | The exact `bcbb` compiler moves its common data kernel out through the toggle and recovers it at the next data action | Uniformize this non-invariant shuttle in `(β,body)`; every toggle-invariant guard factors through the two-dimensional quotient |
| Transverse-kernel terminal dynamics | `G3-O27/O29` reduce the involutive branch to the `M₂(3)` core; `G3-O30`–`O35` close the first infinite-carrier repair; `G3-S03/C07/C08` force and compile the sole two-state gate; `G3-S06/S08/S10/S11` force a positive non-common-fixed fork-kernel triple; `G3-S07/S09` close every fixed spanning Sym² leakage rank; `G3-S13`–`S15` close the first finite-quotient layers; `G3-S16` gives 23 external pump schemas and a free binary affine address stack with unary readers | Find or exclude a genuinely multi-window quotient fork, or make the `bcbc` fork compare general `{DT,TD}` stack addresses, then retain exact normalized mantissa. Alternatively prove every lawful core lies in an audited `D2` decision stratum. Generic irreducible `GL₃` forks, fixed spanning leakage, letterwise, literal, empty-macro, common-fixed, short reduced codes, the odd family, first/second-critical one-window repairs, fixed unary readers, depth-class-only gates, and further third-state guard tuning are dead |
| Positive projective transition lower bound | Same-zero dimension three is point-line incidence in `P²`, and actual one-sided shifts retain finite rank/kernel/image data | Derive a uniform nonstationary or noncommuting shift incompatibility from an unbounded terminal section; direct non-elementary Sym² forks, full-rank fixed leakage, fixed equivariant rank-two leakage on three rays, static support rank, formal inverse completion, fixed equal-length return flowers, and unary consecutive-repeat escape are forbidden |
| Global word-residual recoding | Longer noncommutative atoms can retain order while discarding the four additive role channels | Escape `G3-D05`: fixed-priority affine counters and all one-way reset/transfer/fanout cascades are decidable |
| Head-separated three-schema source | `G3-C04` discharges every arbitrary-trace forcing obligation locally; `G3-O24` isolates the directed stable-cone alternative | Preserve an undecidable mixed or neutral word across returns, or realize zero-sensitive S5 GLB decoding after the `G3-O25` separator-rank fork; complete pure forks are decidable by `G3-D07` |
| Carvalho projective group-orbit separator | `G3-M03` gives the exact saturated three-positive cover; `G3-O23` collapses every singular carrier to invertible dimension two; `D2-D02/D08` decide all elementary group actions; `D2-D09` decides the profinite-blind step-three shear family by height | Add chamber/place direction to the proper height escape forced by `D2-O13`, since `D2-O14` realizes an irrelevant proper ray under unguided search, or construct the invertible three-state line/plane orbit left by `G3-O22`; finite ambient quotients are forbidden by `G3-O28`, primitive-height-only descent by `D2-O05`, and bounded trivial-stabilizer recurrence by `D2-O06/O11` |

These six lanes form three trunks. The first three race a direct paired construction against its
one-sided projective lower bound. The next two seek genuine `GPCP(3)` through either global
recoding or a native source. The last is now a projective group-orbit attack shared with the
dimension-two campaign: `G3-O21` closes its algebraic semantic carrier, `G3-O23` removes
singular spelling memory, `D2-D02/D08` remove the elementary group branch, and `G3-O28`
removes all finite ambient-quotient separation on one promised no-instance. `D2-D09` then decides
that no-instance's complete fixed-source family by Archimedean height. `D2-O05` shows why the
same height cannot simply be carried to a dilation--parabolic free product: a positive target
stabilizer creates an exact inverse cycle even in a promised-empty coset. `D2-O06` proves that
every bounded cycle of distinct normal-form prefixes has exactly this algebraic source; a
trivial-stabilizer successor must escape to unbounded height. `D2-O10` gives the explicit escape
horizon `(2H+1)²+1` for each proposed height ceiling `H`; `D2-O11` turns a collision inside that
window directly into a nonreachability certificate under the promised trivial source stabilizer.

#### Raceable leaves

After `G3-O21`–`G3-O27`, `R32-O22`, and `G3-D07` close their respective carrier, absorption,
pure-source, fixed-transverse-orbit, and finite-line-atlas lanes, the net tree has six independent
raceable leaves:

1. **Common-kernel shuttle constructor.** Give one computable three-state paired recognizer in
   which the toggle moves a freshly minted common-kernel guard back into visible quotient data.
   Prove its state formula and scalar-zero equivalence uniformly in `(β,body)` on the complete
   free control monoid. Toggle-invariant refresh is closed.
2. **Transverse line-atlas escape.** Build a source-computable arbitrary-body recognizer using
   the `M₂(3)` projective-incidence core, the explicit `G3-O30` infinite non-scalar toggle orbit,
   or a full-rank data map.
   Pure kernel geometry, exceptional fibres, minimum-body examples, terminal-row retuning, and
   genuinely two-dimensional dynamics under singular data plus projective involution are closed;
   general one-chart incidence cannot be declared decidable without resolving `M₂(3)`, and
   `G3-O31` forces the nonprojective branch to use proper moving line sections at all but one
   depth, while `G3-O32` proves that every fixed point on those lines accepts all depths or at
   most two. The live nonprojective leaf is source-computed delayed singleton or two-depth
   targeting, broader terminal geometry, or a different orbit. `G3-O33` proves coefficient fitting
   universal, so the isolated-depth branch must now construct or exclude the required
   history-to-depth word map. `G3-O34` kills the letter-blind generator outright. `G3-C06`
   supplies distinct data maps that retain the orbit and separate the first near-fork, but
   `G3-O35` proves that three complete terminal forks force a false zero for every nonzero source
   and gives an opposite-semantics collision at source zero. The live nonprojective escape must
   change the controls or terminal geometry, not retune the `G3-C06` row or column. `G3-S03`
   forces its complete fork orbit into a one- or two-dimensional invariant core for every exact
   three-state recognizer. `G3-C07` supplies the nearest lawful positive model: one singular reset
   can guard a full-rank persistent data action without changing a complete all-word zero
   language. `G3-C08` now compiles that architecture uniformly: all third-state obligations reduce
   exactly to an odd-coordinate invariant and the scalar equation `gA_wq=0` on `c`-headed words
   in a source-indexed two-state core. `G3-S06` shows that the direct mixed-prime specialization
   is exact fixed-endpoint reachability. The twelve-class comparison first requires guarded-shell
   semantics and shift closure for the macro image, then still leaves its rational mantissa; the
   `bcbc` fork forbids every letterwise relabeling and requires three distinct macro maps.
   `G3-S08` further identifies the flat and nested fork actions and excludes every common-fixed
   macro triple. `G3-S10` proves that literal equality itself forces such a forbidden common fixed
   point. `G3-S11` then cancels the inert action context, proves every macro nonempty, forces the
   toggle fixed point beyond the more contracting data fixed point, and exhaustively excludes
   reduced relation length at most `36`. `G3-S12` factors the equation through two ordered
   crossings and proves that equal-action Cassaigne rewrites shift the leading-run address by two
   at every depth. `G3-S13` then classifies every one-context use of the five audited relations
   and their first critical pairs: the first actual fork appears at length `312`, but is the
   forbidden monogenic triple `F,F²,F⁴`. `G3-S14` completes those relations to a convergent
   `50`-rule presentation and separates the whole positive-depth odd family from it. `G3-S15`
   then kills that odd family uniformly as a contextual fork and eliminates every one-context use
   of the `405` new second-critical pairs through the exact internal bound `171`. The unresolved
   `G3-S16` then upgrades the external branch to `23` infinite pump schemas and proves that their
   macros `{DT,TD}` form a free binary affine stack. Every discovered context reads only one
   constant stack address. The unresolved step is a genuinely multi-window non-common-fixed fork
   over the quotient or a `bcbc` comparator for general stack addresses with the complete endpoint
   converse, not another fixed-body rank perturbation, guard recurrence, or finite target-depth
   label.
3. **Positive projective transition obstruction.** Derive from a source-unbounded terminal
   section a finite shift incompatibility which no three-dimensional rational same-zero
   representation can realize for any combination of generator ranks and kernels. It must use
   uniform shifts: the conic realizes every static incidence table, `G3-O17` forbids inverse
   saturation, `G3-C05` realizes the strongest fixed equal-length flower yet isolated, and
   `G3-O20` proves that two consecutive solutions on one stationary fixed-boundary pump force
   its entire tail.
4. **Global non-priority word-residual recoding.** Give a computable three-pair reduction with
   both witness directions and a complete arbitrary-new-word converse. Its searchable witnesses
   must use feedback or backward transfer, source-preserving copy, recurring priority cycles,
   counter products, changing/incomparable tests, or genuine unbounded word order outside
   `G3-D05`.
5. **Persistent-word head-separated native source.** Build an undecidable family of exactly
   three prefix-normal productions satisfying `G3-C04`, with an unbounded mixed or neutral word
   surviving every return. `G3-D06` closes functional private-head routing and `G3-D07` closes
   every complete pure two-chamber fork, including arbitrary finite forward branching. The
   empty-pump and genuinely splitting variants remain secondary constructions. The published
   three-rule S5 source is not head-separated: `G3-O24` forbids absorbing its directed deletion
   faithfully. `G3-O25` then deletes rank-one separators, compresses rank two to a two-state block
   carrier, and refutes monotonicity-only lower bounds. The live branch is zero-sensitive GLB
   decoding with invertible `M_y`, together with the adjacent two-state block seam.
6. **Carvalho projective group-orbit separator.** Starting from the exact `G3-M03` saturated
   cover, realize its singleton exponent-one fibre by an effective projective orbit separator.
   In dimension three, `G3-O22` forces an invertible line/plane group orbit. If any transition is
   singular, `G3-O23` produces instead an equivalent invertible two-state carrier. In the
   nonempty branch its faithful projective action satisfies `[T_z]=[T_y]⁻¹[T_x]⁻¹`; uniformly,
   the target Borel coset has at most one group element. Decide or universalize this two-generator
   **group** orbit through global or noncongruence structure; `R32-O22` excludes any criterion
   based only on residue-orbit membership at all integer moduli. Alternatively construct the
   invertible three-state branch. A positive-semigroup
   `M₂(3)` claim must separately eliminate the inverse edges; none is presently known.

The Carvalho split exposed a real semantic seam: algebraic information about the correlated
group and the orbit language selected by a scalar boundary are distinct. `G3-O21` closes the
former by proving actual slice density; `G3-O23` proves that singular positive spelling dynamics
cannot create a third kind of memory; `R32-O22` refutes congruence separation for the resulting
free orbit. The global projective group-orbit separator remains. Empty-consume
pumping and nonfunctional splitting remain boundaries inside leaf 5 until they supply a concrete
computational mechanism. Generic stochastic, Rees/Brandt, affine, and singular-reset ideas are
implementation vocabularies inside leaves 1–3 until they furnish an exact source interface and
all-word theorem. Another fixed-body fit, fixed macro, punctuation placement, affine atlas, or
formal-inverse argument is not a leaf. The joint derivation and evidence boundaries are recorded
in [`m34-wave-68b831a-synthesis-2026-08-11.md`](audits/m34-wave-68b831a-synthesis-2026-08-11.md).

#### Operational program

The fixed `bcbc` and `bcbcbb` targets have stopped serving as the enemy. Their exact grammars
expose the useful mechanism: one carry recognizes complete excursions, while a transient guard
rejects malformed first controls. For `bcbcbb`, the entire reverse certificate is now
kernel-checked on the free monoid. Further fixed-body fitting has no bearing on `M₃(4)` unless it
isolates a transition law that survives uniformization across an unbounded source family.

The former scalar stroke-carry lane is closed only for its phase-line family. In the notation

```text
D=B T C B,       Z=C T B B,       F=C T B C,       X=B T B B,
```

the local identities `BBv=CBTγ` and `DZv=FXv` force a checked terminal/nonterminal collision.
The successful fixed recognizer evades these identities with its transient guard. This confirms
that the collision is an ansatz obstruction, not a lower bound. It remains useful as a regression
test for any uniform formula.

Any positive construction must then extend to one symbolic family computable from `(β,body)`,

```text
λ(β,body), γ(β,body), H_b(β,body), H_c(β,body), H_t(β,body),

λ H_y γ = 0  ↔  pairedCoefficient(β,body,y)=0
```

on every control word and every admissible body. Its projective orbit must leave the finite-mode
expanding affine class of `G3-O04`; merely changing radix, digits, collisions, conjugacy, or chart
count repeats a closed route. `G3-O17` proves that the semantic orbit is already intrinsically
one-way: two required formal inverse components have no positive common future. A constructor
should exploit that absence through singular positive dynamics, not attempt to represent the
inverse completion excluded by `G3-O05`.
A parameter such as `K=κ(a terminal role word)`, including the fitted targets in `G3-C02`, is
forbidden unless a total source-computable formula produces it on
both mortal and immortal inputs. Finite synthesis should share one formula template across a
mixed ensemble of mortal, immortal, and null-history instances; independently fitted matrices no
longer test the live obstruction. Static zero-pattern fitting is now vacuous: the checked conic
already fits every finite prefix-suffix table in three coordinates. Synthesis and lower-bound
experiments must impose the same `H_b,H_c,H_t` on every left and right shift. The strongest
candidate escape is a history-sensitive singular ideal grammar whose data collapse occurs on the
legal chart and whose transient guard irreversibly destroys illegal histories. Denominator growth
outside a faithful full queue chart is closed by `G3-O12`.

Rank-two data maps must now branch at the outset. A common-kernel construction must move its
hidden direction out through a non-invariant toggle; if the kernel is toggle-invariant, the next
data action erases it and only the two-dimensional quotient persists. A transverse-kernel
construction already realizes the bilinear fibre intersection and every minimum-body history;
`G3-O26` proves that its fixed two-line orbit cannot be extended by any source-dependent row. It
must now change the orbit itself. `G3-O27` proves that singular data plus a projectively
involutive toggle still yields only six rank-at-most-two linear carriers, with whole-carrier or
rank-at-most-one terminal sections. Its exact internal survivor is point reachability in a finite
rational `P¹` atlas. `G3-O29` embeds the complete `M₂(3)` incidence core already in one common
identity-toggle chart. `G3-O30` shows that non-scalar toggle powers genuinely generate infinitely
many exact rank-two carriers even for a rational diagonal toggle; the missing step is one
source-uniform terminal section and complete arbitrary-word converse. `G3-O31` proves that a
nonzero row can contain at most one whole carrier, so that section must exploit the moving proper
lines at every other depth. `G3-O32` further proves that each fixed row-column incidence accepts
all depths or at most two, sharply; arbitrarily delayed singleton depths remain possible when the
row depends on the target. `G3-O33` strengthens that survival to a pole-free rational section for
every coefficient triple and every source. Coefficient algebra is therefore closed as an
obstruction; history-to-depth word dynamics is not. `G3-O34` proves the literal generator cannot
serve: identifying its two data matrices collapses a `bcbc` terminal control with a nonterminal
near-fork. Distinct data maps, with the orbit and section rebuilt, are now mandatory. A full-rank
data map remains the other escape. `G3-C06` realizes the distinct rank-two branch explicitly:
it preserves the original infinite carrier prefixes and delayed section while separating that
near-fork at every source. `G3-O35` closes that concrete monoid: its complete binary terminal fork
forces a false zero for `s≠0`, and an exact opposite-semantics collision closes `s=0`. The live
rank-two branch must change its controls or terminal geometry. `G3-S03` shows that every exact
replacement, including a full-rank one, must make the flat/nested fork orbit reducible into a
one- or two-dimensional invariant core. `G3-C07` proves that one raw data letter may nevertheless
be full-rank: an even persistent guard preserves the complete `bcbcbb` language while singular
data `c` performs the syntax reset. The live template is a singular all-word gate plus a
source-dependent persistent core, with the two-dimensional branch shared explicitly with
`M₂(3)`. A lower-bound attack may use the exact `G3-C08` interface: the only live data are a
parity-preserving two-state orbit and its scalar gate. Direct irreducible `Sym²(GL₂)` fork blocks
cannot replace this core because `G3-S03` forces the accepted fork span to be proper; a conic
collision detector must be inserted as ambient leakage and still satisfy the complete raw-word
gate equation. `G3-S06` further reduces every mixed-prime block-code candidate to exact rational
endpoint reachability. Its fixed `bcbc` witnesses force three distinct induced maps and kill all
letterwise codes. `G3-S08` forces the flat/nested block images to be one affine action and kills
common-fixed macro triples. `G3-S10` also kills the literal branch, leaving only a distinct equal-
action kernel pair of raw length `4(2|κ(b)|+|κ(c)|+|κ(toggle)|)`. `D2-S08` does not automatically
apply to the unguarded macro image. `G3-S11` cancels the inert context to a positive reduced
five-factor pair, forces exterior toggle-fixed-point geometry, and computationally excludes
reduced length at most `36`. `G3-S12` turns the pair into an exact crossing transport but proves
that the affine action cannot determine a raw leading-run address; the known kernel changes that
address by two. `G3-S13` eliminates the complete one-context/first-critical hull off the
common-fixed diagonal and formally rejects its exact length-`312` fork. `G3-S14` gives that
five-rule quotient unique normal forms and proves the infinite odd family is external. `G3-S15`
kills that family as a contextual fork at every depth and eliminates all second-critical
one-context repairs through `N=171`, but leaves genuinely multi-window quotient forks open.
`G3-S16` adds a free `{DT,TD}` binary affine stack and `23` exact unary readers; no reader yet
compares arbitrary addresses. After the missing guard and closure proofs,
`D2-S08` still leaves the normalized mantissa unbounded. Any lower-bound attack
must exclude both positive architectures through actual transition data. Backward cancellation,
inverse cofinality, static incidence, and target-depth classes cannot do so.
Do not spend another attack on separator placement, fixed anchors, or control singularity after
recognition; `MM-C01` closes them unconditionally.

The global recoding lane must now state its non-priority mechanism before algebra begins.
Adding finitely many affine factors, sign modes, counter reversals, and recurrent nested tests is
inside `G3-D04`; one-way destructive reset, transfer, fanout, and fixed multiplication are inside
`G3-D05`. The credible exits are feedback, backward or source-preserving transfer, cyclic
priority reuse, nonlinear counter interaction, changing or incomparable tests, or a literal
word-order carrier whose same-length entropy is unbounded.

The free-group trunk no longer needs another Stallings computation, domain parser, or positive
normal-form machine. `G3-M03` already presents the exponent-one equalizer on three positive
letters with exact affine weight and harmless identity padding, and direct source inspection now
shows `χ∘g=χ∘h` globally. `G3-O21` proves every fixed-character slice of the actual graph Zariski
dense and closes its algebraic lane. The remaining constructive lane must detect equality and
weight through spelling-sensitive, graph-only nonalgebraic dynamics. Extending first to
independent `F×F×ℤ` data is four-dimensional by `G3-O16`; a singular third coordinate over a
persistent invertible quotient is closed by `G3-O14`; a standalone syntax series requires six
states by `G3-O15`. `G3-O22` further forces any everywhere-invertible three-state scalar carrier
into a computable line or plane group orbit, but supplies inverse edges only in the group action,
not as positive matrix controls. `G3-O23` collapses every remaining singular saturated carrier
to an invertible two-state group orbit, so spelling sensitivity no longer evades this orbit
classification. Neither actual slice density nor a rank-four semantic coefficient is a same-zero
language lower bound, and no positive-semigroup reduction follows from the inverse edges.
`R32-O22` additionally forbids residue-orbit nonmembership modulo integers as a complete negative
certificate for the remaining group orbit, without excluding algorithms that also use global
word structure.

The native source race now has a local sufficient acceptance test. Supply three head-separated
productions `αₓX⟶Xβₓ`; `G3-C04` then proves that `sβ(w)=α(w)t` forces every cumulative `α` prefix
for every arbitrary trace, and `G3-C03` performs the entire GPCP reduction. The source must fail
both positive and negative drift feasibility from
[`G3-D03`](SALVAGE.md#g3-d03-one-sided-corrected-drift). Recasting the known arbitrary-substring
three-rule system without transporting redex contexts is underflow, not a compiler. A pure
private-head cycle is now equally dead: `G3-D06` gives it a positive one-sided weighting even
with unbounded balanced payload. Competing forward edges do not suffice: `G3-D07` decides the
entire pure-phase fork on pure endpoints, including the canonical mixed-drift example. The live
source must preserve an unbounded mixed or neutral word across returns, or use an empty consume
or split recurrent output.

No further local punctuation fusion of the four displayed pairs should be attempted. The audited
boundary-aligned additive family is immortal, and `G3-O10` closes the nondegenerate square-root
escape on its required fracture domain.

## The rank-three binary wall: `M₃(2)`

### Shared dimension-two artery

The apparent `(3,2)↔(2,3)` symmetry is not a general exchange of dimension and generator count,
but the hard strata are nearly interreducible. The rank-`(2,2)` part of `M₃(2)` is many-one
equivalent to generic rational projective incidence `GPI₂`. The hard rank pattern of `M₂(3)` is
arbitrary rational projective incidence `PI₂`; genericization reduces each `PI₂` instance to at
most two `GPI₂` queries, while every `GPI₂` instance is already an `M₂(3)` instance. Thus the
decision-theoretic chain is

```text
Mort₃^(2,2) ≡ₘ GPI₂ ≤ₘ M₂(3) ≤₂-query GPI₂.
```

[`G3-O23`](SALVAGE.md#g3-o23-singular-triangle-carrier-collapse) adds a second, adjacent artery
from `M₃(4)`. A singular saturated triangle carrier becomes point-to-hyperplane reachability on
`P¹(ℚ)` for the group generated by two projectivities: the third positive triangle control is
projectively `[B]⁻¹[A]⁻¹`. Call this residue `group-PI₂`. It is not ordinary positive `PI₂`
or `GPI₂`, because arbitrary inverses are available and cannot in general be compiled into the
positive monoid on `A,B`. Carvalho supplies the additional promise that the target Borel coset
contains at most one group element; a hit forces a faithful free orbit. The projectively integral
stratum is decidable by the existing `SL₂(ℤ)` orbit machinery. `D2-D02/D08` now decide every
elementary rational group: the generated group must be genuinely non-elementary. The remaining
`UCB₂(S)` subgroup-Borel-coset intersection is not covered by the audited flat-rational-subset or
integral reachability theorems. It should be attacked jointly with `M₂(3)`, while its distinct
word language remains explicit.

[`G3-S04`](SALVAGE.md#g3-s04-symmetric-square-collision-and-fork-obstruction) makes one exact
algebraic bridge across that joint artery. `Sym²` embeds a binary projective orbit in three
coordinates, preserves multiplication, and converts source-target collision into the scalar
square `Δ²`. Nonsingular binary generators remain rank three. This is a detector, not an
interreduction: it uses all three coordinates, adds no positive syntax guard, and the square has
no orientation. Its three-ray determinant factorization also shows that a Sym² orbit confined to
the line/plane carrier forced by `G3-S03` has at most two projective rays, so it falls back into
the invariant-point/pair strata already removed by `D2-D02`.

`G3-S05` closes the full-rank fixed-leakage repair: nonsingular binary pre/post changes and a
nonsingular `3×3` insertion preserve independence of every three distinct Veronese rays. A
planar complete-fork carrier therefore forces the inserted map to be singular. This sharpens the
joint seam without touching singular or dynamically varying leakage.

[`G3-S07`](SALVAGE.md#g3-s07-fixed-rank-two-symmetric-square-leakage-is-elementary) closes the
next fixed-rank branch at the natural equivariance seam. If rank-two `L` supports quotient
dynamics on three distinct Veronese rays, then `ker L` is a common Sym² eigenline. Its symmetric
tensor is either degenerate, yielding a common rational point, or nondegenerate, yielding an
algebraic pair normalized by every generator. Hence a non-elementary UCB₂ action cannot pass
through one fixed rank-two leakage while retaining consistent dynamics on a spanning Sym² orbit.
Only rank at most one, fewer than three orbit rays, or leakage varying with the word/source
escapes this cut.

[`G3-S09`](SALVAGE.md#g3-s09-fixed-symmetric-square-leakage-taxonomy) removes rank at most one
under the same global-equivariance law. A rank-one leakage exposes an invariant quadratic
covector through the transpose row line; its zero locus is a common rational point or algebraic
pair. A zero-rank leakage is literally zero. The unified corollary derives global equivariance
and singularity from three distinct pointwise ray equations and planar image dependence. Thus a
non-elementary UCB₂ action has no fixed linear Sym² leakage repair on a spanning orbit. The
formal two-ray counterexample proves why `G3-S03` cannot silently supply the missing hypothesis:
two Veronese tests leave the middle three-state direction unseen.

[`R32-O22`](SALVAGE.md#r32-o22-congruence-blind-free-orbit) shows that even the promised faithful
free-orbit case has no congruence-separation theorem: one rational target outside the orbit is in
its orbit modulo every positive integer, now by an actual positive word at each modulus. Thus the shared artery must use rational/global word
structure or a noncongruence invariant. The example proves no `p`-adic density statement and no
decision or hardness result. [`G3-O28`](SALVAGE.md#g3-o28-ambient-profinite-blindness-of-the-unique-coset)
now replaces “congruence” by “every finite quotient of `Γ₀(3;ℤ[1/19])`” and replaces ray agreement
by equality of the entire target matrix. The shared artery must therefore use syntax, height,
Archimedean structure, or another infinite invariant; a finite ambient-group invariant is dead.
[`D2-D09`](SALVAGE.md#d2-d09-step-three-shear-height-decision) proves this distinction is real:
height decides the fixed step-three family despite its profinite blindness. The remaining question
is whether an effective descent survives after recurrent target stabilizers are quotiented.
[`D2-O05`](SALVAGE.md#d2-o05-promised-empty-free-orbit-inverse-cycle) rules out the raw primitive
height as that descent: one free dilation--parabolic orbit has a positive target cycle and forced
inverse heights `5→3→5`. [`D2-O06`](SALVAGE.md#d2-o06-bounded-inverse-recurrence-forces-a-stabilizer)
shows that every bounded-height injective-prefix recurrence forces a nontrivial target stabilizer.
[`D2-O10`](SALVAGE.md#d2-o10-finite-bounded-prefix-horizon) strengthens this to the explicit
finite horizon `(2H+1)²+1`. Hence the next hard no-instance cannot combine trivial target
stabilizer with bounded recurrence. `D2-O11` further decides any supplied bounded window under
trivial source stabilizer by conjugating its collision witness. Unbounded-height paths remain
undecided, although `D2-O12` now forces the exact finite-family rate
`N≤(2H+1)²` below every height ceiling `H`. `D2-O13` strengthens this further: every fixed
height sublevel is visited only finitely often, so the surviving path is proper but lacks a
computable last-return bound. `D2-O14` then exhibits a promised-empty trivial-stabilizer instance
with an irrelevant proper inverse ray, proving that directional legality is indispensable.

Work on projective incidence should therefore be treated as a joint `M₃(2)`/`M₂(3)` campaign.
A `GPI₂` algorithm decides all of `M₂(3)` and the rank-`(2,2)` artery of `M₃(2)`; a universal
encoding in either incidence form transfers to the other. This does not settle full `M₃(2)`:
the rank-`(3,2)` return-recurrence artery below remains independent. Conversely, arguments using
its order-three return structure need not say anything about `M₂(3)`.

### Rank census

`M₃(2)` remains unresolved. The binary pair can, however, be divided by rank without losing
the word problem.

| Rank profile | Reduction |
| --- | --- |
| `(3,3)` | immortal: every product is a unit |
| any rank `0` | immediately mortal |
| any rank `1` | decidable through order-at-most-three scalar recurrence zeros; [`R32-O01`](SALVAGE.md#r32-o01-rank-one-profile-collapse) |
| `(2,2)` | exact two-vertex square of `2 × 2` edges; [`R32-S02`](SALVAGE.md#r32-s02-two-plane-edge-square) |
| `(3,2)` | products of one third-order `2 × 2` return recurrence; [`R32-S01`](SALVAGE.md#r32-s01-split-return-normal-form) |

Thus two residues survive:

```text
rank (2,2): generic projective incidence GPI₂,
rank (3,2): mortality of {VAⁿU : n≥0},  A∈GL₃(ℚ).
```

The first is now reduced exactly to the dimension-two hard core. Rank-one punctuation fractures
every constrained path at consecutive singular edges. All edge-rank patterns are decidable
except one compatible rank-one loop with three units; Lean transports that stratum to one
intrinsic generic PI₂ instance and proves compatibility forces `β=1`. An audited effective
cyclic-orbit algorithm, backed by effective `S`-unit enumeration, discharges the sole
two-parameter cross-edge stratum. Together with the checked reverse compiler
[`R32-M01`](SALVAGE.md#r32-m01-generic-reverse-edge-compiler) this gives

```text
Mort₃^(2,2) ≡ₘ GPI₂.
```

The graph constraint is therefore gone, and the opposite genericity seam is gone for
decidability. The two exceptional source rays are exact. If both orientations are bad at two
sources, their relative projectivity permutes those sources and both labelled transitions exit
together. Positive first exit therefore reduces arbitrary PI₂ to at most two GPI₂ queries.
Every generic instance also scales to `α=β=1` without changing any word zero. Generic PI₂
itself remains unresolved. See
[`R32-S35`](SALVAGE.md#r32-s35-positive-projective-incidence-genericization).

The first exact arithmetic subfamily is now isolated. Two affine branches with common prime
denominator use p-adic denominator poisoning as a complete all-word legality guard; at `p=2`,
the two legal residues give one deterministic parity-selected orbit. Conversely, an injective
homomorphic Möbius word store cannot support recurrent delete-front/append-back updates through
any finite projective controller: every such update is a deleted-prefix inverse times a common
centralizer element, and an injective binary store has trivial centralizer. Thus the live
undecidability route is intrinsic nonhomomorphic arithmetic dynamics, not a free-word store with
finite queue control. See [`R32-S36`](SALVAGE.md#r32-s36-guarded-affine-projective-incidence)
and [`R32-O19`](SALVAGE.md#r32-o19-projective-queue-centralizer-obstruction).

This arithmetic core already contains an exact named benchmark. The fixed projective maps

```text
A(z)=2z,       B(z)=(2z−1)/3
```

generate an integer target from `1` if and only if that target reaches `1` under shortcut
Collatz. A first illegal odd-predecessor letter creates negative 3-adic valuation permanently,
so the converse holds for every binary word. Central rescaling puts every nonzero target
instance in the `α=β=1` chart without changing its zero language. This is a hardness boundary,
not an undecidability result; see
[`R32-S37`](SALVAGE.md#r32-s37-normalized-shortcut-collatz-incidence).

The guarded-affine universality lane has now collapsed to its true arithmetic seam. Clearing any
odd denominator adds no register. When both parity-branch slopes have magnitude one, every orbit
enters an explicit finite interval; when both have magnitude at least three, every orbit outside
an explicit interval escapes monotonically. Only one unit slope paired with one odd expansive
slope survives. After affine conjugacy and acceleration it is a signed generalized Syracuse map

```text
n ↦ (±1)^(v₂(an+B)−1)(an+B)/2^v₂(an+B).
```

Every affine macro has an odd-numerator multiplier, so direct radix-tag append, direct FRACTRAN
valuation decrement, and finite affine-chart microcoding fail by slope or telescoping. The only
remaining memory mechanism is nonhomomorphic carry propagation against the fixed eventually
periodic 2-adic word `−B/a`. Genericity is discharged by bounded traversal of the common bad
source set. See
[`R32-S40`](SALVAGE.md#r32-s40-binary-affine-syracuse-collapse) and
[`m32-binary-affine-syracuse-2026-08-11.md`](audits/m32-binary-affine-syracuse-2026-08-11.md).

The opposing GPI₂ decision route now has an exact ambient normal form. After an effective
rational basis change and localization at finitely many primes, arbitrary projective incidence
is identity membership in a rational subset of `GL₂(ℤ[S⁻¹])`, formed from the positive monoid
and one explicit upper-triangular coset. A uniform rational-subset algorithm would settle this
lane, but the supposedly elementary solvable side already contains the obstruction. The fixed
Collatz projectivities generate the metabelian cusp `Γ₆=ℤ[1/6]⋊ℤ²`; pointwise shortcut
Collatz is membership of a variable translation in one fixed rational subset `R=PK` of `Γ₆`.
The positive monoid is free. What is hard is its ordered intersection with the parabolic coset,
not relations or non-elementary geometry. See
[`R32-S41`](SALVAGE.md#r32-s41-parabolic-rational-subset-normal-form) and
[`m32-parabolic-rational-subset-2026-08-11.md`](audits/m32-parabolic-rational-subset-2026-08-11.md).

Finite ambient quotients cannot see that order. In every finite image of `Γ₆`, the image of the
positive monoid `P={A,B}*` is already the whole generated group, so the fixed rational subset
`R=PK` also fills the image. No congruence or profinite saturation of the ambient group can
separate a translation from `R`; a viable finite abstraction must retain positive spelling.
This is [`R32-O21`](SALVAGE.md#r32-o21-finite-image-positivity-collapse).

Even a free orbit with trivial stabilizer defeats congruence separation. For `A=U(3)`,
`B=L(3)`, `p=[1:1]`, and `q=[10:13]`, ping-pong proves `q∉⟨A,B⟩p` over the rationals, while
an explicit five-factor word sends `p` projectively to `q` modulo every positive integer. This
is [`R32-O22`](SALVAGE.md#r32-o22-congruence-blind-free-orbit). The decision route must use
more than the full tower of ordinary integral residues.

The rank-`(3,2)` profile is the genuinely new artery. If `B=UV`, every binary word containing
`B` is governed exactly by

```text
M_n = VAⁿU ∈ M₂(ℚ).
```

The entries of `M_n` are algebraic linear recurrences of order at most three, but the problem
asks whether the semigroup generated by the infinite recurrence family contains zero. Skolem
decidability for each fixed entry does not decide products of returns with independently chosen
waits.

The irreducible-cubic fallback is now sharply reduced. Cubic-field faithfulness makes every
return nonzero and every singular return rank one. A computable common-left factor makes every
unit return a projective involution and every singular return square-zero. Unless
`χ_A=X³−N`, the singular waits are finite and the remaining exact problem is reachability
between their forced lines under an order-three recurrence of reflections. In the pure case,
Lean collapses all waits modulo three. The unique one-singular normal form has reverse-compiler
scalars `α=β=μ⁻¹`, so it is already GPI₂; zero- and two-singular triples are decidable. Thus only
the non-pure reflection orbit remains as an independent cubic fork.

That fork now has a canonical endpoint form. Projected multiplication on the cubic field's
trace-zero plane writes every faithful family as `Mₙ=F T_(γθⁿ)`, and every
`F∈GL₂(ℚ)` occurs: the physical origin imposes no twist constraint. Clifford normalization makes
the exact residue a null-conic orbit under the adjoint isometry of an arbitrary `Q` interleaved
with recurrence reflections. An explicit physical family with `χ_A=X³−X−1` has unit returns
`M₁=F`, `M₄=FR` generating a free binary submonoid and an injective rational-line orbit. Hence
recurrence order, involutivity, and finite singular timing do not force finitely many bridge
states or bounded bridge length. See
[`R32-O16`](SALVAGE.md#r32-o16-irreducible-cubic-punctuation-collapse) and
[`m32-cubic-null-conic-orbit-2026-08-10.md`](audits/m32-cubic-null-conic-orbit-2026-08-10.md).

The endpoint seam is now closed, and it exposes a sharper enemy. For the non-pure companion
ambient `A³+A²=I`, one rank-two physical twist places the actual singular image at the base of a
free selected binary semigroup and makes selected wait one hit the actual singular kernel. A
second twist has an injective free orbit over selected waits `{1,5}` and Lean proves that no
selected word hits the kernel. Nevertheless the strictly unselected unit word
`[12,12,8,12,12,15,8]` creates an exact zero. Selected ping-pong therefore supplies no all-waits
soundness. The remaining cubic problem is endpoint reachability for the complete fixed recurrence
`M_(n+3)=M_n−M_(n+2)`, or a normalization proving every first hit has a selected representative.
See [`R32-S42`](SALVAGE.md#r32-s42-non-pure-cubic-endpoints-and-false-waits) and
[`m32-cubic-endpoint-false-waits-2026-08-11.md`](audits/m32-cubic-endpoint-false-waits-2026-08-11.md).

The scalar flag-preserving slice now has an exact arithmetic owner. For the false-wait family,
the normalized lower-left coefficient is an integral recurrence

```text
u₀=0,  u₁=0,  u₂=1,  uₙ₊₃=uₙ−uₙ₊₂.
```

Its consecutive triples preserve one cubic norm, and every zero gives an integral solution of
`x³−xy²+y³=1`, the exceptional discriminant-`−23` Thue equation. Lean checks the reduction and
the zeros `0,1,5,14`; the Delone–Nagell classification and an audited orbit exclusion prove these
are all the zeros. The exact positive flag-preserving alphabet is therefore `{1,5,14}`. The
false word proves that this complete scalar classification cannot by itself control cancellation
among nontriangular letters. See
[`R32-S43`](SALVAGE.md#r32-s43-cubic-defect-norm-and-thue-throat) and
[`m32-cubic-defect-thue-2026-08-30.md`](audits/m32-cubic-defect-thue-2026-08-30.md).

The complete matrix residue is now equally explicit. One defect window determines every return
entry and its determinant, and every nontriangular return acts as one recurrence-digit negative
continued-fraction letter `z↦xₙ−tₙ/(z+yₙ)`. Cancellation is therefore an exact generalized
continuant language. It is not locally guarded: `M₁₅M₈M₂₆` and `M₁₂M₈M₃₃` are upper
triangular even though every factor and both adjacent pairs in each word are nontriangular.
These are lawful derived affine macro letters, but they neither classify the triangular language
nor reach the singular endpoint. The remaining fork is descent or decision for the unbounded
recurrence-digit continuant, or a sound compiler that uses its derived macros while controlling
every other word. See [`R32-O23`](SALVAGE.md#r32-o23-cubic-continuant-fracture) and
[`m32-cubic-continuant-fracture-2026-08-31.md`](audits/m32-cubic-continuant-fracture-2026-08-31.md).

Finite triangular-macro completion is now excluded. The exact projective actions contain a
four-ray cycle with entry and exit, pumping
`[19,15][7,8,21,15]ᵏ[7,8,2]`. Every such word is upper triangular, its length is `5+4k`, and
every nonempty proper suffix is nontriangular. These are therefore concatenation-prime
upper-triangular words of unbounded length. No bounded-length dictionary of triangular macros,
and no finite such dictionary whose accepted words factor into its members, can generate the
whole triangular language. This does not establish nonregularity or exclude finite-state
recognition without accepted-factor boundaries. The live fork is now a global descent or
finite-nucleus theorem compatible with the recurrent four-ray component, or a recognizer that
does not factor accepted words into triangular macros. See
[`R32-O24`](SALVAGE.md#r32-o24-unbounded-prime-continuants) and
[`m32-unbounded-prime-continuants-2026-08-31.md`](audits/m32-unbounded-prime-continuants-2026-08-31.md).

The exact terminal-product nucleus is now dead as well. In the same fixed recurrence, wait five
and the positive block `[8,1,15,8,1,8,15,21,15]` have a common normalized diagonal ratio
`4/25` and affine digits `274/300` and `149/300`. Their binary products carry a base-`(4,25)`
positional numerator whose first digit is recovered modulo four. Lean proves that the resulting
physical products are injective even up to rational rescaling, giving `2^n` distinct
upper-triangular transformations at every macro depth. Prefixing the known endpoint bridge by
any code word yields a zero, and these bridge transformations remain projectively distinct.
This does not refute a finite quotient which remembers only the common terminal ray or another
abstract congruence. The live dual is now explicit: compose a positive read/compare operation
with this write-only stack, or prove that all such readers collapse into a decidable affine
quotient. See [`R32-S57`](SALVAGE.md#r32-s57-free-cubic-continuant-radix-stack) and
[`m32-cubic-continuant-radix-2026-08-31.md`](audits/m32-cubic-continuant-radix-2026-08-31.md).

The write-only seam is now closed. The same positive recurrence semigroup contains exact
projective inverses for both radix letters: one reader has physical length `2089`, the other
`1166`, and each correct reader deletes its head letter while preserving every suffix up to a
nonzero scalar. The construction uses a reciprocal-ratio terminal loop corrected by positive
and negative parabolic translations. It also exposes the remaining obstruction exactly. A wrong
zero-read leaves translation `−125/48`, a wrong one-read leaves `125/48`, and the two defects
cancel. Hence a terminal identity test alone is unsound. The compiler lane now needs a local
mismatch trap or a grammar admitting at most one defect sign; the decision lane may exploit the
resulting affine signed-defect quotient. See
[`R32-S58`](SALVAGE.md#r32-s58-positive-cubic-radix-readers) and
[`m32-cubic-continuant-reader-2026-08-31.md`](audits/m32-cubic-continuant-reader-2026-08-31.md).

The local mismatch seam is now closed for a designated spelling. Appending the true radix
letter after every read contracts successive signed errors by `4/25`; the resulting
base-`(4,25)` code is injective on digits `−1,0,1` by a modulo-four induction. Exactly enough
true-readers erase the clock baseline, and splitting the existing endpoint bridge after its
first positive wait converts the surviving translation into a nonzero scalar multiple of the
singular return. The resulting physical word is zero exactly when every guessed bit matches its
writer. What remains is global syntax, not local comparison: an arbitrary raw wait word may omit
or split a clocked block, or reach an unrelated zero. The cleanup multiplicity itself is now
self-checking. With `n` clocks and `m` cleanup readers, the split endpoint bridge forces an affine
balance equation. Its right side has odd `5`-adic valuation when `n>m` and odd `2`-adic valuation
when `m>n`, while every nonzero signed mismatch radix has even valuation at both primes. Hence
zero forces `m=n` and then forces every comparison to match. The fixed family already contains
an unconditional endpoint zero, so this remains a local semigroup gadget rather than a reduction
for that fixed instance. The compiler lane needs instance-dependent target geometry together
with an arbitrary-word block converse or an independent control phase. See
[`R32-S59`](SALVAGE.md#r32-s59-clocked-cubic-radix-comparator) and
[`R32-S60`](SALVAGE.md#r32-s60-self-balancing-cubic-comparator-cleanup), with audits
[`m32-cubic-continuant-mismatch-clock-2026-08-31.md`](audits/m32-cubic-continuant-mismatch-clock-2026-08-31.md)
and
[`m32-cubic-continuant-self-balance-2026-08-31.md`](audits/m32-cubic-continuant-self-balance-2026-08-31.md).

The raw punctuation is now complete. After removing the constant determinant factor, the cubic
return at wait `n` has coefficient `Δ_n` with `Δ₀=0`, `Δ₁=2`, `Δ₂=3`, and
`Δ_(n+3)=Δ_(n+1)+Δ_n`. Lean proves `Δ_n>0` for every positive `n`; hence `M₀` is the sole
nonunit return and every positive-only word is a unit. Its exact rank-one factorization reduces
unrestricted mortality to one scalar bridge over positive waits. This kills the remaining
punctuation question but sharpens the semantic one: classify the positive bridge language. It
also makes the target rectification unavoidable. The fixed family already has at least two
formal seven-positive-wait bridge zeros, so S57–S60 cannot alone encode an instance-dependent
answer in that family. A cell-closing compiler must vary or twist the endpoint geometry, or add
an independent control representation. See
[`R32-S61`](SALVAGE.md#r32-s61-sole-singular-cubic-punctuation) and
[`m32-cubic-continuant-punctuation-2026-08-31.md`](audits/m32-cubic-continuant-punctuation-2026-08-31.md).

### ReturnSquare laboratory

[`R32-S03`](SALVAGE.md#r32-s03-returnsquare-normal-form) is the first completely normalized
rank-`(3,2)` family:

```text
A=diag(1,q,q²),       B=UV,
VAⁿU =
  [(c+1)q²ⁿ−1   qⁿ]
  [c              qⁿ].
```

The zero-wait return is an internal rank-one separator. Every other return is invertible, so
physical mortality is exactly one scalar bridge over positive waits. This removes the binary
word grammar entirely and leaves a rational projective orbit problem.

The family is now sharply fenced:

- `c=−1` is degenerate: `B²=0`;
- one-return zeros are exactly the resonances `c=−q⁻ⁿ`;
- two positive returns never vanish, by the discriminant square cage
  [`R32-O02`](SALVAGE.md#r32-o02-two-return-square-cage);
- `c≥0` is immortal;
- writing `c=−d`, the entire half-line
  `d > 1+(q−1)/q²` is immortal by the projective double-cone wall
  [`R32-D01`](SALVAGE.md#r32-d01-returnsquare-immortality-walls);
- a literal reversible push/pop replacement for the squaring rail requires at least four exact
  states, by [`R32-O03`](SALVAGE.md#r32-o03-reversible-stack-state-tax).
- adding a third singular `1,t,t²` mode still cannot implement reversible squaring, while two
  exact squaring checks collapse to blind scaling, by
  [`R32-O04`](SALVAGE.md#r32-o04-quadratic-pencil-verification-collapse).
- if `q` is a prime power, mortality occurs exactly at the one-return resonances, by
  [`R32-D02`](SALVAGE.md#r32-d02-prime-power-returnsquare-classification).
- at an arbitrary integral base, every rational bridge root is supported on the primes of `q`;
  every positive p-adic valuation is the base valuation times one common proper-tail exponent,
  by [`R32-S44`](SALVAGE.md#r32-s44-composite-returnsquare-tail-synchronization).
- every rational fraction `d=A/B` has an exact reversed two-coordinate pullback. At a prime
  dividing `B`, the unique final predecessor has valuation
  `a−min(2(w+1)vₚ(q),a)` unless `a=2(w+1)vₚ(q)`; at equality its valuation is
  nonpositive, by
  [`R32-S45`](SALVAGE.md#r32-s45-fraction-pullback-and-terminal-denominator-shell).
- every later inverse step is tropical away from four word-visible valuation walls. If the
  target depth is `x` and the selected scale depth is `b`, then `x+b<0` resets to the full
  denominator depth `a`; above zero the next depth is `a−min(x+b,2b,a)` unless two displayed
  terms tie, by
  [`R32-S46`](SALVAGE.md#r32-s46-denominator-predecessor-shell-grammar).
- all four ties have exact normalized residue laws. The walls `x=b`, `x=a−b`, and `a=2b`
  reduce to one displayed residual denominator after removing their common `B`; `x=−b` has a
  unit denominator and carries exactly the valuation of `st−A`. An exact nonresonant word with
  only even scales crosses both `x=−b` and the critical wall, so no wall or shared denominator
  prime is itself an obstruction, by
  [`R32-S47`](SALVAGE.md#r32-s47-exact-four-wall-residue-laws).
- every mortal fraction `A/B` obeys two word-independent cyclotomic filters: modulo every prime
  divisor of `q−1`, `B≡A`; modulo every prime divisor of `q+1`, `B≡±A`, by
  [`R32-S48`](SALVAGE.md#r32-s48-fractional-cyclotomic-finite-walls).
- consecutive exact denominator-center hits force scale exponents `n,2n,4n,…` and can reach the
  physical endpoint only at a one-return resonance. The exact zero residue of the critical wall
  is incompatible with mortality in every fixed-ray quotient where `A/B` remains reduced, by
  [`R32-S49`](SALVAGE.md#r32-s49-geometric-center-chain-extinction).
- after the zero equal-scale residue, immediate re-entry into a denominator center at an odd
  exponent is impossible in every reduced odd signed-ray quotient, by
  [`R32-S50`](SALVAGE.md#r32-s50-odd-signed-re-entry-extinction).
- separating the head wait and moving the tail through explicit adjugates gives one exact
  two-coordinate power-ray incidence. Any positive base-prime valuation fixes the complete tail
  exponent, leaving finitely many weighted tails and no head enumeration, by
  [`R32-S51`](SALVAGE.md#r32-s51-weighted-tail-adjugate-certificate).
- in the remaining pure-denominator branch, an integral denominator prime with depth `a` greater
  than twice the complete tail depth `Er` forces `a=(head+1+2(first+1))r` and bounds the rest of
  the tail by `2 waitExponent(rest)<head+1`. This entire deep chamber is finite; two jointly
  deep primes must also have equal normalized denominator depths `vₚ(B)/vₚ(q)`, by
  [`R32-S52`](SALVAGE.md#r32-s52-deep-pure-denominator-synchronization).
- the finite chamber extends through the complete-tail wall. If one denominator prime is deeper
  than the proper rest, either `R32-S52` applies or `head+1≤2 waitExponent(rest)`. The first tail
  scale then divides a fixed nonzero rest coordinate unless `B=q^(head+1)` is already resonant,
  by [`R32-S53`](SALVAGE.md#r32-s53-proper-rest-pivot-certificate).
- the entire pure-denominator chamber is finite without a depth hypothesis. Its exact affine
  predecessor preserves `[-1,∞)`, and every viable step at scale `t` decreases a target above
  one by at least `t−1`. A bridge zero therefore satisfies
  `q^(head+1)+Σ(q^(wait+1)−1)≤B`; every tail scale is below `B` and
  `q^(head+1)+|tail|(q−1)≤B`, by
  [`R32-S54`](SALVAGE.md#r32-s54-global-pure-denominator-descent).
- these certificates assemble into a uniform executable decision procedure. For a reduced
  positive fraction `A/B`, numerator one uses the `R32-S54` box. Otherwise `minFac(A)` either
  lies outside the base support and rejects mortality, or fixes the tail weight; each tail then
  bounds its head by the absolute upper integral adjugate coordinate. The exceptional fraction
  `1` is handled exactly as the zero-power resonance, by
  [`R32-S55`](SALVAGE.md#r32-s55-effective-returnsquare-decision).
- the rightmost pure-denominator inverse step contracts the terminal target below its quotient
  by the selected scale. A word `head::(properTail++[last])` therefore obeys the strict budget
  `q^(last+1)(q^(head+1)+Σ_properTail(q^(wait+1)−1))<B`. Since every nonresonant zero needs at
  least three returns, mortality is resonance-only throughout `B≤2q²−q`, by
  [`R32-S56`](SALVAGE.md#r32-s56-terminal-weighted-shallow-classification).
- replacing common powers of one base by a scale alphabet totally ordered under divisibility is
  unsound: `[3,15,3,3,15,3,3,3]` has the exact nonresonant root `d=25/27`, by
  [`R32-O25`](SALVAGE.md#r32-o25-divisibility-chain-returnsquare-fracture).

Thus the ReturnSquare decision problem is closed. For every reduced positive rational `d=A/B`
and every `q≥4`, Lean constructs a finite `Finset` whose exact bridge zeros are equivalent to
physical mortality, then derives a `Decidable` term from its nonemptiness. Parameters `c≥0` are
already immortal, while bases `2` and `3` belong to the stronger prime-power classification.
What remains is classification, not decidability: execute the candidate sets to decide whether
composite bases admit a bounded nonresonant multi-return root, or prove that every such set
contains only the one-return resonance.
The one-base geometric architecture is essential: mere divisibility comparability or
common prime content cannot replace it. The one-base prime-power architecture remains closed.
The two-coordinate pullback is not a reduction to finite-alphabet `M₂(3)`; every `qⁿ` remains a
distinct return letter.

The obvious nonsemisimple escape is closed as well. A `1⊕J₋₁` ambient mode can realize the
exact parity-Collatz rails, but the rank-compatible branch is unique up to scalar and preserves
a nonzero line modulo seven. This is
[`R32-O05`](SALVAGE.md#r32-o05-jordan-parity-verifier-collapse).

ReturnConvert [`R32-M03`](SALVAGE.md#r32-m03-two-scale-return-conversion) exposed the missing
valuation direction. The amalgamated guard
[`R32-M04`](SALVAGE.md#r32-m04-amalgamated-valuation-guard) now closes the matrix-engineering
problem outright. In three exact modes it combines a rank-one internal separator, invertible
positive returns, legal-wait verification, and a permanent p-adic trap for every illegal wait.
The checked guarded normal form
[`R32-S04`](SALVAGE.md#r32-s04-guarded-return-normal-form) proves that arbitrary physical
mortality is exactly deterministic target reachability for one rational p-adic orbit.

That orbit is now localized further. In the shifted coordinate, each step is a variable-length
p-adic prefix decoder followed by one fixed fractional-linear map; on a branch, the reciprocal
residual updates affinely. This is
[`R32-S05`](SALVAGE.md#r32-s05-prefix-shift-and-affine-residual).
More decisively, [`R32-S06`](SALVAGE.md#r32-s06-resonance-localization) proves that every
nonresonant ready continuation strictly decreases the positive wait, while an overdeep tail is
poisoned. Every infinite ready chain therefore enters the equal-depth resonance shell
arbitrarily late.

The obvious rational-counter route is closed. By
[`R32-O06`](SALVAGE.md#r32-o06-rational-affine-wait-rail-rigidity), a reduced rational chart
cannot realize `a↦da+h` at infinitely many prime-power configurations unless the wait update is
the identity. The proof forces `P(λXᵈ)∣Q(X)`, then `d=1`, equal degrees, and finally a p-adic
contradiction for every nonzero shift `h`.

The global state has now been contracted again. By
[`R32-S07`](SALVAGE.md#r32-s07-decoded-residual-address-normal-form), the reciprocal center
displacement lies in one of pairwise disjoint rational p-adic spheres, and each sphere is the
image of the rational unit shell under one explicit Möbius inverse branch. Physical mortality
is exactly finite inverse-address membership of the terminal residual. Distinct branches share
no finite fixed point, so no single Möbius chart makes their interaction affine.

This address system has genuine rational nested dynamics: the checked period-three itinerary
uses waits `1,2,3`, with two consecutive resonant increases followed by nonresonant descent. The
first naïve periodicity conjecture is therefore false.

The first global arithmetic sieve is also exact.
[`R32-M05`](SALVAGE.md#r32-m05-cyclotomic-reset-or-cancellation-sieve) projectivizes the
primitive integer-pair recurrence and proves that every prime divisor of `pᵃ−1` either resets
the reduced point to one or is swallowed by the common reduction factor. The latter event is
not an untyped failure of a finite quotient. The general one-sided certificate owner is
[`R32-M02`](SALVAGE.md#r32-m02-finite-quotient-sieve); here the quotient semantics are exact:
for every divisor `d ∣ pᵃ−1`, primitive reduction
swallows `d` exactly when the source residual is congruent to the terminal residual modulo `d`.
The remaining local-global escape is therefore repeated terminal shadowing at unbounded
cyclotomic orders.

[`R32-S08`](SALVAGE.md#r32-s08-cumulative-endpoint-recurrence) removes primitive normalization
from the state. Retaining every signed removed content yields one deterministic integral pair
recurrence from `(A+D−L,1)`; the cumulative numerator alone obeys a second-order exact-division
law, and terminality is exactly its vanishing. Primitive content, complementary content, and
reduced denominators are derived local factors.

[`R32-S09`](SALVAGE.md#r32-s09-complete-cancellation-law) removes the remaining ambiguity in
that split. For every prime `ℓ≠p`, the exact cancellation depth is

```text
min(vℓ(T(m,n)), vℓ(L(1−pᵃ)m)).
```

Fixed and novel cancellation are not separate algebraic phenomena: both are the intersection of
the terminal divisor with one displacement divisor. The distinction is dynamical. Outside fixed
support the displacement valuation is cyclotomic; at fixed primes it can also contain source
valuation. On a primitive source, however, determinant support bounds the cancellation actually
attained by `vℓ(DL(pᵃ−1))`.

[`R32-S10`](SALVAGE.md#r32-s10-logarithmic-wait-and-height-envelope) makes that bound effective.
Lifting the exponent proves logarithmic wait dependence at every fixed prime, including the
two-adic case. Globally, `|g|≤|DL||pᵃ−1|`. More importantly, a nonzero legal step obeys

```text
a ≤ log_p((|A|+|D|+|L|)H),
H′ ≤ (|A|+|D|+|L|)H.
```

Thus waits grow at most linearly with orbit time. This removes superlinear clock amplification
as a universality mechanism, but it does not yield a finite state space: exponential height and
linear counter growth remain possible.

[`R32-S11`](SALVAGE.md#r32-s11-primitive-factor-terminal-gate) now performs the first exact
local-global comparison. Let the primitive cyclotomic radical be the product of the distinct
prime factors of `Φ_a(p)` which do not divide `a`. If that radical exceeds

```text
(|A−L|+|D|)H,
```

then the current state is terminal or at least one exact-order prime survives reduction and
resets the next projective state to one modulo that prime. The complementary no-reset theorem
retains every prime multiplicity: the full primitive part `P_a(p)` divides the removed content
and satisfies

```text
p^((s−1)a) P_a(p) ≤ (|A|+|D|+|L|)H.
```

Thus repeated prime powers are no longer an uncontrolled escape. Glasby-Lübeck-Niemeyer-Praeger
identify this part as `Φ_a(p)` or `Φ_a(p)/r` above exponent two. Lean now proves the exact
surrogate needed for growth and combines it with the content budget:

```text
p^((s−1)a)(p−1)^φ(a) ≤ a(|A|+|D|+|L|)H.
```

The remaining task is global: combine strong-primitive absorption on no-reset branches with
exact-order quotient dynamics on reset branches.

[`R32-S12`](SALVAGE.md#r32-s12-exact-order-projective-automata) turns surviving factors into an
exact finite proof system. A primitive divisor `ℓ` of exponent `e` yields a transition automaton
on `ℙ¹(𝔽ℓ)⊔{cancelled}` whose labels are the `e` wait residues. On an actual primitive integral
step, `cancelled` is reached exactly when `ℓ` is swallowed by normalization; otherwise the
automaton follows the reduced rational state. A closed invariant containing the reset but not
cancellation is therefore a complete certificate against primitive terminal executions.

[`R32-S13`](SALVAGE.md#r32-s13-canonical-decoded-integral-lift) closes the normalization
direction needed to apply those certificates to the physical pair. Canonical rational
numerator-denominator coordinates are primitive, and a decoded target is a p-adic unit, so its
canonical denominator is prime to `p`. In the raw branch fraction

```text
N / (p^(sa)T),
```

the entire `p^(sa)` scale must therefore divide the common reduction factor. Removing it yields
exactly one `PrimitiveIntegralStep`; decoded executions lift step for step. A safe quotient
invariant now proves decoded unreachability and physical immortality without an independent
rational-cycle argument.

This mechanism is nonvacuous. For the checked rational period-three survivor, `ℓ=11` has exact
order five for base three, and all residue transitions collapse onto `{1,4,6,10}`. The terminal
ray is zero and cancellation is unreachable. Lean consequently excludes every primitive
integral terminal execution and, through the canonical lift, proves the physical pair immortal.
Reconnaissance also found many saturated quotients, so the remaining question is not whether
finite certificates exist or are sound, but whether some effective family is complete. The
modulo-eleven example owes its rank-one collapse to `11∣D`; parameter-divisor certificates and
genuinely projective primitive quotients should be analyzed separately.

The parameter-divisor branch is now uniform. If a primitive divisor also divides `D`, while
`A−L` and every `A−Lpʳ` over one period remain nonzero, all quotient transfers are rank-one
resets of the nonzero affine shell and the terminal residual is zero. This is an immediate
finite no-certificate. The condition is the clean group-theoretic exclusion
`A/L∉⟨p⟩⊆𝔽ℓ×`. The physical theorem uses the canonical terminal pair, so an unreduced raw
terminal presentation cannot make the certificate vacuous.

[`R32-S14`](SALVAGE.md#r32-s14-drift-divisor-certificate-classification) closes this subfamily
exactly. At a primitive drift divisor, *some* closed safe quotient invariant exists if and only
if the center avoids the scaled base-power orbit. If a residue hits the center, closure from the
reset forces either quotient annihilation or the terminal zero ray in one step; no smaller or
less obvious invariant can rescue the certificate. If the scale survives, the forbidden orbit
has exactly `e` elements and the classifier accepts exactly `ℓ−e` center residues. Thus large
primitive factors of small order kill most center classes, while `e=ℓ−1` leaves only the zero
center class. The test is executable in Lean and the modulo-eleven example is accepted by it.

[`R32-S15`](SALVAGE.md#r32-s15-finite-quotient-completeness) closes the missing global clause.
The zero-residue transfer is the rank-one reset with covector `(A−L,D)`, so its kernel is
exactly the terminal residual. Any invariant containing terminality therefore contains
cancellation one step later. Safe certificate existence is precisely cancellation
unreachability; terminal exclusion is redundant. This also kills ordinary synchronized
multi-prime products: every joint invariant excluding cancellation in either coordinate
projects to a cancellation-free invariant in each factor. A product cannot rescue any failed
factor. Further local-global progress must model what happens *through* primitive
renormalization, retaining swallowed-factor valuations instead of treating cancellation as an
absorbing reject state.

The cancellation-jet and tangent-cocycle detour has now been removed from the live theorem
bank. Its projective coordinate was the original residual in a known moving scale, so it did
not supply a second register. The only additional datum was the primitive normalization
scalar. That scalar is now retained directly by the endpoint/content calculus below; carrying
an auxiliary tangent machine obscured rather than strengthened the argument.

[`R32-S26`](SALVAGE.md#r32-s26-evaluation-frame-gauge-closure) closes the parameter-lifting
detour. If `F(j,H)` is the evaluation frame with columns `j` and `(1,H)`, the consecutive
Cramer transition is exactly

```text
F(j,H)⁻¹F(j′,H′).
```

The matrix cocycle telescopes. Its determinant `κ=Hj₀−j₁` is the coordinate denominator for
recovering two fixed parameter values, not a new state variable. Relative to the reset anchor,

```text
κ = j₀(H+α)−A(j).
```

If the anchor evaluation has depth `d`, any defect deeper than `d` forces the residual back
onto the depth-`d` reset shell. The former unbounded Cramer denominator is therefore return
precision in disguise. The parameter-digit, moving-frame, and higher-jet tower has been removed
from the live theorem bank.

[`R32-S27`](SALVAGE.md#r32-s27-rational-gap-macro-pumping) attacks that return precision
directly. On one common legal wait branch,

```text
vₚ(Sₐ(x)−Sₐ(y)) = vₚ(x−y)−sa.
```

A wait word subtracts the sum of these weights, and a perturbation deeper than the total weight
follows the same schedule. Thus a deep near-return to a rational checkpoint pumps bounded
repetitions of the same macro with exactly linear depth loss.

Primitive projective height supplies the opposing Archimedean bound:

```text
p^vₚ(x−y) ≤ 2H(x)H(y),       H(next) ≤ C H(current).
```

For a fixed macro `w` repeated `r` times from checkpoint `1`, either the first return is already
exact or

```text
p^((r−1)s·sum(w)) ≤ 2C^length(w).
```

Hence one fixed macro cannot store an unbounded counter through progressively deeper noncyclic
returns. Every surviving construction must move its checkpoint, change its macro, or use a
genuinely nonperiodic wait word. Conversely, a decision proof may finish by showing that every
sufficiently deep canonical return contains a powered macro violating the displayed gap.

[`R32-S28`](SALVAGE.md#r32-s28-terminal-endpoint-and-complementary-content) replaces the
discarded tangent branch with a fixed terminal gauge

```text
x=L(z−1)=A−L+D/w.
```

One wait acts by an explicit `2 × 2` divisor-Collatz transfer whose determinant is
`−DLp^(sa)(pᵃ−1)`. Primitive reduction splits the cyclotomic factor into forward content `h`
and complementary reverse content `k`; the adjugate reconstructs the source with scalar
`−k`. Across a complete terminal word, the first-row coefficient is exactly
`(−1)^N∏kᵢ`. The coefficient boundary yields immediate finite obstructions. In particular, a
prime dividing `A−L` but neither `D` nor `p` excludes every terminal word. This one-line test
subsumes both the former collision-ladder analysis and the more elaborate terminal proof for
the period-three survivor.

[`R32-S29`](SALVAGE.md#r32-s29-adelic-content-and-repeated-factor-budget) retains the forward
content without inventing another projective state:

```text
|hᵢ|Hᵢ₊₁ ≤ C Hᵢ,
p^((s−1)aᵢ)|hᵢ| ≤ C Hᵢ.
```

The entire factor of `pᵃ−1` coprime to `hᵢ`, including multiplicity, survives as a reset
congruence in the reduced target. Two trajectories through the same branch obey an exact
exterior-product law, and any repeated legal factor at arbitrary checkpoints is either an
exact cycle or its p-adic expansion is bounded by the two rational height envelopes.

[`R32-S30`](SALVAGE.md#r32-s30-fixed-cusp-and-record-ascent-calculus) gives the cumulative
recurrence its canonical global coordinate. The complete quotient

```text
Zᵢ = −DL Rᵢ₋₁/Rᵢ
```

obeys one generalized continued-fraction law with fixed forbidden cusp `Z=−L`; the wait is
exactly the approximation depth to the fixed ray `A Rᵢ=DL Rᵢ₋₁`. Terminal reverse content
divides the fixed boundary `L(A+D−L)`, but this does not bound the last wait: every positive
wait has an explicit terminal predecessor.

At critical depth two, consecutive nondecreasing waits satisfy the sharper local budget

```text
p^(a+b)|hh′| ≤
  (|D| + (1+|L|)(|A|+|L|)) H(R,β).
```

The intermediate height is eliminated, and the underlying decoder is an order-three core
followed by one wait-dependent shear. This is the exact record-ascent wall. It remains an
absolute estimate at a moving checkpoint: height accumulated before the ascent may already pay
the displayed power. The report's stronger fresh-cyclotomic-core claim was rejected because its
successive versions use incompatible loss exponents and omit the decisive valuation accounting.

[`R32-S31`](SALVAGE.md#r32-s31-smith-decoder-and-maximal-cancellation-throat) resolves the local
active-core allocation without adding state. Complementary contents split as

```text
h=ηu,    k=θv,    ηθ=DL,    uv=pᵃ−1,
```

and the associated endpoint decoder is unimodular. Every prescribed cyclotomic core not
absorbed by `h` passes to `k`, with multiplicity. In a fixed weighted norm, all branches with
`v≥2` contract uniformly after their natural `p^(2a)` scale; `v=1` is the unique
noncontracting branch and obeys an exact first-order recurrence. This is a real dichotomy, but
not yet a global contraction theorem: successive decoder coordinates use different wait
frames. The correct variable-wait transfer contains an explicit gauge between those frames.
The decoder now also has the checked continuant factorization

```text
C(q,u,v)=[[1,v],[0,1]][[0,1],[1,(q+1)u]],
```

which makes a continued-fraction bridge exact rather than analogical.
The submitted ungauged cocycle and its tropical path bound were algebraically false and have
been removed from the live branch.

[`R32-O07`](SALVAGE.md#r32-o07-parity-immortality-and-maximal-isolation) closes the maximal
throat as a global escape. The adjacent unit hypotheses force `p` odd. If
`R=A+D−L` is odd, every cumulative endpoint numerator stays odd and terminality is impossible.
If `R` is even, a maximal step satisfies the sharper cancellation

```text
r′=θt+(Dq²+A−L)t′.
```

Its target numerator is odd, and the next Smith coordinate `v`, when a next step exists, is
even. Maximal steps neither terminate nor occur consecutively. Eliminating the remaining Smith
ratios returns the existing guarded scalar state; it does not supply a second register capable
of repaying contraction.

[`R32-O08`](SALVAGE.md#r32-o08-recurrent-boundary-divisors-stay-reverse) kills the proposed
Jacobi prime-handoff shortcut. The exact denominator recurrence has coefficient
`A+Dqˢ−Lq′`, not `L(q′−1)`. More decisively, if a divisor `d` of reverse content `k` recurs in
the next boundary `L(q′−1)` and is coprime to `L(A+D−L)`, then `d` is coprime to the next
forward content and divides the next reverse content with full multiplicity. The token stays
reverse; it does not alternate into cancellation. Across intervening smaller waits its fate is
again a projective incidence problem already owned by the exact-order quotient automata. The
submitted normalized transfer, torsion rails, and global alternation argument are therefore
retired.

[`R32-O09`](SALVAGE.md#r32-o09-universal-boundary-reset-ball) adds a coefficient-level wall at
the universal boundary. At depth two, for any prime `ℓ`, write

```text
λL=vℓ(L),  λR=vℓ(A+D−L),  λD=vℓ(D),
e=vℓ(p−1),  ε=vℓ(2).
```

If `λR<λL+e` and `2λR<λD+e+min(λL,λR+ε)`, an explicit `ℓ`-adic ball around reset is
invariant under every positive endpoint branch and excludes terminal. In particular every prime
divisor of `p−1` must divide `A+D−L` in any mortal coefficient presentation. This kills the previous
period-three fixed ray as an entire physical law, not merely as a bounded orbit. Passing the
sieve supplies no height amortization: survivors may absorb the universal-boundary primes into
their fixed coefficients.

[`R32-O10`](SALVAGE.md#r32-o10-ready-order-breaking-bridge-ejection) closes the proposed first
order-breaking bridge as an independent local consumer. The even-resultant law

```text
p=3,   A=R=249398,   D=L=1
```

has a ready wait-four entry into the strict `5`-adic reset ball, followed by a ready wait-one
bridge back to its boundary. The bridge swallows no `5`-content, amplifies the primitive
denominator from `19` to `270178`, and leaves another ready wait. Thus neither ball invariance,
auxiliary-content loss, repetition, nor denominator descent can be charged uniformly to the
first bridge, even under one-step continued survival. A theorem over an unbounded bridge sequence
would still be a global amortization theorem and remains live only under that name.

[`R32-O11`](SALVAGE.md#r32-o11-terminal-only-pole-contraction-is-a-decision-oracle) rejects a
terminal-only fixed-frame contraction as a new intermediate theorem. The complete endpoint
product does admit the exact form

```text
M=[[εK,−εRK],[c,S−Rc]],    π=R−S/c,
```

and Smith reconstruction identifies the lower-left shear `c` as the fixed-frame channel which
can repay a local nonmaximal loss. For fixed coefficients, however, there is at most one
first-hit terminal execution. Existential constants in

```text
H(π)≤C p^T ρ^m
```

can therefore be chosen after that execution is known, or arbitrarily when it does not exist.
A uniform algorithm producing valid constants from the coefficients yields the desired terminal
length bound and is conversely computable from a guard decider. The formulation is equivalent in
effective content to guard decision unless an explicit coefficient formula is derived. Bare
rational approximation also stops at the sharp natural lower scale
`H(π)≥p^T/(1+|R|)`; any surviving estimate must use the semigroup recurrence to control `c`.

[`R32-O12`](SALVAGE.md#r32-o12-periodic-shadow-obstruction) kills coefficient-uniform descent
over all legal primitive corridors. The fixed guard

```text
p=3,   A=17,   D=−5,   L=16,   reset=3/4
```

has ready wait one at reset and fixes reset, yet admits legal off-reset corridors longer than
any prescribed bound. Every edge has wait one, exact forward content `−4`, and Smith coordinate
`v=2`. The carried prequotient pair and the actual primitive Smith quotient are primitive and
strictly increase along arbitrarily long runs of consecutive edge coordinates; the raw Smith
decoder output is exactly four times the displayed primitive quotient. The repeated Smith
transfer has audited all-place factor `10^j` on a `j`-step block. Thus neither bounded
positive-Smith height nor the corresponding all-legal adelic height can supply uniform descent,
even after the wait gauge becomes constant. The
construction is not reset-started and does not reach terminal. It moves the live obstruction
from local block geometry to the arithmetic depth with which the actual reset orbit may enter,
shadow, and leave a periodic ray.

[`R32-O13`](SALVAGE.md#r32-o13-renewal-graph-collapse-and-reset-pullback) closes the resulting
local renewal dichotomy. The exact common-branch similarity already proves that every nonempty
aligned macro consumes `s∑aᵢ` units of p-adic shadow depth, so a fixed positive-depth renewal
macro and every finite aligned ray cycle are impossible. A misaligned switch can exceed the
fixed ray-separation depth only on one threshold shell through leading-residue cancellation; it
has no iterable weight. Conversely, bounded depth does not give a local finite box. In the
fixed periodic-shadow guard, exact remaining carried-ray depth two and fixed wait, content, and
Smith label coexist with arbitrarily large endpoint and carried heights.

Reset ancestry is instead the exact integral law

```text
Δ(P₀,adj(M_u)V)=p^(s∑u)Δ(Pᶜ_u,V),
```

where the cumulative endpoint `Pᶜ_u` retains every primitive normalization scalar. This
identified the complete ancestral determinant but did not determine whether its radial direction
moved with the prefix.

[`R32-O14`](SALVAGE.md#r32-o14-fixed-reset-geodesic-and-complete-endpoint-language) closes that
ambiguity. For every nonempty positive endpoint word,

```text
M_u mod p = A^(|u|−1) [[A−L,(A−L)L],[1,L]],
```

so a normalized coefficient presentation has one fixed nonzero rank-one flag. More strongly,
for every actual cumulative prefix from reset, with `Ω=s∑u`, Lean proves

```text
ker(M_u mod p^Ω) = (ℤ/p^Ωℤ)·(A+D−L,1).
```

Reset ancestry therefore follows one fixed distinguished-prime geodesic; only its depth changes.
The moving datum in the pullback law is angular: the reference ray and the allocation of the
auxiliary factors of `p^a−1`, not the radial direction at `p`. At positive transverse depth,
primitive normalization removes no distinguished-prime power, so no hidden p-adic saving remains.

The same ratchet completes the endpoint language:

```text
EndpointTerminalWord(u) ↔ inverseAddress(u,terminalResidual)=1.
```

Positive endpoint terminal words are unique, and physical mortality is exactly the existence of
a nonempty one. Thus endpoint products create no malformed witnesses. The lawful guard
`(p,s,A,D,L)=(3,2,122753,−17,39232)` has unique positive terminal word `[1,1,1]`, excluding every
universal one- or two-return terminal bound. See
[`m32-fixed-geodesic-endpoint-completeness-2026-08-07.md`](audits/m32-fixed-geodesic-endpoint-completeness-2026-08-07.md).

The fixed-support counter branch is also closed. If finitely many rational canonical-tail
charts store counters in a fixed set of auxiliary-prime exponents and their waits depend
affinely on those exponents, every uniformly valid edge has constant waits. Laurent-monomial
charts then admit no nonconstant instruction, and arbitrary rational charts admit no repeatable
control cycle: the common rank-one reduction modulo `p` gives the cycle a projective eigenvalue
ratio of nonzero p-adic valuation, while every toric chart shift preserves the Gauss valuation.
Thus an aperiodic counter-orbit cannot be a stationary FRACTRAN-style prime register. It must use
continually moving cyclotomic support and retain history not rationally recoverable from a fixed
finite torus. See
[`R32-O15`](SALVAGE.md#r32-o15-fixed-support-toric-compiler-obstruction) and
[`m32-fixed-support-toric-obstruction-2026-08-08.md`](audits/m32-fixed-support-toric-obstruction-2026-08-08.md).

Endpoint/product-formula compactness has now been cut to its recurrence-sensitive core. A lawful
first-hit terminal word has primitive pole `(494,−41)`, and Lean checks that its primes `19` and
`41` are absent from every coefficient, reset, and branch-cyclotomic factor. Thus the angular
carry is not an `S`-unit on determinant support. Abstract endpoint data leave its shear free even
after all diagonal factors, Smith labels, valuations, and finite congruences are fixed; moreover,
the wait gauge has projective adelic height `p^(2|b−a|)`, not one. Any surviving decision proof
must use the actual additive continuant and its gcd with the radial factor. See
[`R32-O17`](SALVAGE.md#r32-o17-angular-emergent-primes-and-endpoint-compactness-no-go) and
[`m32-angular-emergent-primes-2026-08-08.md`](audits/m32-angular-emergent-primes-2026-08-08.md).

The actual continuant cuts this obstruction further. If `P` is the endpoint product before the
final branch, `X` is the terminal scalar, and `c` is the full lower-left coefficient, the final
lower row gives

```text
z c − X c⁻ = det P.
```

Thus `gcd(X,c)` divides only the earlier determinant support; the final branch creates no new
primitive normalization. More globally, every primitive exact-order factor whose order divides
all waits to the right is forced into forward content, while one whose order divides all waits
to the left is forced into reverse content. The global wait gcd is effectively finite, and the
terminal stratum `a₀∣a₁∣⋯∣aₙ₋₁` is decidable. The lawful word `[3,1]` shows the exact
residue: useful order must be broken on both chronological sides, allowing earlier reverse
content to finance later angular cancellation. See
[`R32-S33`](SALVAGE.md#r32-s33-terminal-casoratian-and-two-sided-order-allocation) and
[`m32-casoratian-order-allocation-2026-08-09.md`](audits/m32-casoratian-order-allocation-2026-08-09.md).

The moving-support ledger is now exact as well. For every divisor `d` coprime to `pDL`, one
primitive step satisfies

```text
d∣h ⇔ d∣r and d∣(pᵃ−1).
```

Thus an angularly emergent prime is inert until a later wait synchronizes with its
multiplicative order and the current endpoint numerator contains the same multiplicity. There
is no hidden prime register outside those two visible conditions. The reciprocal Euclidean
rewrite and Wronskian collapse to existing endpoint coordinates and `R32-S33`; rational
Mahler rails `a⁺=ka+d`, `k≥2`, were already excluded by the checked rail-degree theorem. See
[`R32-S34`](SALVAGE.md#r32-s34-exact-moving-prime-ledger) and
[`m32-moving-prime-ledger-2026-08-09.md`](audits/m32-moving-prime-ledger-2026-08-09.md).

The checked content-height law now has a global genealogy synthesis. In the endpoint-adapted norm
`Ψ(r,t)=max(|D||t|,|r−(A−L)t|)`, cumulative forward content and reduced denominator satisfy

```text
(∏_{n<N}|hₙ|)Ψ_N ≤ |D|Γᴺ,
Q_N∏_{n<N}|hₙ| ≤ |L|Γᴺ,
p^aⁿ∏_{j≤n}|hⱼ| ≤ Γⁿ⁺¹.
```

Thus fresh activated primes have count `O(N/log N)`; every activated packet on an aperiodic
orbit is microscopic relative to its current height and imposes a logarithmic recovery delay;
consecutive whole-numerator handoffs have bounded second wait. Formalization also continued the
proposed `(3,2,249398,1,1)` counterorbit beyond the reported prefix: its forced waits are
`[4,1,1,1,1]`, after which it reaches a nonterminal 3-adic unit and enters the trap. The surviving
construction is therefore not that tuple, nor any dense or macroscopic prime rail, but a sparse,
microscopic, doubly order-broken genealogy. See
[`R32-S29`](SALVAGE.md#r32-s29-adelic-content-and-repeated-factor-budget) and
[`m32-sparse-genealogy-budget-2026-08-10.md`](audits/m32-sparse-genealogy-budget-2026-08-10.md).

The counter lane now has an exact schedule-incidence formulation. For adjacent primitive
reductions, the native quotient `τᵢ=Ltᵢ/(hᵢtᵢ₊₁)` obeys

```text
qᵢ₊₁+qᵢ₊₁ˢ/τᵢ₊₁=A/L+(D/L)(qᵢˢ+(qᵢ−1)τᵢ).
```

Every prescribed positive wait schedule determines one compatible p-adic Jacobi tail, but it is
reset-started and rational only when one explicit continued fraction equals the rational reset
value. Adjacent handoffs must approximate `A/D` to growing p-adic precision and pay matching
Archimedean height. Finite handoff alphabets are eventually periodic, while readiness forces any
single fixed rational chart into the already excluded monomial rail. Thus a genuine aperiodic
counterorbit requires an infinite unbounded-height alphabet of history-dependent charts; choosing
an aperiodic wait substitution is not a construction. See
[`R32-S38`](SALVAGE.md#r32-s38-jacobi-schedule-incidence) and
[`m32-jacobi-schedule-incidence-2026-08-11.md`](audits/m32-jacobi-schedule-incidence-2026-08-11.md).

The remaining reverse reservoir cannot be charged by a function of the projective endpoints.
For the checked period-three guard, Lean now verifies exact primitive contents and a second
rational eigenline of the endpoint macro. Repeating the lawful cycle fixes the reset orbit while
placing exactly one new factor of thirteen per period in the transverse eigenvalue; the reset
eigenvalue remains coprime to thirteen. Thus endpoint-only all-packet amortization is false even
with fixed coefficients. The first-hit terminal and aperiodic hypotheses are now essential, not
technical residue. See [`R32-O20`](SALVAGE.md#r32-o20-transverse-reverse-reservoir) and
[`m32-transverse-reverse-reservoir-2026-08-10.md`](audits/m32-transverse-reverse-reservoir-2026-08-10.md).

First-hit terminality now supplies the missing nonzero boundary. Pulling reset backward through
the same address gives one canonical lawful companion ending at reset. Its projective cross with
the actual trajectory obeys an exact exterior recurrence that converts every actual reverse
content outside reset support into companion forward content. The uncancelled residue is one
angular gcd deficit `|RH|/|K̂|`; every moving prime surviving there is order-broken on both
chronological sides. This does not yet contract. A Lean-checked one-return family has
`|H|/|K̂|=(12n+1)/2`, unbounded even on a nonmaximal Smith step. Multiplication of local savings
is therefore false. Terminal-only bilateral amortization is also not a smaller live theorem:
the positive terminal language is singleton-or-empty, so pointwise constants are automatic and
a coefficient algorithm producing a terminal-length bound is already a guard decider. See
[`R32-S39`](SALVAGE.md#r32-s39-reset-companion-and-bilateral-shadow) and
[`m32-reset-companion-2026-08-11.md`](audits/m32-reset-companion-2026-08-11.md).

Finite rational carry-mode atlases cannot supply the opposing aperiodic orbit either. If each
mode is a rational function of the current `p^a` and each transition has one fixed additive wait
shift, every directed control cycle has total shift zero. On an actual infinite orbit the
recurrent shifts are therefore a coboundary, the waits are bounded, and determinism forces exact
eventual periodicity. A counterexample must carry unbounded angular history through infinitely
many effective charts or shifts, or through state not rationally recoverable from `p^a` and
finite control. See [`R32-O18`](SALVAGE.md#r32-o18-finite-rational-radial-atlas-obstruction).

The remaining unbounded channel is now sharply Archimedean. The formalized
[`R32-D03`](SALVAGE.md#r32-d03-bounded-denominator-periodicity) theorem says that every
infinite legal rational orbit with bounded reduced denominators is eventually periodic.
Its proof gives an explicit record-ascent ceiling and finite primitive-state box for every
supplied denominator bound and every depth at least two. Thus any genuinely nonperiodic
survivor must have unbounded reduced denominators.

The broad number-theory review
[`m32-number-theory-triangulation-2026-08-06.md`](audits/m32-number-theory-triangulation-2026-08-06.md)
now nominates two adjacent bridges rather than another local invariant. The first bridge has
since been resolved algebraically. For consecutive primitive reductions, put

```text
q=p^a,  Q=p^b,  Xᵢ=(tᵢ,hᵢtᵢ₊₁)ᵀ.
```

Existing prequotient coprimality makes `Xᵢ` primitive, and Lean now proves at every depth `s`

```text
Q^s hᵢ Xᵢ₊₁ =
  [[0,Q^s],[DL(q−1),A+Dq^s−LQ]] Xᵢ.
```

This removes the former mixed-endpoint state obstruction. It does not yet orient Panti descent:
`Xᵢ` is attached to an outgoing edge, its second entry has the sign of `hᵢ`, and the moving Smith
chart still divides by `uᵢ`. No checked identity makes the proposed positive two-decoder matrix
the live transfer of `Xᵢ`.

Capuano-Murru-Terracini's adelic continued-fraction criterion, extended by
Capuano-Checcoli-Mula-Terracini to a fixed set of extraneous denominator places, gives finiteness
under a strict all-place factor `ν<1` and finite-or-periodic behavior under `ν≤1`. The displayed
transfer projectivizes to a generalized continued fraction with variable partial numerator
`DL(q−1)/Q^s`, but the published scalar theorem does not directly cover it. `R32-O12` now shows
that no coefficient-uniform extension quantified over all legal guard corridors can provide the
required strict factor. Any use of this literature must exploit reset-started or terminal
history absent from the scalar recurrence alone.

The moving wait gauge is exact in one common basis:

```text
[[1,0],[1,1]] J(q,Q) [[1,0],[−1,1]] = diag(1,Q²/q²).
```

Its real growth and p-adic size are product-formula duals. This removes an irreducible shear from
the wait gauge, but not the global angular carry between endpoint-adapted flags; the dilation
still does not commute through the intervening cocycles. Every
nonmaximal Smith branch contributes a checked `3/4` real saving, while maximal branches are
isolated and nonterminal. Periodic shadows show that these local facts do not assemble into an
all-legal block inequality for the carried generalized continuant. See
[`m32-prequotient-adelic-2026-08-06.md`](audits/m32-prequotient-adelic-2026-08-06.md).

### Live attacks

| Lane | Required move | Present obstruction |
| --- | --- | --- |
| Split-guard decision | Produce an explicit coefficient recurrence-or-escape bound on a nonterminal class broad enough to contain every first-hit prefix | Terminal-only amortization is goal-equivalent; every residual packet is doubly order-broken and one wait can service nested packets |
| Split-guard counter | Solve the rational reset incidence for an aperiodic p-adic Jacobi schedule with sparse microscopic doubly order-broken packets | Finite handoff alphabets and fixed rational charts are periodic or impossible; the history-dependent handoff height must be unbounded |
| Irreducible cubic reflection orbit | Decide the recurrence-digit generalized-continuant endpoint language, or compile through its derived affine macros with an all-word converse | Ternary products can become triangular although every factor and adjacent pair is nontriangular; the endpoint witness still requires an uncontrolled seven-wait word |
| Generic projective incidence | Decide rational-subset membership in the rank-two affine cusp, or encode universality through its carry dynamics | Fixed-subset shortcut Collatz already occupies `ℤ[1/6]⋊ℤ²`; the Tits split, direct stores, and one-dilation algorithms miss it |

The split-spectrum hot path is an explicit reset-anchored recurrence-or-escape theorem on a
nonterminal class, opposed by a genuinely history-sensitive aperiodic
unbounded-denominator reset orbit solving one rational p-adic Jacobi incidence with sparse
microscopic activations. The matrix compiler,
arbitrary-word converse, deterministic wait decoder, rational inverse-address grammar,
primitive integral lift, endpoint factorization, exact branch similarity, arbitrary
repeated-factor pumping, local record-ascent budget, local content allocation, maximal-step
isolation, universal-boundary valuation wall, complete endpoint language, and fixed reset
geodesic are complete. Uniform first-bridge closure and coefficient-uniform all-legal block
descent are false; fixed positive renewal cycles are impossible; bounded local shadow depth does
not imply bounded height; terminal length can exceed two; endpoint support and finite rational
carry atlases are insufficient; reverse mass is invisible to projective endpoints on exact
cycles; even the reset companion need not contract at one nonmaximal step. The companion ledger
remains exact bookkeeping but terminal-only existential bounds are goal-equivalent. The
rank-`(3,2)` artery asks for an explicit coefficient formula valid before terminality is known,
or one exact aperiodic
reset orbit with unbounded denominators and unbounded history. The final boundary, persistent
exact orders, and divisibility-chain schedules are closed; only recycled support across
two-sided order breaks remains. In parallel, rank-(2,2) is exactly generic PI₂.

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

[`G3-O29`](SALVAGE.md#g3-o29-one-chart-projective-hard-core) identifies this exact node inside
the `M₃(4)` transverse campaign. The lifts `A↦diag(A,0)` and `B↦diag(B,0)`, together with identity
toggle and zero-extended endpoints, preserve every scalar coefficient after toggle erasure. For
invertible `A,B`, both lifts have rank exactly two and the same invariant image plane. Hence even
the one-chart projectively involutive line atlas is `M₂(3)`-hard. Multi-chart coherence may make
the general atlas richer, but it cannot make the full class easier than this subfamily.

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
  [`D2-D04`](SALVAGE.md#d2-d04-single-base-affine-stratum);
- prescribed translated-letter count:
  [`D2-D05`](SALVAGE.md#d2-d05-prescribed-translation-count);
- affine pairs with a private multiplier prime outside one endpoint shell:
  [`D2-D06`](SALVAGE.md#d2-d06-private-prime-peeling);
- bounded affine families with cooriented valuation vectors:
  [`D2-D07`](SALVAGE.md#d2-d07-bounded-valuation-orthants).

`D2-D01` and `D2-D05`–`D2-D07` have passed independent project audits. The invariant-pair,
common-multiplier, and single-base records remain reported research stock, not publication
theorems.

Simultaneous triangularization alone is not a solved stratum. It yields rational affine
reachability

```text
z ↦ a_i z+b_i,
```

whose general two-map case remains part of the wall. The provisional common-multiplier and
single-base theorems and the audited valuation strata cover substantial subfamilies but do not
settle every mixed multiplicative direction.

### Exact unresolved residue

Two qualitatively different classes remain after the preceding tests.

#### Mixed-prime affine systems

These have a common rational fixed point but genuinely independent multiplier valuations.
After affine normalization, every non-elementary pair has the form

```text
F(z)=az,      G(z)=bz+1.
```

Its words obey the monotone exponent-path theorem
[`D2-S02`](SALVAGE.md#d2-s02-monotone-affine-path-form). A prescribed number of `G` letters is
decidable by rational-base carries, and a private prime often determines that number directly.
Bounded cooriented valuation families are finite-state even when their slopes are
multiplicatively independent.

The benchmark

```text
z ↦ (2/3)z+1,       z ↦ (3/5)z+1
```

is therefore no longer wholly opaque. It is conjugate to

```text
F(z)=(2/3)z,      G(z)=(3/5)z+1.
```

Private-prime tests decide every endpoint pair outside

```text
v₅(3−x)=0,      v₂(6y−15)=0.
```

Inside that shell, every maximal shell-preserving prefix is governed by

```text
T_m(u)=(1+3u(2/3)^m)/5,
v₅(u)=v₅(T_m(u))=0.
```

The multiplier-prime skeleton is now exact. Below the `2`-adic wall,
`v₂(T_m(u))=v₂(u)+m`; below the `3`-adic wall,
`v₃(T_m(u))=v₃(u)+1−m`; above either wall the corresponding output is a unit. Thus any output
that is a unit at both primes forces the finite interval
`−v₂(u)≤m≤v₃(u)+1`. If both transported valuations are negative, their sum rises by one
independently of `m`. This is `D2-S03`. It localizes all unbounded behavior to mixed-sign chamber
crossings and equality-wall cancellation, but does not yet bound how often a successful history
can use them.

The local shell is now known to be maximally recurrent. Every nonempty finite wait schedule has
an exact rational periodic orbit entirely in the unit shell; period-one rational fixed points
are dense in both admissible `5`-adic cylinders. Every admissible source and unit target at
finite `5`-adic precision are joined by one wait residue. Recursively lifting those residues
gives every admissible rational source aperiodic all-unit addresses with arbitrarily large waits.
Yet the single-wait graph on period-one nodes has only its loops and the exceptional edge
`T₂(x₀)=x₁`. The varying-schedule valuation topology inside negative `3`-adic depth is now exact.
For rational `3`-unit carrier `c`, the state `u=c/3^d` obeys

```text
d'=d+m−1,      c'=(2^m c+3^d')/5.
```

The only exit is `d=1,m=0`; a target at depth `d'` has a complete, pairwise-distinct fan of
`d'+1` debt predecessors. A `5`-unit target carrier makes the whole fan shell-legal. Arbitrary
uninterrupted schedules are Łukasiewicz bridges with
`d_end+length=d_start+sum(waits)`. At fixed endpoint depths and length their affine slope is
fixed, so a point collision is already a global affine-map relation. The remaining
source-specific collision problem is cross-length, together with chamber exits and reentries.
That cross-length seam now has an exact normal form: two nonempty unequal-length schedules have
one collision source, and it is automatically a `5`-adic unit because both slope and intercept
have valuation `−length`. Thus source-shell exclusion supplies no length bound. The common target
is a unit exactly when the affine determinant `a_left b_right−a_right b_left` has valuation
`−max(left.length,right.length)`; this exact shorter-length cancellation remains live. Exact
adjacent-length bridges sharpen it: common debt endpoints force slope ratio `2/5`, and with
`C_w=5^|w|b_w`, target acceptance is equivalent to
`v₅(C_long−2C_short)=|short|`. The suffix recurrence for `C_w` is explicit but still unbounded.
The debt-safe collision `[4]` versus `[0,5]` at `2/9↦55/243` overcancels and rejects the target,
so source unitality alone does not imply acceptance. Exact unit-target examples realize both
possible `3`-adic carrier orientations, killing that one-bit invariant as a global separator.
Conversely, fixed-source equality itself has an exact infinite saturation family: for every
`m≥0`, `[1,m+2]` and `[3,1,m]` are adjacent debt bridges from depth one to `m+2` and collide from
`43/24`; every `m=10k` member is accepted. Their targets are pairwise distinct, so this kills a
fixed-source wait bound but cannot pump one target and does not settle the fixed-target
quantifier. Every target nevertheless lies on the complementary endpoint pole
`v₂(1−2u)=0`. Within this ray the fixed-target query is decidable by testing the sole candidate
`m=max(0,v₂((45y−9)/11))`; the unresolved quantifier is intersection of the full reachable set,
not this family. This is [`D2-O03`](SALVAGE.md#d2-o03-fixed-source-adjacent-saturation).
The first exit extension is also exact. Every next wait from the accepted `m=10k` subfamily
leaves the shell at valuation `−1`, and every later block lowers that valuation once more. The
two-parameter exit surface has displacement
`75E(k,r)−15=(2/3)^r(9+11(2/3)^(10k))`; it is injective, and fixed-target membership reduces to
two valuation-derived equality tests. Thus neither the ray nor its first exit block has an
infinite fixed-target fibre. Target valuation also fixes the length of every later suffix. The
resulting full schedules have one fixed translated-letter count and regular wait control, so
`D2-D05` decides the entire continuation cone. This is
[`D2-O04`](SALVAGE.md#d2-o04-forced-exit-surface).
The suffix collapse is universal. Any step leaving a `5`-adic unit is zero, has valuation `−1`,
or has positive valuation. Zero and positive exits enter valuation `−1` after one further block;
negative valuations then fall once per block. A nonempty suffix to a fixed target therefore has
one of two consecutive target-derived lengths. By `D2-D05`, every fixed exit has a decidable
suffix. The sole infinite seam is the fixed-source set of shell-preserving prefixes and their
first-exit images, not the schedule after an exit. This is
[`D2-O07`](SALVAGE.md#d2-o07-universal-exit-suffix-collapse).
Real order removes both exterior target components. Every shell block preserves
`[1/5,1/2]`; a trajectory ending above `1/2` or below `1/5` is dominated by the all-zero-wait
trajectory, whose distance from `1/2` contracts by `(3/5)^n`. Lean converts this into an explicit
computable block-count bound, and `D2-D05` decides every smaller count. The variable-schedule
real survivor is therefore exactly the closed target interval `[1/5,1/2]`. This is
[`D2-D10`](SALVAGE.md#d2-d10-real-trap-exterior).
The guarded part of that interval is backward-saturated. Every rational `5`-adic unit target
`y∈(1/5,1/2]` has a rational unit predecessor in the same interval, and iteration supplies a
guarded predecessor schedule of every prescribed block length. The source varies with the
length. Thus target position, target unitality, and real contraction cannot bound the remaining
translated count; only the simultaneous fixed-source/fixed-target arithmetic can discriminate.
This is [`D2-O08`](SALVAGE.md#d2-o08-real-trap-backward-saturation).
Real order nevertheless cuts the local reverse fan. For each `y∈(1/5,1/2]`, one computable
exponent `c(y)` brackets `(10/3)(y−1/5)` between consecutive powers of `2/3`. Every predecessor
inside the trap has wait `c(y)`, `c(y)−1`, or `c(y)−2`, and fixed-source one-step reachability is
exactly three rational equality tests. The width is sharp at `y=49/150`. Thus the surviving
backward graph is an explicit ternary tree: unbounded depth, not unbounded local fanout, is now
the reverse-search obstruction. This is
[`D2-S04`](SALVAGE.md#d2-s04-real-trap-ternary-predecessor-nucleus).
The source-side dual is sharper. Every `x∈(1/5,1/2]` lies in one of three intervals, and its
entire one-step orbit is one normalized-mantissa ray:
`U(m,2x)`, `U(m+1,3x)`, or `U(m+2,(9/2)x)`. Once the target depth is computed, fixed-source
one-step reachability is one equality rather than three. This is
[`D2-S05`](SALVAGE.md#d2-s05-fixed-source-real-trap-rays). Independently, every reduced-
denominator exponent away from `2`, `3`, and `5` is invariant through all shell schedules,
including first exits. Endpoint pairs with different prime-to-30 denominator skeletons are
therefore excluded before the active-prime search. This is
[`D2-S06`](SALVAGE.md#d2-s06-spectator-prime-denominator-skeleton).
The remaining local `5`-adic guard is finite: from any fixed unit source, one-step acceptance
depends only on the wait modulo ten. Together with `D2-S05`, every guarded one-step orbit is one
mantissa ray with ten tested depth classes. A fixed tail of length `ℓ` raises the sufficient
period to `2·5^(ℓ+1)`, and unit zero preimages prove the exponent sharp: changing by `2·5^ℓ`
can flip zero to a unit. More strongly, for every `M>0`, congruent waits `m` and `m+2M` have
opposite guard outcomes at a unit zero preimage with tail length `v₅(M)`. Fixed-modulus all-depth
compression is therefore dead. This is
[`D2-S07`](SALVAGE.md#d2-s07-period-ten-shell-guard).
For the fixed-unit-target problem this growing guard precision disappears: final unitality is
already equivalent to every intermediate shell guard. More importantly, normalized target depth
collapses. The exact identity
`T_(m+k)(x)=U(d+k,μ) ↔ T_m(x)=U(d,μ)` lets the final wait absorb every depth shift. For `d≥2`,
the sharp three-wait window also makes the shift reversible, so the nonempty predecessor set is
independent of target depth. Unit acceptance has period ten along the ray. Every guarded
fixed-source query therefore reduces to depths `0`, `1`, or one of `2,…,11`, with the exact
rational mantissa left untouched. The live reverse tree is an unbounded mantissa address, not an
unbounded target-depth counter. This is
[`D2-S08`](SALVAGE.md#d2-s08-twelve-class-target-depth-collapse).
The exact mantissa address has three interval-separated reverse candidates: `μ/2`, `μ/3`, and,
above `μ=9/10`, `2μ/9`. Only the last branch resets to unbounded depth. For reduced unit
`μ=a/b`, its centered numerator is `N=10a−9b`, and Lean proves
`gcd(N,b)=gcd(2,b)`. The odd-denominator and four-divisible-denominator updates are rigid. Every
remaining cancellation lies on the single wall `b=2c`, where
`v₂(ν)=v₂(5a−9c)−(n−1)` at predecessor depth `n`; the three-adic update is exact as well. This
is [`D2-S09`](SALVAGE.md#d2-s09-centered-lower-mantissa-recurrence). Exact high-cancellation
orbits exist. For every `d≥7`, the reduced mantissa
`μ_d=3^(d−1)/(10·3^(d−3)−2^(d−1))` lies above `9/10`, has denominator two-adic value one,
and gives a guarded fixed state `T_(d−2)(U(d,μ_d))=U(d,μ_d)`. Its centered residual has
two-adic value `d−2`; arbitrary repetitions remain accepted. Global height, odd-part, and
centered-valuation descent are therefore dead. This identifies the abstract singleton cycles of
`D2-O02` exactly on the `D2-S09` secondary wall. That wall now has a finite target-dependent
nucleus. If a reduced unit transition `a/(2c)→a'/(2c')` stays on the wall, Lean proves
`c=3^k c'` for a bounded exponent. Hence every successor lies in the finite rectangle
`a'≤2c`, `c'≤c`; its witness depth is the computable value `v₂(5a−9c)+2`, the transition is
functional, and every infinite consecutive wall orbit is eventually periodic. The explicit fixed
family is recognized as terminal singleton components. Pairing
the rectangle with the `D2-S08` representative gives a finite coordinate-by-twelve-depth product.
This is [`D2-S10`](SALVAGE.md#d2-s10-finite-secondary-wall-nucleus). The live arithmetic
obstruction is no longer internal wall recurrence, but excursions through upper or middle
branches or rigid two-adic strata and their later returns.
The rigid stratum is now closed. Exact upper, middle, and lower valuation formulas show that any
reduced denominator divisible by four remains divisible by four under every reverse branch. A
lower-wall under-cancellation enters this absorbing cone and cannot return; exact wall
cancellation remains in the finite `D2-S10` nucleus. This is
[`D2-S11`](SALVAGE.md#d2-s11-absorbing-four-divisible-cone). Only wall-preserving upper steps and
lower over-cancellation into an odd denominator can participate in a recurrent excursion.
Those odd exits are genuinely recurrent. For every `n≥7`, `2≤m≤6`, and also exactly the
boundary pairs `n=6`, `4≤m≤6`, an explicit reduced five-adic-unit pair closes a guarded
two-cycle with waits `[n−1,m−2]`. For each depth pair it is the unique solution of the
lower/middle cycle equations. At fixed `m` the wall mantissas for `n≥7` form a
strict infinite sequence converging to `9/10`, while the corresponding lower-depth states
converge to the excluded endpoint `1/5`. This is
[`D2-S12`](SALVAGE.md#d2-s12-exact-wall-odd-two-cycle-family). The finite literal SCC census of
`D2-S10` cannot extend across excursions; the live target is a symbolic classifier for these
two-cycles and every longer odd return, not another finite valuation box.
The longer upper-run branch is now explicit. For every `n≥7`, `2≤m≤6`, and `r≥0`, the itinerary
`L_n,U₀^r,U₁,M_m` closes a guarded primitive cycle of exact period `r+3`, with every intermediate
mantissa, branch interval, two-adic phase, and five-adic prefix guard checked. In particular the
real trap has primitive cycles of every period at least three. This is
[`D2-S13`](SALVAGE.md#d2-s13-guarded-upper-run-cycles-of-every-period). Literal period bounds and
finite cycle lists are therefore dead; the family must be collapsed symbolically or coupled to
a fixed endpoint.
In fact the schedule word itself has no restrictive local grammar. For arbitrary finite `E`,
every wrapped word `[a]++E++[c]` with `c≥7` has a guarded periodic source `x∈(1/5,2/9]` whose
mantissa `9x/2` lies exactly on the reduced unit wall; the first step is its lower predecessor.
Thus every finite wait word occurs as a middle factor of a wall-anchored periodic excursion.
This is [`D2-S14`](SALVAGE.md#d2-s14-arbitrary-body-wall-excursion-saturation). It kills local
forbidden-factor and bounded-excursion grammars, though not regularity: the endpoints vary with
the body. The remaining seam is necessarily endpoint-coupled.
For periodic endpoint fibres, that coupling has an exact algebraic owner. Two nonempty schedules
have the same periodic source exactly when their global affine actions commute. Their slopes are
equal exactly when both length and total wait agree. The equal-slope branch is therefore the
existing balanced affine kernel; every unequal-slope branch is the single explicit equation
`collisionSource(u,v)=shellPeriodicPoint(u)`. This is
[`D2-S15`](SALVAGE.md#d2-s15-fixed-endpoint-centralizer-reduction). It replaces a separate
periodic-state census by a positive-centralizer problem, but does not yet decide that
centralizer or general unequal-endpoint reachability.
That centralizer has a sharp determinant fork. Two common-point schedules whose `(length,sum)`
vectors are dependent force an explicit global equality between fixed powers. Independent
vectors generate an injective `ℕ²` family of pairwise distinct guarded loops at the same rational
source. This is [`D2-S16`](SALVAGE.md#d2-s16-periodic-centralizer-determinant-fork). Hence a
genuinely noncyclic centralizer cannot be sporadic: one witness saturates the fixed source in two
parameters. The live centralizer question is whether this independent branch exists at all.
The same slope split applies without periodicity. For any fixed rational source, two schedules
have the same output exactly when they are either equal-length/equal-sum representatives of one
global affine-kernel class, or have different slopes and the source equals their explicit unique
collision source. This is [`D2-S17`](SALVAGE.md#d2-s17-fixed-endpoint-fibre-dichotomy). Thus the
general fixed-endpoint search may quotient the balanced kernel grade by grade and send every
cross-grade pair to one source equation before considering the target.
For the same-length cross-grade branch, source acceptance is now one exact carry. If
`Δ=|sum(u)−sum(v)|`, the slope difference has five-adic value `κ(Δ)−length`, where `κ` is zero
for odd `Δ` and `1+v₅(Δ/2)` for even `Δ`. The collision source is a unit exactly when the
intercept difference has that value. This is
[`D2-S18`](SALVAGE.md#d2-s18-same-length-cross-grade-five-carry). Target acceptance is equally
exact: the common target, and equivalently every prefix on both colliding schedules, is a
five-unit exactly when the affine determinant has value `κ(Δ)−length`. This is
[`D2-S19`](SALVAGE.md#d2-s19-same-length-collision-acceptance-certificate). The remaining
same-length task is to solve the fixed-source intercept equation together with this determinant
carry, not to inspect intermediate guards.
That equation now has a global monotone cut. Order equal-length schedules by all aligned suffix
sums. For every positive source the shell endpoint is strictly antitone in this order, so every
nontrivial endpoint fibre is an antichain; equivalently, the suffix-sum difference of any
colliding pair must take both signs. This is
[`D2-S20`](SALVAGE.md#d2-s20-positive-endpoint-suffix-antichain). The live same-length search may
discard every one-sided cumulative-wait walk before computing the fixed-source equation or the
`D2-S19` determinant carry.
That carry now has an exact denominator-free owner. If `H` is the determinant of the cleared
gain-offset vectors, then target acceptance is `v₅(H)=length+κ(Δ)`. A common initial wait
multiplies `H` by a five-power times a unit and advances the collision source by the same shell
step; a common terminal wait strips from endpoint equality by injectivity and leaves the
collision source fixed. This is
[`D2-S21`](SALVAGE.md#d2-s21-affine-determinant-carry-stripping). The live crossing-walk search
therefore starts only from pairs with different initial and terminal waits; terminal extension
still has an inhomogeneous determinant carry and remains part of the hard core.
The carry is now termwise. The cleared determinant is a weighted sum of prefix-gain gaps whose
nonzero term at index `i` has exact value `i−1+κ(Pᵢ)`. Accepted collisions cannot have a unique
lowest term. If `j` is the first nonzero prefix gap, some `i>j` must satisfy
`i−j+κ(Pᵢ)≤κ(Pⱼ)`. Hence `Pⱼ` is even; when `κ(Pⱼ)=1`, the next prefix gap exists and is odd.
This is [`D2-S22`](SALVAGE.md#d2-s22-prefix-carry-minimum-classifier). It leaves only
higher-depth tied-minimum trees coupled to the exact weighted suffix source equation and its
cleared real-trap corridor. Two exact
length-two pairs with the same signed suffix-gap walk and source have opposite target-acceptance
outcomes, so no suffix-gap-only quotient can decide the residue.
Length two is now closed as a separate seam. Every positive cross-grade pair has, up to swap,
the form `[c+k+Δ,b]` against `[c,b+k]`. Source acceptance is `κ(k)=κ(Δ)`; target acceptance
forces `κ(k+Δ)=κ(Δ)+1`. The exact tail transition has value `κ(s)−1` under a positive shift
`s`, so target acceptance depends only on `b mod 10` and accepted gauges share one parity. The
real trap forces `k≤2`; the carry equations then give exactly the `k=1` odd gaps excluding
`9 mod 10`, or the `k=2` gaps equal to `8 mod 10` excluding `48 mod 50`. Target acceptance is
respectively periodic in `Δ mod 50` or `Δ mod 250`. For fixed gaps the real-trap condition
is exact: `k=1` leaves `c=0` at gap one, `c≤1` at gap three, and `c∈{1,2}` thereafter;
`k=2` leaves only `c=0`. Lean exhausts both finite target rectangles: each contains exactly
forty accepted `(Δ,b)` residue pairs. The fully guarded length-two parameter language is an
explicit finite union of affine congruence families. This is
[`D2-S23`](SALVAGE.md#d2-s23-length-two-mixed-sign-classifier). The live carry-tree search
therefore begins at length three, where three or more prefix terms can share the lowest height.
The deepest of those three branches is itself a full depth reset. In normalized band coordinates
`U(d,μ)=1/5+(3/10)(2/3)^dμ`, every target band `d≥2` contains a point whose `d−2` predecessor has
any prescribed band `n≥7` and mantissa in `(2/3,1]`. An explicit guarded subfamily fixes target
depth four and wait two while the source depths run through `50k+50`; exact residues modulo 125
prove that both endpoints remain `5`-adic units. Both are also `2`-adic units, while their exact
`3`-adic depths are `50k+49` and `50k+50`. The targets are pairwise distinct. Therefore fixed
real depth plus finitely many valuation modes cannot form an inverse nucleus, but this ray still
does not create a fixed-target fibre. Moreover `T_(50k+48)(2/9)=U(50k+50,1)`: one fixed unit
source inside the real trap feeds the ray at unbounded waits, again with distinct targets. Exact
mantissa arithmetic is indispensable. This is
[`D2-O09`](SALVAGE.md#d2-o09-guarded-real-pole-reset).
Higher depth is not free: a published length-thirteen relation yields two distinct
schedules with the same affine map and a common Lean-checked guarded periodic source. This is an
exact rewrite seed. Lean also proves that it preserves all intermediate shell guards in every
word context. Lean now factors every boundary-shifted schedule equality as one raw `D,T` context
and checks the published length-27 relation, an infinite family at every odd length `29+2k`, and
three independent length-30 relations. Every odd-family relation has an exact shell schedule
factorization, preserves every intermediate unit guard in arbitrary context, and has a common
rational all-unit cycle. Exact homogeneous products show that the family remains nonfree after
every independent nonzero scaling used by unit normalization. Its `k=0,1` instances force every
later member after group cancellation, but not in the raw positive congruence; the schema
preserves length and letter content and yields no reachability bound. Lexical orientation of the
original five-rule basis
terminates, but has 45 nonjoinable critical overlaps. Exhaustive affine census proves bounded
completeness through raw length 30 and finds seven independent collisions at length 31; one is
now the formal `k=1` family member and six remain computational. There is no
complete-presentation claim. Thus state-independent unlabeled bounded-residue
nonexistence pruning, eventual exit or periodicity, shell-wide strict drift, and a single-wait
period-one compiler are closed. The surviving issue is exact target and accepting-exit
reachability from a specified rational source. See
[`D2-O02`](SALVAGE.md#d2-o02-critical-shell-periodic-saturation).

The exact scope and the remaining infinite-exit seam are
[`D2-M01`](SALVAGE.md#d2-m01-benchmark-critical-shell). The general affine residue still
includes pairs with no private prime, no bounded invariant interval, and incompatible valuation
signs.

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

The singular-triangle `M₃(4)` stream lands on an adjacent group-orbit shell, not on normalized
two-positive GPI₂. `PositiveFreeCancellation.triangleCarrier_dichotomy_rat` compresses every
singular saturated triangle carrier to invertible projective action on a rational plane. Its
three positive controls satisfy `[C]=[B]⁻¹[A]⁻¹`, so they generate the two-generator group
`Γ=⟨[A],[B]⟩` as a positive monoid. The exact promise is `|Γ∩g₀B_p|≤1`; conditional on a hit, the
stabilizer is trivial and the orbit is free. Eliminating `C` would require replacing an inverse by
a positive `{A,B}` word and is not generally lawful. This is the positive-vs-inverse seam between
[`G3-O23`](SALVAGE.md#g3-o23-singular-triangle-carrier-collapse) and the present two-positive
artery; see
[`m34-singular-triangle-collapse-2026-08-30.md`](audits/m34-singular-triangle-collapse-2026-08-30.md).

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
| Separate the Collatz cusp by finite ambient quotients | every finite image identifies the positive monoid with the whole generated group |
| Assume the mixed-prime schedule action is free | a published length-thirteen relation is a checked guarded collision |
| Bound the mixed-prime reverse fan by valuations alone | a target at negative `3`-depth `d` has exactly `d+1` distinct shell-legal predecessors when its rational carrier is a `3`- and `5`-unit; `D2-S04` recovers a sharp ternary bound only after intersecting both endpoints with the real trap |
| Prune cross-length shell collisions at their source | every two nonempty unequal-length shell maps have a unique collision source and it is automatically a `5`-adic unit; only fixed-source equality and target acceptance remain discriminating |
| Infer target acceptance from the automatic cross-length source unit | the adjacent debt-safe bridges `[4]` and `[0,5]` collide from the `5`-unit source `2/9`, but their target `55/243` has `5`-adic valuation one |
| Bound accepted waits from one fixed source | for every `k≥0`, `[1,10k+2]` and `[3,1,10k]` are accepted adjacent bridges from `43/24`; inside the real trap itself, `T_(50k+48)(2/9)=U(50k+50,1)` is an accepted one-step family |
| Use real contraction to bound every shell schedule | the common invariant interval `[1/5,1/2]` is the exact recurrent real survivor; zero-wait extremality bounds only exterior targets |
| Bound the translated count from a target inside the real trap | every rational `5`-adic unit target there has guarded rational predecessor schedules of every prescribed length, with varying source |
| Bound the next real-trap depth from the current depth and unit status | the guarded pole-reset family has fixed target depth four and fixed wait two but source depths `50k+50` |
| Invoke a general module `S`-unit algorithm | the arbitrary three-prime case leads to open linear-exponential systems, and forgetting the monotone path destroys useful structure |

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
| Syntax-sensitive automatic structures and positive rational languages | 5% | 5% decidable |
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
regular language. The canonical synchronous version is now excluded:
[`D2-O01`](SALVAGE.md#d2-o01-canonical-collatz-reachability-is-not-automatic) imports
Dhiman--Pandey's theorem that, whenever odd `q,d` satisfy `q+d=2^s`, the full reachability
relation of `n↦n/2` or `(qn+d)/2` is not recognizable by a finite base-`q` automaton. This
includes classical shortcut Collatz. It does not exclude a fixed-target slice, a redundant or
annotated encoding, an asynchronous transducer, a counter model, or a general algorithm.

For the affine benchmark, the first target is narrower: decide whether the guarded maps

```text
T_m(u)=(1+3u(2/3)^m)/5
```

have a finite synchronized representation that couples the base-`5` carry to the `2`- and
`3`-exponents and recognizes accepting shell exits. `D2-O02` proves that a bounded
unlabeled residue-transition graph alone is maximally nondiscriminating. The odd-length family is
now exact and collapses to two seeds only in the cancellative envelope; unit normalization does
not remove it. The next algebraic experiment is to derive even-length families from the three
checked length-30 relations and the six residual computational length-31 classes, classifying
separately their group closure and their uncancelled positive congruence. The current finite
Knuth–Bendix basis terminates but is nonconfluent and already incomplete at the next length. Run
fixed-source point collisions, exit-fibre, and carry-state growth with total `2`- and
`3`-exponents in parallel. For
the non-elementary residue, compare reachable carry-state growth for ordinary continued
fractions, slow continued fractions, Stern–Brocot paths, and redundant multi-prime expansions.
Any claimed finite nucleus must state the annotation or restriction that avoids the full
canonical reachability relation proved nonautomatic by `D2-O01`.

#### 3. Characteristic-zero affine modules

For triangular systems, express the translation component as a module element over the
multiplicative slope group. The target theorem is decidability of cyclic-coset reachability in
a rank-one characteristic-zero module-by-abelian group generated by two affine maps. Minimal
`S`-unit relations, Laurent-module normal forms, or effective semilinearity are the likely
invariants.

The unresolved critical shell of the `(2/3,3/5)` pair is the benchmark. Generic endpoints are
already peeled by `D2-D06`; a method that cannot decide the shell has not crossed the affine
residue.

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

[`D2-D09`](SALVAGE.md#d2-d09-step-three-shear-height-decision) is the exact positive seed. For
the fixed step-three shear orbit of `[1:1]`, alternating coordinate dominance makes every reduced
syllable double primitive pair height and bounds every exponent by the target height. Generalize
the chamber/height pair only after handling [`D2-O05`](SALVAGE.md#d2-o05-promised-empty-free-orbit-inverse-cycle):
a diagonal `S`-unit and transverse parabolic admit a positive target stabilizer whose deterministic
inverse stripping cycles through primitive heights `5→3→5`. A viable state must detect and
quotient such cycles or add a secondary well-founded invariant. `D2-O06` proves that bounded
recurrence along distinct normal-form prefixes always comes from a target stabilizer. After that
stabilizer component is removed, `D2-O10`–`D2-O13` give the exact survivor: a proper
height-escaping path with at most `(2H+1)²` visits below each ceiling `H`, but without a computable
last-return index. `D2-O14` realizes such a proper false ray explicitly under unguided inverse
search. Raw word length alone is not a lawful height: relations can make long words represent
short group elements.

#### 6. Exact symbolic saturation and finite obstructions

Run backward saturation from the target using cones, valuation vectors, residue classes, and
affine lattices. A successful well-structured formulation must decide exact reachability, not
only coverability. `G3-O28` closes finite ambient-group separation for `UCB₂(S)`: one promised
empty coset survives every finite quotient of its natural `S`-arithmetic ambient group. Finite
residues may remain components of an infinite annotated state, but cannot be the complete
negative certificate. `D2-D09` decides that explicit family by an unbounded Archimedean height;
it is the model for the annotation that finite saturation was missing. `D2-O05` adds the first
required transition type for any general saturation: a chamber-directed inverse component may
be periodic even when the target coset is empty, so recurrent stabilizer components must be
recognized rather than mistaken for failed descent. `D2-O06` proves that this accounts for every
bounded-height recurrence with distinct normal-form prefixes; saturation beyond the stabilizer
quotient must confront unbounded primitive height.

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
- Finite-modulus no-certificates are insufficient on both the positive orbit and unique-coset
  arteries by `R32-O22/G3-O28`.
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

1. Attack the two surviving `M₄(3)` nodes: an all-word classification of arbitrary consecutive
   wall incidences under `M4-S04` and `M4-S06`, and a syntax-sensitive compiler or strictly
   narrower universal source image that excludes `M4-O15` pseudo-terminals. The exhaustive
   positive overlap-queue source class, alternating/multiple residue-two defect grammar, retuned
   fixed-row closure, and `M4-C04` endpoint architecture are closed. Cross-pollinate exact
   exterior invariants only within their contragredient representation; do not transplant them
   to primal endpoint actions or revive deletion scanners, complete-token queues, fixed-ray
   complete-block semantics, one-coordinate dynamics, finite wall-separated cones, or literal
   Neary recodings.
2. Use formalized `MM-O01`, `G3-O01`, `MM-O03`, and `MM-O04` to reject exact packings, macros,
   and bridges without conflating their scope with solvability preservation.
3. Prove or refute the setter candidate's projective avoidance property, construct a
   five-state same-zero binary root, or find a constant-state scheduled delimiter fusion.
   Treat fixed-width-three universality as a separate source theorem and enforce the
   [`MM-D01`](SALVAGE.md#mm-d01-sparse-width-three-source-decision) one-`c` closure and
   [`MM-D02`](SALVAGE.md#mm-d02-adjacent-two-c-source-decision) adjacent-two-`c` closure on
   candidate source families. Reopen `MM-C04` only for a physically different six-state family.
4. Run the `M₃(4)` program on distinct tracks: history-sensitive paired point-line synthesis,
   projective group-orbit separation for the exponent-one singleton, global word-residual
   recoding, and native three-schema rewriting. `G3-O23` has absorbed the singular saturated
   Carvalho branch into dimension two, and `G3-O28` has killed every finite quotient of one
   natural `S`-arithmetic ambient group there. `D2-D09` decides that fixed shear family by height;
   `D2-O05` forbids universalizing primitive height without recurrent-cycle state, while `D2-O06`
   identifies every bounded injective-prefix recurrence with a target stabilizer. `D2-O10`–`D2-O13`
   turn that branch into a finite certificate and prove that every trivial-stabilizer survivor tends
   to infinite primitive height. `D2-O14` proves that an irrelevant inverse ray can satisfy that
   properness exactly. Seek a chamber-complete or place-sensitive escape law rather than retaining
   either example as a hardness candidate.
   Do not revive singular spelling memory, conflate group inverses with positive `M₂(3)` controls,
   or retry finite ambient-group separation as a complete certificate.
5. Formalize `D2-S02` and `D2-D05`–`D2-D07`, use `D2-D10` to remove real exterior targets, then
   attack fixed-source exact prefix and first-exit-image reachability inside `[1/5,1/2]` with a
   synchronized `2`/`3`/`5` representation. Use the checked `D2-S03` walls to isolate mixed-sign
   debt transfer and equality-wall cancellation; a chamber argument that never handles those
   transitions is incomplete. Inside uninterrupted negative `3`-depth, restrict source-specific
   point-collision search to cross-length bridges: fixed-length collisions are already global
   affine relations by `D2-O02`. The forced-exit records remove the post-exit schedule from the
   infinite seam, so treat chamber exit and reentry as separate pre-exit seams. In parallel, seek
   a parametric affine-kernel description beyond the checked length-30 basis and run normalized
   collision/exit-fibre census. Do not reopen unlabeled residue-only finite nuclei, uniformly
   valuation-only reverse bounds, one-sided endpoint bounds, or global real drift inside the
   invariant trap. `D2-O08` already saturates target-only reverse length there when the source may
   vary, while `D2-S04` replaces its local reverse fan by a sharp ternary nucleus. Attack the
   unbounded depth of that inverse tree through endpoint-coupled height or congruence. `D2-O09`
   localizes every unbounded Archimedean reset to the deepest branch and proves that fixed
   depth/unit modes do not contain it; attack that branch through exact mantissa arithmetic,
   guarded concatenation, or endpoint-coupled height. `D2-S10` classifies every consecutive
   reduced unit-wall segment inside a finite denominator-bounded rectangle and proves eventual
   periodicity there. `D2-S12` classifies every immediate lower/middle two-cycle and kills a
   finite literal return census. `D2-S13` realizes primitive guarded cycles of every positive
   period through exact upper runs. `D2-S14` embeds every finite wait body in a guarded wall
   excursion, so local forbidden-factor grammars are equally exhausted. Attack endpoint-coupled
   fibres rather than refining the wall-only graph. `D2-S15` identifies equality of periodic
   endpoints with global affine commutation and splits it into balanced-kernel and explicit
   collision-source fibres. `D2-S16` further turns any two-loop fibre into either a global power
   relation or an injective rank-two guarded loop family. `D2-S17` extends the balanced-kernel/
   collision-source split to arbitrary fixed endpoint fibres. `D2-S18` reduces same-length
   cross-grade source acceptance to one explicit parity/LTE intercept carry, and `D2-S19`
   reduces complete collision acceptance to the matching affine-determinant carry. `D2-S20`
   removes every suffix-ordered pair from every positive-source fibre, leaving only signed
   cumulative-wait walks that cross zero. `D2-S21` strips every common initial or terminal
   segment from the fixed-source equation and gives the exact cleared-determinant recurrence;
   enumerate only endpoint-irreducible crossing walks. `D2-S22` rejects odd first prefix gaps,
   forces a bounded later carry partner, and completely classifies the depth-one first carry;
   `D2-S23` completely classifies length-two mixed-sign crossings: `k≤2`, the gap lies in one of
   two explicit residue families, the target lies in a `10×50` or `10×250` residue rectangle,
   each rectangle has an exact forty-pair table, and the real gauge is classified exactly.
   Begin the remaining higher-depth
   tied-minimum search at length three through the weighted source balance.
   Keep the non-elementary lanes independent: adelic cone types, parabolic rational subsets,
   trace/height descent, finite-obstruction saturation, and valuation universality.
6. Synthesize the returned attacks by the discriminating signals above; do not average
   incompatible hypotheses into one generic mortality prompt.

These are research programs, not consequences of the present theorem.

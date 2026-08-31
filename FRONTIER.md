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
two-`c` obstruction is not a source classification. See
`audits/m53-separated-two-c-orbits-2026-08-31.md`.

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
| `M₄(3)` | an undecidable promised two-state overlap queue with pure deletion, or closure of either parabolic bridge language | by CHHN, also `M₈(2)` |
| `M₅(3)` | a five-state binary same-zero root, a toggle/separator fusion, or fixed-width-three scheduled universality | supersedes `M₆(3)`; `M₁₀(2)` is already known |
| `M₉(2)` | a history-sensitive same-zero compiler, overlapping parser fibres, or a changed source; canonical and trailing-toggle exact prefix routes stop at ten | improves the two-generator threshold by one |
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
   `bb c bⁿ c bⁿ` in residues zero and one. The next source-level cut is the residue-two
   diagonal or unequal separated runs, not another adjacent-`c` example.

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
excludes the residual value `2μ`, so the complete distinguished-boundary
`β` shell is safe.
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

[`MM-O20`](SALVAGE.md#mm-o20-decimal-first-cylinder-collision) gives the unbounded suffix
language an exact metric: a backward word gains the sum of its shifts in both decimal valuations,
and one block maps the unit domain onto one exact suffix cylinder. But first-cylinder decoding is
not injective. The lawful blocks `R_bR_cD_b` and `D_bR_cD_b` have identical depth-`2β+3`
cylinders for every compiler-emitted body; their long common lower suffix hides the first phase.
The live cut is therefore the intersection of the encoded-entry orbit with complete composed
inverse branches, or a proved reachability-sound quotient of those branches. Neither a fixed
congruence graph nor the first unbounded cylinder retains enough information.

The immediate ternary question is which other positive valuation-one discrepancies survive its
suffix sieve without already certifying source halting.
Exact bidirectional diagnostics for the ternary swap at `β=3`, body `bbcc`, exclude every
false-pole word of at most six projective blocks when each regular block has
role length at most three; this is computational evidence only.
A single explicit nonterminal pole orbit kills this family; a closed invariant proves
`M₅(3)`. The same-zero binary root and fixed-width-three source remain independent fallbacks.

### 3. Two-generator realization: `M₉(2)`

The exact obstruction is now complete. The physical word `000` in the restricted ten-state
pair is rank one, but its scalar sandwich has exact Hankel rank ten. More strongly, the word
products of the pair span `M₁₀(ℚ)`
([`MM-O08`](SALVAGE.md#mm-o08-full-algebra-prefix-pair)). The pair therefore has no nonzero
proper invariant subspace or quotient, and every nonzero internal-word sandwich has exact
realization dimension ten. Common-image restriction, kernel quotient, reachable/observable
minimization, and internal punctuation cannot reach nine states from this pair.

The surviving route must change the physical pair, change its nonzero values while preserving
zeros, or use a nonlinear compiler. A literal binary prefix tree for five source symbols has
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

Thus neither another exact prefix layout nor an exact three-phase block factorization remains
live. The direct frontier is a genuinely changed zero series, a nonfactorial state-dependent
decoder, another invariant quotient not induced by the generators' common image, or a nonlinear
reduction. A singular same-zero/history compressor borrowed from the `M₃(4)` lane is now governed
by [`G3-O27`](SALVAGE.md#g3-o27-projective-toggle-line-atlas): if both data stages are singular
and the absorbed trailing toggle is projectively involutive, its projective history remains in a
six-carrier line atlas. Such a nine-state escape must therefore solve the surviving nonexpanding
point-reachability problem in a finite rational `P¹` atlas, potentially jointly with `M₂(3)`,
retain non-scalar toggle powers, or use a full-rank data stage. `GPCP(3)` remains the independent
stronger ancestor.

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
| Transverse-kernel terminal dynamics | `G3-O27/O29` reduce the involutive branch to the `M₂(3)` core; `G3-O30` gives an infinite nonprojective plane orbit; `G3-O31` permits at most one whole-plane depth per nonzero row | Exploit the moving proper line sections with an all-word converse, solve the joint dimension-two node, or use a full-rank data map |
| Positive projective transition lower bound | Same-zero dimension three is point-line incidence in `P²`, and actual one-sided shifts retain finite rank/kernel/image data | Derive a uniform nonstationary or noncommuting shift incompatibility from an unbounded terminal section; static support rank, formal inverse completion, fixed equal-length return flowers, and unary consecutive-repeat escape are forbidden |
| Global word-residual recoding | Longer noncommutative atoms can retain order while discarding the four additive role channels | Escape `G3-D05`: fixed-priority affine counters and all one-way reset/transfer/fanout cascades are decidable |
| Head-separated three-schema source | `G3-C04` discharges every arbitrary-trace forcing obligation locally; `G3-O24` isolates the directed stable-cone alternative | Preserve an undecidable mixed or neutral word across returns, or realize zero-sensitive S5 GLB decoding after the `G3-O25` separator-rank fork; complete pure forks are decidable by `G3-D07` |
| Carvalho projective group-orbit separator | `G3-M03` gives the exact saturated three-positive cover; `G3-O23` collapses every singular carrier to invertible dimension two; `D2-D02/D08` decide all elementary group actions; `D2-D09` decides the profinite-blind step-three shear family by height | Universalize the height/continued-fraction normal form to arbitrary non-elementary `UCB₂(S)`, or construct the invertible three-state line/plane orbit left by `G3-O22`; finite ambient quotients are forbidden by `G3-O28` |

These six lanes form three trunks. The first three race a direct paired construction against its
one-sided projective lower bound. The next two seek genuine `GPCP(3)` through either global
recoding or a native source. The last is now a projective group-orbit attack shared with the
dimension-two campaign: `G3-O21` closes its algebraic semantic carrier, `G3-O23` removes
singular spelling memory, `D2-D02/D08` remove the elementary group branch, and `G3-O28`
removes all finite ambient-quotient separation on one promised no-instance. `D2-D09` then decides
that no-instance's complete fixed-source family by Archimedean height.

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
   depth.
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
lines at every other depth. A full-rank data map remains the other escape.
A lower-bound attack must exclude both positive
architectures through actual transition data. Backward cancellation, inverse cofinality, and
static incidence cannot do so. Do not spend another attack on separator placement, fixed anchors,
or control singularity after recognition; `MM-C01` closes them unconditionally.

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
is whether comparable descent survives for arbitrary non-elementary rational generators.

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

Thus every unclassified ReturnSquare instance has a base divisible by at least two distinct
primes; every nonresonant zero must use at least three positive returns in the bounded middle
negative strip. The one-base prime-power architecture is closed.

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
| Bound the mixed-prime reverse fan uniformly | a target at negative `3`-depth `d` has exactly `d+1` distinct shell-legal predecessors when its rational carrier is a `3`- and `5`-unit |
| Prune cross-length shell collisions at their source | every two nonempty unequal-length shell maps have a unique collision source and it is automatically a `5`-adic unit; only fixed-source equality and target acceptance remain discriminating |
| Infer target acceptance from the automatic cross-length source unit | the adjacent debt-safe bridges `[4]` and `[0,5]` collide from the `5`-unit source `2/9`, but their target `55/243` has `5`-adic valuation one |
| Bound accepted debt-bridge waits from one fixed source | for every `k≥0`, `[1,10k+2]` and `[3,1,10k]` are accepted adjacent bridges from `43/24`, with terminal waits tending to infinity |
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
the chamber/height pair to arbitrary nonelementary generators, or isolate the algebraic feature
which prevents it. Raw word length alone is not a lawful height: relations can make long words
represent short group elements.

#### 6. Exact symbolic saturation and finite obstructions

Run backward saturation from the target using cones, valuation vectors, residue classes, and
affine lattices. A successful well-structured formulation must decide exact reachability, not
only coverability. `G3-O28` closes finite ambient-group separation for `UCB₂(S)`: one promised
empty coset survives every finite quotient of its natural `S`-arithmetic ambient group. Finite
residues may remain components of an infinite annotated state, but cannot be the complete
negative certificate. `D2-D09` decides that explicit family by an unbounded Archimedean height;
it is the model for the annotation that finite saturation was missing.

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
4. Treat `MM-O08` and `MM-O11` as formally closed exact-family obstructions. Search for
   `M₉(2)` only through a changed physical pair, changed nonzero behavior, or a nonlinear
   compiler.
5. Run the `M₃(4)` program on distinct tracks: history-sensitive paired point-line synthesis,
   projective group-orbit separation for the exponent-one singleton, global word-residual
   recoding, and native three-schema rewriting. `G3-O23` has absorbed the singular saturated
   Carvalho branch into dimension two, and `G3-O28` has killed every finite quotient of one
   natural `S`-arithmetic ambient group there. `D2-D09` decides that fixed shear family by height;
   universalize the infinite descent rather than retaining the example as a hardness candidate.
   Do not revive singular spelling memory, conflate group inverses with positive `M₂(3)` controls,
   or retry finite ambient-group separation as a complete certificate.
6. Formalize `D2-S02` and `D2-D05`–`D2-D07`, then attack fixed-source exact prefix and
   accepting-exit reachability in the guarded `5`-adic schedule with a synchronized `2`/`3`/`5`
   representation. Use the checked `D2-S03` walls to isolate mixed-sign debt transfer and
   equality-wall cancellation; a chamber argument that never handles those transitions is
   incomplete. Inside uninterrupted negative `3`-depth, restrict
   source-specific point-collision search to cross-length bridges: fixed-length collisions are
   already global affine relations by `D2-O02`. Treat chamber exit and reentry as separate seams.
   In parallel, seek a parametric affine-kernel description beyond the checked length-30 basis
   and run normalized collision/exit-fibre census.
   Do not reopen unlabeled residue-only finite nuclei or uniformly bounded reverse fanout.
   Keep the non-elementary lanes independent: adelic cone types, parabolic rational subsets,
   trace/height descent, finite-obstruction saturation, and valuation universality.
7. Synthesize the returned attacks by the discriminating signals above; do not average
   incompatible hypotheses into one generic mortality prompt.

These are research programs, not consequences of the present theorem.

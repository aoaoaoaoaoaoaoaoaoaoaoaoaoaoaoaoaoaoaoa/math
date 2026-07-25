# Salvage Theorem Registry

This file is the canonical index of reusable results obtained while an attack failed to settle
its target. `FRONTIER.md` owns strategy; `FORMALIZATION.md` owns Lean coverage; `audits/` own
bounded reviews. Raw prompts and undigested Pro reports are not repository artifacts.

## Record Contract

Every record has a stable identifier and five core fields:

- **kind**: compiler, obstruction, structure theorem, decidable stratum, certificate, or partial
  mechanism;
- **evidence**: `reported`, `audited`, `formalized`, or `computational`;
- **disposition**: `stock`, `active`, `closed`, `parked`, or `graduated`;
- **scope**: the exact hypotheses and conclusions that may be reused;
- **use**: the attack or proof obligation for which the result is operational;

Every active record also states the next promotion step. A graduated record instead cites its
formal artifact.

The first namespace component identifies the campaign: `MM` for general matrix-mortality
compilers, `M4` for the `M₄(3)` frontier, `G3` for the three-letter GPCP and `M₃(4)`
frontier, and `D2` for the dimension-two wall. The second component identifies the result
class: `C` compiler, `O` obstruction, `M` partial mechanism, `S` structure theorem, or `D`
decidable stratum. Numbers never change after assignment.

`reported` means that the result survives only as a contracted statement from an external
review. It cannot support a publication claim. `audited` means that its proof has been checked
independently in this project. `formalized` means that the cited Lean declaration passes the
strict gate. `computational` never licenses an unbounded theorem.

`stock` is ready for reuse without scheduled promotion. `active` has a live use or promotion
task. `parked` remains valid but lacks a current route to its target. `graduated` has entered the
formal corpus. `closed` is retained only as a warning after refutation or strict subsumption.

Agents should cite record identifiers in research prompts and frontier updates. A prompt must
carry the record's scope, not merely its conclusion. A reusable result without enough statement
or construction to recover its use does not belong here. GitHub issues own scheduled work; this
file owns the mathematical stock.

## Index

| ID | Kind | Result | Evidence | Disposition |
| --- | --- | --- | --- | --- |
| [`MM-C01`](#mm-c01-fixed-anchor-rank-one-compiler) | compiler | common-fixed-column scalar zero to mortality | formalized | graduated |
| [`MM-C02`](#mm-c02-common-image-restriction) | compiler | mortality-preserving restriction to a common image | formalized | graduated |
| [`MM-C03`](#mm-c03-scheduled-binary-compiler) | compiler | fixed-width tag strokes to a total two-letter scalar series | formalized | graduated |
| [`MM-O01`](#mm-o01-all-placement-packing-rank) | obstruction | literal CHHN packing has exact rank six for every separator placement | reported | active |
| [`MM-O02`](#mm-o02-one-sided-phase-overlap) | obstruction | standard common-line phase fusion becomes one-sided | reported | parked |
| [`MM-O03`](#mm-o03-two-channel-boundary-tax) | obstruction | exact diagonal rank-two punctuation costs two states beyond Hankel rank | audited | active |
| [`MM-O04`](#mm-o04-uniform-rank-four-paired-series) | certificate | the paired scalar series has exact Hankel rank four | audited | active |
| [`MM-O05`](#mm-o05-width-three-scheduled-rank) | obstruction | the width-three scheduled series has exact rank five | formalized | graduated |
| [`MM-O06`](#mm-o06-pure-power-punctuation-obstruction) | obstruction | an exact isolated toggle cannot also punctuate through a pure power | audited | stock |
| [`MM-O07`](#mm-o07-setter-parameter-rigidity) | obstruction | source-boundary alignment fixes the setter parameter | audited | stock |
| [`MM-M01`](#mm-m01-off-diagonal-companion-interface) | partial mechanism | off-diagonal rank-two bridge has a complete fracture grammar | audited | stock |
| [`MM-M02`](#mm-m02-bordered-toggle) | partial mechanism | one lifted toggle has a stable rank-two third power | audited | parked |
| [`MM-M03`](#mm-m03-five-state-setter-punctuation) | partial mechanism | a mixed delimiter word is an exact internal rank-one separator | audited | active |
| [`MM-S01`](#mm-s01-square-run-projective-normal-form) | structure theorem | malformed square runs reduce to rational projective pole avoidance | audited | active |
| [`M4-C01`](#m4-c01-two-state-pushout-compiler) | compiler | binary deterministic two-state scalar control compiles to three `4 × 4` matrices | audited | active |
| [`M4-O01`](#m4-o01-exact-toggle-fusion-leaves-an-immortal-core) | obstruction | exact local toggle fusion preserves an invertible two-plane | audited | stock |
| [`M4-O02`](#m4-o02-two-private-state-phase-signature) | obstruction | exact shared-channel phase ratios are constant or two-periodic | audited | active |
| [`M4-S01`](#m4-s01-odd-phase-macro-cut) | structure theorem | paired Neary roles inherit a rigid macro-stroke language | reported | active |
| [`M4-O03`](#m4-o03-closed-serialization-collapse) | obstruction | finite closed-token queue serialization is decidable | audited | active |
| [`M4-O04`](#m4-o04-exact-internal-final-code-defect) | obstruction | distinct exact binary codes for one macro force commuting upper images | audited | stock |
| [`M4-O05`](#m4-o05-direct-two-state-first-return-recoding) | obstruction | the present four Neary roles have no direct two-state first-return code | reported | active |
| [`M4-M01`](#m4-m01-mixed-cube-root-punctuation) | partial mechanism | rational cube-root toggles reduce mixed punctuation to incidence equations | audited | parked |
| [`G3-O01`](#g3-o01-four-role-macro-irreducibility) | obstruction | exact nonerasing macros cannot reduce the four source roles to three letters | audited | active |
| [`G3-S01`](#g3-s01-shift-equivariant-zero-incidence) | structure theorem | same-zero state dimension is equivariant projective incidence dimension | audited | active |
| [`G3-M01`](#g3-m01-free-group-discrepancy-engine) | partial mechanism | free cancellation implements queue deletion with an all-path converse | reported | active |
| [`D2-S01`](#d2-s01-projective-hard-core) | structure theorem | `M₂(3)` is equivalent to two-generator projective incidence | audited | active |
| [`D2-D01`](#d2-d01-projectively-unimodular-stratum) | decidable stratum | projectively unimodular hard-core instances are decidable | audited | stock |
| [`D2-D02`](#d2-d02-invariant-pair-stratum) | decidable stratum | invariant projective pairs reduce to abelian-by-`C₂` reachability | reported | active |
| [`D2-D03`](#d2-d03-common-multiplier-stratum) | decidable stratum | rational affine maps with one multiplier are decidable under regular control | reported | active |
| [`D2-D04`](#d2-d04-single-base-affine-stratum) | decidable stratum | rational-subset incidence in `G_q^±` is decidable | reported | active |

## Matrix Mortality

### MM-C01: Fixed-anchor rank-one compiler

**Kind:** compiler  
**Evidence:** formalized  
**Disposition:** graduated

Let every active matrix `X_a` fix a nonzero column `e`, let `Le ≠ 0`, and put `P = CL`. Then the
family `{X_a} ∪ {P}` is mortal exactly when `LX_wC = 0` for some active word `w`. The converse
fractures every arbitrary product at every occurrence of `P`; the fixed column replaces
invertibility at the exterior row.

**Scope:** empty internal blocks are harmless only when `LC ≠ 0`; the theorem does not make the
scalar source undecidable.

**Artifact:** `MatrixMortality.fixedAnchor_mortal_adjoin_outer_iff` in
[`TerminalTile.lean`](MatrixMortality/TerminalTile.lean).

**Use:** prefer this theorem to a bespoke separator argument whenever a common fixed column is
available.

### MM-C02: Common-image restriction

**Kind:** compiler  
**Evidence:** formalized  
**Disposition:** graduated

Suppose every generator maps the ambient space into a common subspace `K`, and explicit integral
maps `J : K → V` and `Q : V → K` satisfy `QJ = I` and `A_iJ = JB_i`. Mortality of the restricted
family follows from mortality upstairs. Conversely, if `B_w = 0`, then `A_w` kills `K`; appending
any generator whose image lies in `K` gives a zero ambient product.

**Scope:** the appended-letter converse is required. Restriction alone may introduce zero
products absent from the ambient family.

**Artifact:** `MatrixMortality.isMortal_commonImage_iff` and
`MatrixMortality.restrictedPrefixGenerator_mortal_iff_prefixMachine` in
[`MatrixSemigroup.lean`](MatrixMortality/MatrixSemigroup.lean) and
[`PrefixMortality.lean`](MatrixMortality/PrefixMortality.lean).

**Use:** this is the reusable core of the `12 → 10` binary mortality compiler.

### MM-C03: Scheduled binary compiler

**Kind:** compiler
**Evidence:** formalized
**Disposition:** graduated

A deletion-width-`β` tag stroke consists of one rule role followed by `β−1`
erasures. After reversal its phase schedule is fixed. Two generators can therefore
select only the tag letter while a cyclic `β`-phase lower channel selects rule or
erasure semantics. The representation has coordinates

```text
(affine, upper, lower₀, …, lower_{β−1})
```

and dimension `β+2`.

The decoder is total on the binary free monoid and preserves the source
coefficient exactly. Every lawful tile history has an explicit reverse-stroke
encoding. Conversely, a zero coefficient invokes the terminal-match normal form,
so the decoded roles form complete strokes; in particular, every zero word has
length divisible by `β`. Unfinished clock cycles cannot create zeros.

**Scope:** this is a fixed-width compiler, not a fixed-dimensional reduction from
the present undecidable source. Neary's universality compiler sets `β=10·period`.

**Artifact:** `MatrixMortality.scheduledCoefficient_eq_sideCoefficient`,
`MatrixMortality.decodeScheduled_historyCode`,
`MatrixMortality.scheduledCoefficient_zero_length_dvd`, and
`MatrixMortality.scheduledBinary_zero_iff_tagHaltsFrom` in
[`ScheduledBinary.lean`](MatrixMortality/ScheduledBinary.lean).

**Use:** any future undecidable source at constant deletion width `β` immediately
gives a two-generator scalar representation in dimension `β+2`. At `β=3`, the
conditional rewards are `Z₅(2)`, `M₅(3)`, and `R₆(2)`.

### MM-O01: All-placement packing rank

**Kind:** obstruction  
**Evidence:** reported  
**Disposition:** active

For every placement of the four ordinary `3 × 3` payloads and the rank-one separator in the
literal three-generator `6 × 6` CHHN packing, the selected scalar coefficient series reportedly
has Hankel rank exactly six. The report supplies six-prefix and six-suffix determinant
certificates for the three separator-location cases.

**Scope:** this excludes exact five-state realizations of that coefficient series. It does not
exclude a different five-state series with the same zero set.

**Use:** reject further exact minimization of the literal CHHN packing and require a changed
coefficient series or punctuation architecture.

**Artifact:** the claim and its prior-art scope are preserved in
[`audits/m44-prior-art-2026-07-22.md`](audits/m44-prior-art-2026-07-22.md#7-the-chhn-packing-and-the-hankel-rank-six-obstruction).
The symbolic proof has not been independently reconstructed in Lean.

**Next:** audit the determinant families, then formalize one placement-independent finite
certificate.

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O02: One-sided phase overlap

**Kind:** obstruction  
**Evidence:** reported  
**Disposition:** parked

In the standard two-slot selector architecture, a common invariant line reportedly forces its
overlap vector into either the upper-word or lower-word invariant plane. The resulting bridge
depends on only one positional-value channel; after this forcing step, its zero language is
effectively regular.

**Scope:** the forcing statement concerns the stated common-line phase fusion, including its
projective rescalings. The regularity conclusion is conditional on the global mortality
converse reducing malformed words to finitely many such bridges. It is not a general
impossibility theorem for five-state zero-set representations.

**Use:** reject a proposed common-line selector only after matching all of its hypotheses.

**Artifact:** bibliographic scope is recorded in
[`audits/m44-prior-art-2026-07-22.md`](audits/m44-prior-art-2026-07-22.md#8-the-phase-fusion-obstruction-and-regular-positional-value-languages).

**Next:** recover and audit the forcing proof before using it to reject another architecture.

### MM-O03: Two-channel boundary tax

**Kind:** obstruction

**Evidence:** audited

**Disposition:** active

Let `A : Σ* → Mₙ(K)`, let `U=[u₀ u₁]` and `V=[v₀;v₁]` both have rank two, and suppose

```text
V A_w U = [[0,0],[0,h(w)]]
```

for every word `w`. If `h` has Hankel rank `d`, then `n ≥ d+2`.

Write `R = span{A_wu₁}` and `N = {x : v₁A_wx=0 for every w}`. The active realization has
dimension `dim R/(R∩N)=d`; the zero bridge entries give `u₀∈N` and `v₀R=0`. If `u₀∈R`, it adds
one unobservable reachable direction and `v₀` forces one complementary dimension. If `u₀∉R`,
the direct sum `R+Ku₀` is still annihilated by nonzero `v₀`. Both cases give `n≥d+2`.

**Scope:** exact diagonal two-channel identities only. Invertible row and column changes on the
two boundary channels preserve the conclusion. Same-zero series and off-diagonal bridges are
outside the theorem.

**Use:** with [`MM-O04`](#mm-o04-uniform-rank-four-paired-series), this closes every exact
five-state diagonal rank-two bridge for the paired scalar series.

**Next:** formalize the finite-dimensional statement without importing a general infinite
Hankel library.

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O04: Uniform rank-four paired series

**Kind:** certificate  
**Evidence:** audited  
**Disposition:** active

For every `β≥3` and every tag body, the scalar series

```text
f(w) = ℓ A_w γ,       w ∈ {b,c,t}*
```

of the explicit paired `4 × 4` controls has Hankel rank exactly four. A
body-independent certificate already lies in the subalphabet `{b,t}`. Put

```text
s = 3^β,      p = 3s,      m = (5s−1)/2,
u = 3m+2,     a = 3p.
```

For the `b` control `B`, toggle `T`, row `ℓ`, and column `γ`, the four prefix rows

```text
ℓ, ℓB, ℓB², ℓBT
```

have determinant `48u(13a−15)`. The four suffix columns

```text
γ, Tγ, Bγ, BTγ
```

have determinant `12p(s−3)`. Both are nonzero for `β≥3`, so their product is a
nonzero `4 × 4` Hankel minor. The displayed representation supplies the matching upper
bound.

The same certificate survives

```text
g(w) = λ χ(w) f(w)
```

for `λ≠0` and every nonzero monoid character `χ`, because the Hankel minor changes only
by invertible diagonal row and column scalings.

**Scope:** exact coefficient series over characteristic zero, including similarity, exact
restriction or quotient, and nonzero per-letter rescaling. The result supplies no lower bound
for another series with the same zero set.

**Use:** proves exact minimality of paired-role compression and supplies `d=4` to
[`MM-O03`](#mm-o03-two-channel-boundary-tax). It also closes exact three-state
minimization of the paired route to `M₃(4)`.

**Next:** check the determinant identities in Lean and add their transitive axioms to the
publication snapshot.

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O05: Width-three scheduled rank

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For deletion width three and every nonempty tag body, the scheduled binary
coefficient series has exact rational Hankel rank five. A symbolic `5×5` minor
using

```text
prefixes = {ε, 0, 1, 00, 10},
suffixes = {ε, 0, 1, 00, 01}
```

factors into explicit reachable and observable matrices with nonzero
determinants. Every exact rational representation therefore has at least five
states; the native scheduled representation has exactly five.

**Scope:** exact coefficients, deletion width three, and nonempty body. The
generic experimental claim `rank=β+2` is not part of the theorem. Same-zero
representations remain outside every Hankel-rank lower bound.

**Artifact:** `MatrixMortality.scheduledWidthThree_exact_state_lower_bound`,
`MatrixMortality.scheduledWidthThreeHankel_det_ne_zero`, and
`MatrixMortality.scheduledWidthThree_native_state_card` in
[`ScheduledBinaryRank.lean`](MatrixMortality/ScheduledBinaryRank.lean).

**Use:** reject exact state compression of the width-three clock below five.
The live fixed-table routes must change the zero series, change the source, or
fuse the clock with a delimiter or mortality interface.

### MM-O06: Pure-power punctuation obstruction

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Lift the paired data matrices and toggle to five dimensions by

```text
Ĝ_x = diag(G_x,0),      T̂ = diag(T,0).
```

For a nonempty tag body, `Ĝ_b` and `Ĝ_c` have a common three-dimensional image
`H` and common kernel `ℚe₅`. Suppose a candidate delimiter `S` realizes an
isolated toggle in every data context:

```text
Ĝ_i S Ĝ_j = Ĝ_i T̂ Ĝ_j,      i,j∈{b,c}.
```

Then `S−T̂` maps `H` into `ℚe₅`. Since `T` fixes the affine and upper-word
directions, `S` has a nonzero fixed vector in their span. Evaluating any proposed
contextual identity

```text
Ĝ_i S^m Ĝ_j = λ Ĝ_i P̂ Ĝ_j,      m≥1, λ≠0,
```

on that vector contradicts the payload action of the paired separator `P=CL`.
No pure delimiter run can therefore serve as the separator while isolated
delimiters retain their exact toggle semantics.

**Scope:** the theorem assumes a nonempty body, exact toggle behavior between
both data contexts, the lifted paired matrices, and punctuation by a pure power
of `S`. It does not exclude a mixed word containing data matrices, approximate
or same-zero toggle semantics, or another representation.

**Use:** reject pure-power variants of the bordered-toggle route. Any surviving
fusion must punctuate with a mixed word.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md).

### MM-O07: Setter parameter rigidity

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

In the five-state setter construction, write

```text
f=(1,0,r)ᵀ,      p=(0,−1,0)ᵀ,      B=[f p q],
C=(μ,−1,t)ᵀ,     C̃=(μ,1,0,1,0)ᵀ.
```

The payload part of the marked boundary is

```text
B(μ,1,0)ᵀ=(μ,−1,μr)ᵀ.
```

Exact alignment with `C` therefore forces

```text
r=t/μ.
```

The parameter is not generic in the displayed source-preserving family. A
reported malformed zero at `r=8735/8978` also fails direct symbolic
multiplication: for `β=3`, body `bbcc`, the claimed word has coefficient

```text
(2r+1)(17956r²−9246r−8709)/(134(r−1)),
```

which is nonzero both at the reported value and at the lawful value `81/67`.

**Scope:** this fixes the parameter only for the displayed basis and marked
boundary. Another construction may introduce genuine free parameters. The
coefficient check rejects the reported counterexample, not all malformed
counterexamples.

**Use:** remove generic-parameter selection from the live proof program. The
projective avoidance problem must be settled at `r=t/μ`.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#parameter-correction).

### MM-M01: Off-diagonal companion interface

**Kind:** partial mechanism  
**Evidence:** audited  
**Disposition:** stock

For `g(w)=λB_wd`, invertible `B_a`, and `α=λd≠0`, define

```text
J(x) = [[0,x],[1,0]].
```

In dimension `r+1`, put

```text
u₀ = e_{r+1},           u₁ = (d/α,0)ᵀ,
v₀ = (λ,0),             v₁ = e_{r+1}ᵀ,
U  = [u₀ u₁],           V  = [v₀;v₁],
E  = UV.
```

Then `rank E=2` and

```text
V diag(B_w,1) U = J(g(w)/α).
```

Products fracture at `E`, and a central product of `J` matrices can vanish only if a bridge
coefficient vanishes. Repeating one zero bridge twice gives `J(0)²=0`.

**Scope:** as a standalone scalar-to-mortality compiler this is dominated by the rank-one
separator `P=dλ`, which stays in dimension `r`. A four-state binary root would therefore prove
`M₄(3)`, not merely `M₅(3)`.

**Use:** retain `J` only as a target interface when punctuation must be represented by a word in
another generator rather than adjoined as its own generator.

**Next:** use the off-diagonal interface in the fused-toggle search; do not present it as a new
frontier reduction.

### MM-M02: Bordered toggle

**Kind:** partial mechanism  
**Evidence:** audited  
**Disposition:** parked

Choose a two-plane `F` in the `+1` eigenspace of the paired toggle, complete it by a third
`+1` eigenvector `g`, a `−1` eigenvector `h`, and a fifth vector `η`. In the basis
`(F,g,h,η)`, put

```text
S = I_F ⊕ K,             K = [[1,0,1],[0,−1,1],[−1/2,−1/2,0]].
```

Its upper-left four-dimensional block is the original toggle, and

```text
rank S = 4,     rank S² = 3,     S³ = Π_F,     rank Π_F = 2.
```

With data lifts `diag(G_x,0)`, every word containing no adjacent toggles has the original
four-dimensional control product as its upper-left block and is therefore nonzero. Maximal
toggle runs have three modes: `S`, `S²`, and `Π_F`.

**Scope:** mixed `S²` runs, malformed placements of `Π_F`, and the required rank-one or
off-diagonal selector are unresolved. Bounded searches on one benchmark do not establish an
impossibility theorem.

**Use:** a concrete architecture for fusing the toggle and separator into the third physical
generator of an `M₅(3)` family.

**Next:** parameterize the permitted fifth-coordinate couplings, solve the selector identities
symbolically, and prove a global maximal-run grammar or a symbolic no-go theorem.

### MM-M03: Five-state setter punctuation

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

Let `r=t/μ`, put

```text
f=(1,0,r)ᵀ,      p=(0,−1,0)ᵀ,
q=(0,0,2r(1−r))ᵀ,      B=[f p q],
α=1+2r,          λ=α/μ,
```

and conjugate the three-dimensional rule matrices by `B`. Two marker
coordinates produce explicit rational `5 × 5` data matrices `A_b,A_c` and a
delimiter `S`. The latter satisfies

```text
rank S=3,      rank S²=2,      rank S³=1,
Sⁿ=S³ for n≥3.
```

Every data matrix clears the markers. On words without `S²`, an isolated
delimiter immediately to the right of a data letter selects its erasure role;
absence of a delimiter selects its rule role. The marked terminal column makes
the rightmost data letter an erasure. This is an exact total decoder on the
regular physical language and represents every lawful source history.

For the distinguished letter `c`, the mixed word

```text
E=S²A_cS³
```

obeys the exact rank-one identity

```text
E=λC̃L̃.
```

Hence `EWE=0` exactly when `L̃WC̃=0`. A source halting witness therefore gives a
zero word over the three five-state generators `{A_b,A_c,S}`.

**Scope:** this proves the regular-word semantics, internal separator, and
halting-to-mortality implication. It does not prove the converse: arbitrary
words may contain maximal delimiter runs of length two.

**Use:** this is the concrete mixed-word successor to the parked bordered
toggle. Combine it with [`MM-S01`](#mm-s01-square-run-projective-normal-form);
do not claim `M₅(3)` until projective avoidance is proved.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#side-normal-data).

**Next:** formalize the displayed matrices, regular decoder, power identities,
and separator identity.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S01: Square-run projective normal form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

For the candidate in [`MM-M03`](#mm-m03-five-state-setter-punctuation), the
image of `S²` is the two-plane

```text
J={(a,x,0,x,0)ᵀ : a,x∈ℚ}.
```

If a regular intervening block has side product

```text
M_z=[[1,V,U],[0,B,0],[0,0,A]],
```

its action between square runs is represented on `J` by

```text
F_z =
[[1+rU,       −V],
 [κ(A−1−rU),  κV]],

κ=(1+2r)/(2μ(1−r)).
```

The determinant `κVA` is nonzero. Thus a segment containing square runs but no
`S³` cannot collapse by rank loss. On the affine projective chart, it acts by

```text
Φ_z(x)=κ(A−1−rU+Vx)/(1+rU−Vx)
```

and vanishes exactly when the current state reaches the pole

```text
π_z=(1+rU)/V.
```

Runs of length at least three equal the rank-one map `S³` and fracture every
arbitrary product into such projective bridges. The possible reset values are
`0` and `1/μ`. At `1/μ`, the pole equation is

```text
(μ+tU−V)/μ=0,
```

which is precisely the original terminal-match equation.

Consequently, the full mortality converse for `{A_b,A_c,S}` is equivalent to
the following avoidance property: every finite orbit generated by the
admissible maps `Φ_z`, starting at `0` or `1/μ`, avoids every pole except a
genuine terminal-match pole reached from `1/μ`.

**Scope:** the projective normal form and equivalence are proved for the
displayed candidate at the forced value `r=t/μ`. The avoidance property itself
is open. No bounded search certifies it.

**Use:** replaces an unstructured malformed-word grammar by a one-dimensional
rational dynamical problem. A proof of avoidance completes `M₅(3)`; one
nonterminal pole orbit refutes this candidate.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#square-run-transfer).

**Next:** seek a finite invariant based on congruences, `3`-adic valuation and
pulse phase, signed intervals, or self-synchronizing code suffixes. Search
states are projective values, not five-dimensional vectors.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

## Three-Generator Four-State Frontier

Formal promotion of this section is tracked in
[#5](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/5).

### M4-C01: Two-state pushout compiler

**Kind:** compiler
**Evidence:** audited
**Disposition:** active

For each data letter `x∈{b,c}`, let the role matrices

```text
R_x = [[1,V_x^R,U_x],[0,B_x^R,0],[0,0,A_x]],
D_x = [[1,V_x^D,U_x],[0,B_x^D,0],[0,0,A_x]]
```

agree on `E={(a,0,c)ᵀ}`. Embed the rule and deletion copies by

```text
ι_R(a,b,c) = (a,b,c,0)ᵀ,
ι_D(a,b,c) = (a,0,c,b)ᵀ.
```

For an arbitrary deterministic transition function
`δ : {R,D}×{b,c} → {R,D}`, let `ε_{q,x}` be one when `δ(q,x)=R` and zero
otherwise, and define

```text
X_x =
[[1, V_x^R,                  U_x, V_x^D                 ],
 [0, ε_{R,x}B_x^R,          0,   ε_{D,x}B_x^D         ],
 [0, 0,                      A_x, 0                     ],
 [0, (1−ε_{R,x})B_x^R,      0,   (1−ε_{D,x})B_x^D     ]].
```

Then

```text
X_x ι_R(v) = ι_{δ(R,x)}(R_xv),
X_x ι_D(v) = ι_{δ(D,x)}(D_xv).
```

Reading phases from the terminal column therefore gives a total suffix decoder for every
binary word. The rank is four when the two source states have different destinations and
three when they reset to the same destination.

Every `X_x` fixes `e₁`. For a terminal phase `q*`, put `C=ι_{q*}(μ,−1,t)ᵀ`,
`L=e₁ᵀ`, and `P=CL`. The fixed-anchor fracture then proves

```text
{X_b,X_c,P} mortal
  ↔ ∃w∈{b,c}⁺ : LX_wC=0.
```

This remains valid when either data generator has rank three: if an exterior column
`X_uC` vanishes, applying `L` already produces a nonempty scalar witness.

**Scope:** the theorem compiles a supplied undecidable controlled scalar source; it does not
prove that such a binary two-state source exists. The controller is deterministic and the
role pairs must agree on the complete two-dimensional upper channel.

**Use:** this is the finished matrix half of the `M₄(3)` route. Source searches should target
binary two-state controlled correspondence, not another four-dimensional separator proof.

**Artifact:** the independent algebraic reconstruction is
[`audits/m43-two-state-pushout-2026-07-24.md`](audits/m43-two-state-pushout-2026-07-24.md).

**Next:** formalize the pushout, total decoder, rank classification, and mortality equivalence
over the existing side-normal role matrices.

### M4-O01: Exact toggle fusion leaves an immortal core

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

For the paired controls, let

```text
H = im G_b = im G_c = span{e₁,e₃,e₄},
E = span{e₁,e₃}.
```

If a proposed fused generator satisfies

```text
SG_b = TG_b,       SG_c = TG_c,
```

then surjectivity onto `H` forces `S|_H=T|_H`. The toggle is the identity on `E`;
both data matrices preserve `E` and restrict there to invertible upper-triangular maps.
Every word over `{G_b,G_c,S}` therefore restricts invertibly to `E` and cannot be zero.

Separately, `S^r=T` with `r>0` makes `S` invertible, so no other pure power of `S` can be
rank one or zero.

**Scope:** exact contextual toggle identities and pure power codes only. A mixed macro may
break the shared plane internally and reconstruct it at its boundary.

**Use:** reject `T+P`, `TP`, `PT`, and power-coded toggle/punctuation proposals whenever they
claim exact local toggle semantics.

### M4-O02: Two-private-state phase signature

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

Suppose an exact phase compiler shares a two-dimensional upper plane and stores every private
lower channel in a quotient `Q` of dimension at most two. If `q_j∈Q` is the phase-`j`
private direction and

```text
X̄_x q_j = B_{j,x} q_{j+1},
```

then the ratio sequence

```text
ρ_j = B_{j,b}/B_{j,c}
```

is constant or two-periodic. If the `q_j` span one line, it is constant. Otherwise
`F=X̄_c⁻¹X̄_b` has every `q_j` as an eigenline; a two-dimensional operator has at most two
eigenlines unless scalar, and `X̄_c` can only fix or swap them.

The supplied Neary source has signature

```text
(ρ₀,1,…,1),       ρ₀≠1,
```

because all deletion lower words coincide while the two rule lower lengths differ. For
`β≥3` this is neither constant nor two-periodic.

**Scope:** exact phasewise `4=2+2` shared-channel realizations, including phase rescaling,
projective normalization, upper-plane shears, and basis changes. Nonletterwise macros and
same-zero representations remain outside the theorem.

**Use:** closes the direct extension of paired-role compression from two phases to the full
Neary deletion clock.

**Next:** formalize the quotient-eigenline argument and instantiate the Neary scale signature.

### M4-S01: Odd-phase macro cut

**Kind:** structure theorem
**Evidence:** reported
**Disposition:** active

For Neary's compiled width `β=10p`, the report observes that every semantic entry phase is odd
and every even track of the woven Table 2 word is the constant letter `b`. Pair the old roles as

```text
K_x = R_xD_b,       E_x = D_xD_b.
```

Writing `m=β/2`, every claimed macro solution expands to an old solution and is forced into

```text
((K_b+K_c)(E_b+E_c)^(m−1))⁺.
```

The upper words of `K_x` and `E_x` coincide for each `x`, while both deletion-macro lower
words are `00`. The macro family therefore retains the two-plane agreement required by
[`M4-C01`](#m4-c01-two-state-pushout-compiler).

**Scope:** the existing Lean corpus proves the deletion-stroke normal form and packages the
relevant Table 2 tracks, but it does not yet state the parity invariant or the macro
solvability equivalence. This record cannot support a theorem claim until those links are
checked.

**Use:** converts the source search from four isolated roles to a rule macro followed by
`m−1` deletion macros. It does not license the closed serialization refuted by
[`M4-O03`](#m4-o03-closed-serialization-collapse).

**Next:** prove the even-track invariant for every reachable compiled queue, define the macro
morphisms in Lean, and derive the all-solution macro normal form from
`tileHistory_of_terminal_match`.

### M4-O03: Closed serialization collapse

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

Let `Γ` be finite and let each semantic token `γ` have a complete binary block `Φ(γ)`.
Assume every macro-boundary queue is a concatenation of complete blocks, processing one
complete front block returns to the boundary state, and its output is a concatenation of
complete blocks determined only by `γ`:

```text
Φ(γ₁)…Φ(γₙ)  ↦  Φ(γ₂)…Φ(γₙ) Φ(τ(γ₁)).
```

At macro boundaries this is deletion-one substitution

```text
γ₁…γₙ ↦ γ₂…γₙ τ(γ₁).
```

It empties exactly when no symbol reachable from the initial word reaches a directed cycle in
the finite dependency graph `γ→η` for `η` occurring in `τ(γ)`. A reachable cycle supplies an
infinite descendant lineage; an acyclic reachable graph gives finite substitution forests.
Halting is therefore decidable.

**Scope:** finite closed tokens with locally determined complete-token output. Finitely many
instruction, junk, initialization, and terminal types merely enlarge `Γ`. Open front or tail
residues, state-dependent gauges, cancellation, and reconstruction only at larger pulse
boundaries are not covered.

**Use:** permanently reject the proposed single-active-track serialization
`x c^(m−2)b` and every elaboration that retains closed token boundaries.

**Artifact:** the proof audit is
[`audits/m43-two-state-pushout-2026-07-24.md`](audits/m43-two-state-pushout-2026-07-24.md).

**Next:** formalize the finite-graph criterion and use it as a guardrail for any future source
serializer.

### M4-O04: Exact internal/final code defect

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Suppose a binary source morphism `h` gives one semantic macro two distinct codewords `p≠q`
but preserves its upper word exactly:

```text
h(p)=h(q).
```

Then `h` is noninjective. By the two-word defect theorem, the images of the two binary letters
commute and are powers of one primitive word; every pair of words in `im h` therefore
commutes. The macro upper words

```text
û_b = u_bu_b,       û_c = 1u_b,       u_b=10^β1
```

do not commute: `û_bû_c` begins `10`, while `û_cû_b` begins `11`.

**Scope:** exact binary word-pair compilers with a state-independent upper morphism. A
state-dependent matrix gauge, an open residue, or solvability-only preservation is outside the
argument.

**Use:** distinct exact codewords cannot make one deletion macro mean “internal” in one place
and “final” in another.

### M4-O05: Direct two-state first-return recoding

**Kind:** obstruction
**Evidence:** reported
**Disposition:** active

Every first-return word to one state of a deterministic binary two-state controller is either a
one-letter loop or belongs to a family `emⁿr`. Four length-two returns form a rectangle, forcing
an exact factorization identity among their role maps. A loop family forces paired roles with
equal upper words to use equal exponents and hence equal lower words.

The report applies this classification to the four Neary roles and concludes that no direct
first-return recoding exists: the two deletion lower words coincide, while the rule lower words
do not.

**Scope:** direct exact recoding of the present four roles by first returns of a deterministic
binary two-state controller. A new controlled source, open residues, and nonexact matrix gauges
remain possible.

**Use:** [`M4-C01`](#m4-c01-two-state-pushout-compiler) needs a new source theorem; the present
four tiles cannot simply be relabeled by controller returns.

**Next:** reconstruct the rectangle and loop-family cases uniformly and formalize the
free-monoid cancellation argument before upgrading this record.

### M4-M01: Mixed cube-root punctuation

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** parked

The paired toggle has rational cube roots. On its three-dimensional `+1` eigenspace choose a
rational order-three map, and act by `−1` on the `−1` eigenspace; then `S³=T`.

Let `H=im G_b=im G_c` and let `k_x` span `ker G_x`. For a mixed word

```text
W = G_z S^s G_y S^r G_x,
```

the first rank drop is exactly

```text
rank(G_yS^rG_x)=2  ↔  k_y∈S^rH.
```

Writing `Π=G_y(S^rH)`, the second is

```text
rank W=1  ↔  S^(−s)k_z∈Π.
```

The search for a rank-one punctuation word is therefore a finite family of projective
incidence equations in the cube-root conjugacy parameters, followed by row- and column-boundary
alignment.

**Scope:** no parameter satisfying all incidences and boundary alignments is known. Even such
a solution would still require an arbitrary-product converse for every other mixed fragment.

**Use:** independent matrix-level fallback if the two-state source route stalls.

**Next:** solve the incidence varieties symbolically before enumerating words; reject any
candidate without a rank-stratified all-word grammar.

## Three-Letter Source Frontier

### G3-O01: Four-role macro irreducibility

**Kind:** obstruction

**Evidence:** audited

**Disposition:** active

Let the four fixed-boundary source roles be

```text
R_c = (1,    1H(q)10),      R_b = (H(b), 110),
D_b = (H(b), 0),            D_c = (1,    0).
```

Suppose a role morphism `h : {R_c,R_b,D_b,D_c}* → C*` and two nonerasing
morphisms `X,Y : C* → {0,1}*` preserve each displayed pair exactly. Then `|C|≥4`,
even when the four macro words `h(r)` have arbitrary unequal lengths and need not form a
code.

Indeed, the one-letter upper words of `R_c,D_c` force distinct one-letter macros `x,y`
with `X(x)=X(y)=1`. The one-letter lower word of `D_b` forces a third one-letter
macro `z` with `Y(z)=0` and `X(z)=H(b)`. If `C={x,y,z}`, any macro for `R_b`
must contain `z` to produce a zero under `X`. Since `X(z)` already has the complete
required length and `X` is nonerasing, that macro is exactly `z`; its lower image is then
`0`, contradicting the required `110`.

**Scope:** exact rolewise factorization through fixed macros with both new morphisms
nonerasing. It does not cover erasure, target recoding, boundary residuals, overlapping or
context-dependent codes, preservation of solvability alone, or a different computational
source.

**Use:** reject every proposal to merge or macro-expand the present four roles unless it
explicitly invokes one of the escape mechanisms outside the scope.

**Next:** formalize the length-one argument over free monoids and connect its role constants
to the existing Neary source definitions.

**Issue:** [#4, Formalize the four-role macro irreducibility
obstruction](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/4).

### G3-S01: Shift-equivariant zero incidence

**Kind:** structure theorem

**Evidence:** audited

**Disposition:** active

For a language `L⊆Σ*`, define its zero-language dimension over a field `K` by

```text
zdim_K(L) =
  min {d : ∃ λ,γ,(M_a)_{a∈Σ},
             w∈L ↔ λM_wγ=0}.
```

A `d`-state same-zero representation of a series `f` is equivalent to a
shift-equivariant incidence realization of its infinite Hankel zero pattern. Put

```text
r_x = λM_x,       c_y = M_yγ.
```

Then, for every prefix `x`, suffix `y`, and letter `a`,

```text
f(xy)=0 ↔ r_x c_y=0,
r_{xa}=r_xM_a,
c_{ay}=M_ac_y.
```

Conversely, rows, columns, and common letter maps satisfying these equations recover the
same-zero representation from `λ=r_ε` and `γ=c_ε`. For `d=3`, nonzero columns are
points and nonzero rows are lines in `P²(K)`; zeros are incidences.

**Scope:** a finite zero-pattern matrix of rank three is only a necessary finite shadow.
The common shift maps and rational realizability are indispensable. Zero rows or columns
must also be interpreted globally, not discarded projectively.

**Use:** formulate the surviving paired-route attack as equivariant point-line synthesis,
not exact weighted-automaton minimization. Finite nonlinear solves should enforce both
incidence and shift equations.

**Next:** construct increasing prefix/suffix instances, quotient projective gauge, and retain
finite unsatisfiable cores as candidate zero-language dimension obstructions.

### G3-M01: Free-group discrepancy engine

**Kind:** partial mechanism

**Evidence:** reported

**Disposition:** active

Carvalho's inverse-transducer reduction carries a cyclic-tag queue in the freely reduced
discrepancy

```text
Δ(w) = w⁻¹T(w).
```

On a legal transition, cancellation deletes the queue head while the transducer output
appends the production. An `H` marker counts simulated steps, a `p` marker prevents
trivial discrepancy on false paths, and every fixed point is forced to a closed transducer
path. This supplies both implicit deletion and an arbitrary-path soundness invariant.

**Scope:** the source is a free group, not a positive free monoid. The subgroup of closed
input paths has a computed free basis whose rank depends on the transducer. No bound of
three, positive encoding, or classical fixed-boundary GPCP compiler follows from the
preprint.

**Use:** audit whether the closed-path subgroup can be generated uniformly by three
positive macros or whether its control can be moved into boundaries without admitting
spurious reduced words.

**Source:** [`carvalho-2026-free-group-pcp.md`](references/carvalho-2026-free-group-pcp.md).

**Next:** extract the transducer for the smallest universal cyclic-tag source, compute its
closed-path subgroup rank, and identify exactly which formal inverses occur in the fixed-loop
converse.

## Dimension Two

### D2-S01: Projective hard core

**Kind:** structure theorem  
**Evidence:** audited  
**Disposition:** active

Every unresolved `M₂(3)` instance has two nonsingular generators `A,B` and one nonzero rank-one
generator `R=cr`. A minimal mortal word has the form `RWR`, and

```text
RWR = c(rWc)r.
```

Thus `M₂(3)` is computably equivalent to deciding whether `rWc=0` for some
`W∈{A,B}*`, equivalently point-to-point reachability on `P¹(ℚ)` under two rational Möbius
transformations.

**Scope:** the empty interior is allowed and gives `R²=0` exactly when `rc=0`. Larger generator
families may have several endpoint pairs; the three-generator hard core has one.

**Use:** every dimension-two attack should state which projective-incidence residue it decides
or encodes.

**Next:** formalize the minimal-word case split and rational-to-integer transport when the
dimension-two campaign enters its verification phase.

### D2-D01: Projectively unimodular stratum

**Kind:** decidable stratum  
**Evidence:** audited  
**Disposition:** stock

If primitive integral representatives of both projective generators have determinant `±1`,
point-to-point reachability is decidable by the established `GL₂(ℤ)` reachability machinery.
This includes rational scalar multiples of unimodular matrices.

**Scope:** it does not extend to arbitrary nonunit determinants.

**Use:** eliminate this stratum before invoking arithmetic dynamics or valuation storage.

### D2-D02: Invariant-pair stratum

**Kind:** decidable stratum  
**Evidence:** reported  
**Disposition:** active

If the generated projective group preserves an unordered pair of distinct algebraic points,
conjugation reduces it to multiplication and inversion in a finitely generated subgroup of a
number field of degree at most two. The report reduces rational point reachability to effective
semilinear membership in an abelian-by-`C₂` group.

**Scope:** the recognition algorithm and effective semilinearity require independent checking.
The claim does not cover a group with only one common fixed point.

**Use:** separate elementary projective groups from the non-elementary residue before invoking
height growth or valuation universality.

**Next:** audit the invariant-pair recognition cases and the positive-semigroup reachability
step.

### D2-D03: Common-multiplier stratum

**Kind:** decidable stratum  
**Evidence:** reported  
**Disposition:** active

For finitely many rational affine maps `z ↦ az+b_i` with one nonzero rational multiplier `a`,
rational endpoints, and regular control, the report reduces reachability to semilinear path
weights when `a=±1` and to corrected finite target discounted-sum reachability otherwise.
Fixed positive powers of one rational base reduce by regular block substitution.

**Scope:** the result depends on the corrected finite-word discounted-sum theorem. Different
multipliers with independent valuation vectors remain outside it.

**Use:** remove common-slope and common-positive-base affine candidates from the dimension-two
undecidability search.

**Next:** verify the corrected source theorem, reversal and final-letter constructions, and
negative-multiplier parity handling.

### D2-D04: Single-base affine stratum

**Kind:** decidable stratum  
**Evidence:** reported  
**Disposition:** active

For

```text
G_q^± = {z ↦ εqⁿz+t : ε∈{±1}, n∈ℤ, t∈ℤ[1/q]},
```

the report claims decidability of point incidence for every rational subset represented by a
finite automaton. It reduces the incidence set to a coset of an effectively cyclic stabilizer
and invokes Boolean emptiness for rational subsets of `BS(1,q)`, followed by an index-two sign
extension.

**Scope:** this is not a theorem for several independent rational bases. Recognition of the
ambient single-base condition and the coset construction require independent checking.

**Use:** reject any universality proposal confined to one `BS(1,q)`-type affine group.

**Next:** audit the stabilizer calculation, effective word construction, and transfer through
the index-two extension.

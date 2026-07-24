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
compilers, `G3` for the three-letter GPCP and `M₃(4)` frontier, and `D2` for the
dimension-two wall. The second component identifies the result class: `C` compiler, `O`
obstruction, `M` partial mechanism, `S` structure theorem, or `D` decidable stratum.
Numbers never change after assignment.

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
| [`MM-O01`](#mm-o01-all-placement-packing-rank) | obstruction | literal CHHN packing has exact rank six for every separator placement | reported | active |
| [`MM-O02`](#mm-o02-one-sided-phase-overlap) | obstruction | standard common-line phase fusion becomes one-sided | reported | parked |
| [`MM-O03`](#mm-o03-two-channel-boundary-tax) | obstruction | exact diagonal rank-two punctuation costs two states beyond Hankel rank | audited | active |
| [`MM-O04`](#mm-o04-uniform-rank-four-paired-series) | certificate | the paired scalar series has exact Hankel rank four | audited | active |
| [`MM-M01`](#mm-m01-off-diagonal-companion-interface) | partial mechanism | off-diagonal rank-two bridge has a complete fracture grammar | audited | stock |
| [`MM-M02`](#mm-m02-bordered-toggle) | partial mechanism | one lifted toggle has a stable rank-two third power | audited | parked |
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

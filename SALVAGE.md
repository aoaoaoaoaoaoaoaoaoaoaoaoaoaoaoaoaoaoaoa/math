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

The first namespace component identifies the campaign: `FC` for Frankl’s conjecture, `MM` for
general matrix-mortality compilers, `R32` for the rank-three binary frontier `M₃(2)`, `M4` for
the `M₄(3)` frontier, `G3` for the three-letter GPCP and `M₃(4)` frontier, and `D2` for the
dimension-two wall.
The second component identifies the result class: `C` compiler, `O` obstruction, `M` partial
mechanism, `S` structure theorem, or `D` decidable stratum. Numbers never change after
assignment.

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
| [`FC-S01`](#fc-s01-bidual-horn-density-dichotomy) | structure theorem | every bidual Horn function satisfies Frankl’s conjecture | audited | stock |
| [`FC-S02`](#fc-s02-downward-boundary-obstruction) | structure theorem | a low-density counterexample has large average downward boundary | audited | active |
| [`FC-S03`](#fc-s03-binary-semigroup-weighted-frankl-theorem) | structure theorem | weighted Frankl at homogeneous weight `1/2` | audited | active |
| [`FC-S04`](#fc-s04-cubical-unique-root-obstruction) | structure theorem | a counterexample complement has too many uniquely rooted sets | audited | active |
| [`FC-S05`](#fc-s05-exact-mean-yu-repair) | structure theorem | Yu's coupling reduction is valid after a monotone exact-mean lift | formalized | graduated |
| [`FC-S06`](#fc-s06-half-support-elimination) | structure theorem | entropy extremes may be confined to `[0,1/2]∪{1}` by a finite monotone kernel | formalized | graduated |
| [`FC-S07`](#fc-s07-low-orbit-contraction) | structure theorem | every surviving two-orbit extreme contracts to one of two bivariate families | formalized | graduated |
| [`FC-S08`](#fc-s08-diagonal-family-collapse) | structure theorem | every target-mean two-diagonal objective is bounded below by the point law | formalized | graduated |
| [`FC-S09`](#fc-s09-endpoint-core-contraction) | structure theorem | the high-conditional-mean endpoint core contracts to the centered curve | formalized | graduated |
| [`FC-S10`](#fc-s10-centered-endpoint-positivity) | analytic certificate | the saturated centered endpoint curve is positive through complement `21/25` | formalized | graduated |
| [`FC-S11`](#fc-s11-endpoint-boundary-certificate) | certificate | every canonical endpoint objective is nonnegative at `38234553336670271/10^17` | formalized | graduated |
| [`FC-S12`](#fc-s12-finite-entropy-bridge) | structure theorem | the finite affine coupling inequality implies strict union-closed abundance | formalized | graduated |
| [`FC-S13`](#fc-s13-rational-universal-abundance) | theorem | every nontrivial finite union-closed family has abundance greater than `38234553336670271/10^17` | formalized | graduated |
| [`FC-S14`](#fc-s14-blocker-pivot-normal-form) | structure theorem | every normalized counterexample is an exactly biased deletion blocker with a local pivot at each deleted set | audited | active |
| [`FC-M01`](#fc-m01-rational-yu-certificate) | partial mechanism | Arb independently checks the reduced gaps at `38234553336670271/10^17` | computational | active |
| [`FC-O01`](#fc-o01-homogeneous-tilt-persistence-fails) | obstruction | one-coordinate majority need not persist under homogeneous product tilt | audited | active |
| [`FC-O02`](#fc-o02-uniform-fiber-semigroup-ceiling) | obstruction | finite full-fiber semigroup lifts cannot beat the uniform entropy barrier | audited | stock |
| [`FC-O03`](#fc-o03-maximal-self-dual-completion-fails) | obstruction | maximal complement-free meet families need not be self-dual | audited | stock |
| [`FC-O04`](#fc-o04-affine-two-coupling-wall) | obstruction | the independent/max-entropy affine scheme cannot pass `c⋆=0.382345533366702721…` | audited | stock |
| [`MM-C01`](#mm-c01-unconditional-rank-one-separator) | compiler | arbitrary scalar zero to mortality by one outer product | formalized | graduated |
| [`MM-C02`](#mm-c02-common-image-restriction) | compiler | mortality-preserving restriction to a common image | formalized | graduated |
| [`MM-C03`](#mm-c03-scheduled-binary-compiler) | compiler | fixed-width tag strokes to a total two-letter scalar series | formalized | graduated |
| [`MM-C04`](#mm-c04-internal-word-sandwich-minimization) | compiler | internal low-rank words repair reachable/observable minimization | formalized | graduated |
| [`MM-O01`](#mm-o01-all-placement-packing-rank) | obstruction | literal CHHN packing has exact rank six for every separator placement | formalized | graduated |
| [`MM-O02`](#mm-o02-one-sided-phase-overlap) | obstruction | standard common-line phase fusion becomes one-sided | reported | parked |
| [`MM-O03`](#mm-o03-two-channel-boundary-tax) | obstruction | exact diagonal rank-two punctuation costs two states beyond Hankel rank | formalized | graduated |
| [`MM-O04`](#mm-o04-uniform-rank-four-paired-series) | certificate | the paired scalar series has exact Hankel rank four | formalized | graduated |
| [`MM-O05`](#mm-o05-width-three-scheduled-rank) | obstruction | the width-three scheduled series has exact rank five | formalized | graduated |
| [`MM-O06`](#mm-o06-pure-power-punctuation-obstruction) | obstruction | an exact isolated toggle cannot also punctuate through a pure power | audited | stock |
| [`MM-O07`](#mm-o07-setter-parameter-rigidity) | obstruction | source-boundary alignment fixes the setter parameter | audited | stock |
| [`MM-O08`](#mm-o08-full-algebra-prefix-pair) | obstruction | the exact ten-state prefix pair spans the full matrix algebra | formalized | graduated |
| [`MM-O09`](#mm-o09-two-state-ternary-prefix-image) | obstruction | a literal two-state ternary decoder has no five-state common-image restriction | audited | stock |
| [`MM-O10`](#mm-o10-additive-toggle-fusion-cycle) | obstruction | the normalized toggle-minus-separator ansatz has rank three at every power | audited | stock |
| [`MM-O11`](#mm-o11-full-algebra-paired-binary-family) | obstruction | the paired-binary mortality family spans the full six-state algebra | formalized | graduated |
| [`MM-O12`](#mm-o12-boundary-calibrated-setter-shear-is-gauge) | obstruction | boundary calibration erases the setter's side-basis shear from its separator and transfer | formalized | graduated |
| [`MM-O13`](#mm-o13-finite-positive-ray-setter-obstruction) | obstruction | arbitrary low/high setter blocks defeat every finite family of positive invariant rays | audited | graduated |
| [`MM-O14`](#mm-o14-decimal-setter-elliptic-product) | obstruction | two strictly hyperbolic decimal setter blocks have an elliptic product | formalized | graduated |
| [`MM-M01`](#mm-m01-off-diagonal-companion-interface) | partial mechanism | off-diagonal rank-two bridge has a complete fracture grammar | audited | stock |
| [`MM-M02`](#mm-m02-bordered-toggle) | partial mechanism | one lifted toggle has a stable rank-two third power | audited | parked |
| [`MM-M03`](#mm-m03-five-state-setter-punctuation) | partial mechanism | a mixed delimiter word is an exact internal rank-one separator | audited | closed |
| [`MM-M04`](#mm-m04-swapped-digit-setter) | partial mechanism | reversing the nonzero ternary digits preserves the setter and makes every transfer orientation preserving | audited | active |
| [`MM-M05`](#mm-m05-decimal-swapped-setter) | partial mechanism | radix ten with digits `0 ↦ 7`, `1 ↦ 5` preserves the setter and separates every real length shell | audited | active |
| [`MM-S01`](#mm-s01-square-run-projective-normal-form) | structure theorem | malformed square runs reduce to rational projective pole avoidance | audited | active |
| [`MM-S02`](#mm-s02-reset-zero-projective-peeling) | structure theorem | the ordinary reset cannot reach a false pole after one transfer | audited | active |
| [`MM-S03`](#mm-s03-centered-setter-carry) | structure theorem | setter orbits obey an integer valuation-and-suffix carry recurrence | audited | active |
| [`MM-S04`](#mm-s04-reverse-suffix-discrepancy) | structure theorem | setter resonance is a word-valued discrepancy queue with a bounded front fringe | audited | active |
| [`MM-S05`](#mm-s05-distinguished-boundary-beta-shell) | obstruction | the distinguished-boundary `β`-shell cannot reach a false pole | audited | active |
| [`MM-S06`](#mm-s06-valuation-one-divisor-normal-form) | structure theorem | every integral valuation-one pole lies on a finite family of divisor rays | audited | active |
| [`MM-S07`](#mm-s07-swapped-digit-finite-slope-reduction) | structure theorem | the swapped setter reduces integral valuation-one poles to finitely many primitive slopes | audited | active |
| [`MM-S08`](#mm-s08-swapped-distinguished-boundary-beta-shell) | obstruction | the swapped distinguished boundary cannot reach either single-erasure pole | audited | active |
| [`MM-S09`](#mm-s09-canonical-swapped-residue-cannot-hit-a-pole) | obstruction | the unavoidable all-erasure residue cannot meet a valuation-one pole at emitted widths | audited | active |
| [`MM-S10`](#mm-s10-swapped-target-suffix-sieve) | structure theorem | pole compatibility fixes `β+2` lower digits and excludes the residue `Δ=ρ−1` | audited | active |
| [`MM-S11`](#mm-s11-decimal-setter-hyperbolicity) | structure theorem | every decimal setter transfer is strictly hyperbolic | audited | active |
| [`MM-S12`](#mm-s12-decimal-two-prime-carry) | structure theorem | decimal setter poles obey an exact centered recurrence and coupled `2`/`5` trace balance | formalized | active |
| [`MM-S13`](#mm-s13-decimal-first-transfer-extinction) | obstruction | neither decimal centered reset reaches a false pole after one completed transfer | formalized core; audited assembly | active |
| [`MM-S14`](#mm-s14-ordinary-depth-two-shell-forest) | structure theorem | the ordinary depth-two decimal carry has only three resonant families and no B-to-B branch | formalized | active |
| [`MM-S15`](#mm-s15-ordinary-a-to-a-length-two-extinction) | obstruction | both ordinary A-to-A length-two resonances miss every admissible next pole | formalized | active |
| [`MM-S16`](#mm-s16-complete-ordinary-depth-two-extinction) | obstruction | no ordinary-reset orbit reaches a false pole after two completed transfers | formalized core; audited assembly | active |
| [`MM-S17`](#mm-s17-recursive-decimal-carrier) | structure theorem and obstruction | repeated A-shell resonances have an exact two-unit carrier whose last digits form a compatible period-two cycle | formalized | active |
| [`MM-S18`](#mm-s18-length-two-carrier-extinction) | obstruction | every consecutive multi-shell carrier transition has upper length at least three | formalized | active |
| [`R32-S01`](#r32-s01-split-return-normal-form) | structure theorem | rank-two cuts reduce one-unit binary mortality to a `2 × 2` return recurrence | formalized | graduated |
| [`R32-S02`](#r32-s02-two-plane-edge-square) | structure theorem | two rank-two generators are a two-vertex square of `2 × 2` edges | formalized | graduated |
| [`R32-O01`](#r32-o01-rank-one-profile-collapse) | obstruction | a rank-one generator reduces mortality to order-at-most-three scalar recurrence zeros | audited | stock |
| [`R32-S03`](#r32-s03-returnsquare-normal-form) | structure theorem | ReturnSquare mortality is an exact scalar bridge over positive returns | formalized | active |
| [`R32-O02`](#r32-o02-two-return-square-cage) | obstruction | no two positive ReturnSquare returns can vanish | formalized | graduated |
| [`R32-O03`](#r32-o03-reversible-stack-state-tax) | obstruction | literal reversible binary-stack returns require at least four exact states | formalized | graduated |
| [`R32-O04`](#r32-o04-quadratic-pencil-verification-collapse) | obstruction | three simple modes cannot reversibly verify squaring | formalized | graduated |
| [`R32-O05`](#r32-o05-jordan-parity-verifier-collapse) | obstruction | the rank-compatible parity-Jordan verifier is unique and immortal modulo seven | formalized | graduated |
| [`R32-D01`](#r32-d01-returnsquare-immortality-walls) | decidable stratum | nonnegative parameters and a uniform outer negative half-line are immortal | formalized | stock |
| [`R32-D02`](#r32-d02-prime-power-returnsquare-classification) | decidable stratum | prime-power ReturnSquare is mortal exactly at one-return resonances | formalized | graduated |
| [`R32-M01`](#r32-m01-generic-reverse-edge-compiler) | partial mechanism | projective incidence generically embeds into a compatible two-plane edge square | formalized | active |
| [`R32-M02`](#r32-m02-finite-quotient-sieve) | partial mechanism | finite monoid quotients give complete modular no-certificates for fixed candidates | formalized | active |
| [`R32-M03`](#r32-m03-two-scale-return-conversion) | partial mechanism | a minimal two-scale return pencil has nonresonant multi-return zeros | formalized | active |
| [`R32-M04`](#r32-m04-amalgamated-valuation-guard) | partial mechanism | one three-mode return family combines punctuation, wait verification, and a permanent trap | formalized | active |
| [`R32-S04`](#r32-s04-guarded-return-normal-form) | structure theorem | physical mortality is deterministic reachability for the ready-tail recurrence | formalized | active |
| [`R32-S05`](#r32-s05-prefix-shift-and-affine-residual) | structure theorem | each legal step decodes one p-adic prefix and updates the reciprocal residual affinely | formalized | active |
| [`R32-S06`](#r32-s06-resonance-localization) | structure theorem | every nonresonant continuation descends and every infinite ready chain resonates arbitrarily late | formalized | active |
| [`R32-O06`](#r32-o06-rational-affine-wait-rail-rigidity) | obstruction | no reduced rational chart supports a nontrivial affine wait rail at infinitely many prime powers | formalized | graduated |
| [`R32-O07`](#r32-o07-parity-immortality-and-maximal-isolation) | obstruction | odd reset resultants are immortal, while maximal Smith steps in the even stratum are isolated | formalized | graduated |
| [`R32-O08`](#r32-o08-recurrent-boundary-divisors-stay-reverse) | obstruction | outside fixed scale-reset support, a reverse-content divisor recurring in the next boundary remains wholly reverse | formalized | graduated |
| [`R32-O09`](#r32-o09-universal-boundary-reset-ball) | obstruction | a coefficient-prime reset ball excludes every depth-two guard below its explicit valuation wall | formalized | graduated |
| [`R32-O10`](#r32-o10-ready-order-breaking-bridge-ejection) | obstruction | a ready order-breaking bridge can eject a strict reset ball without auxiliary cancellation while amplifying denominator height | formalized | graduated |
| [`R32-O11`](#r32-o11-terminal-only-pole-contraction-is-a-decision-oracle) | obstruction | terminal-only contraction constants are pointwise vacuous; uniform effectivity is already a terminal bound | audited | graduated |
| [`R32-O12`](#r32-o12-periodic-shadow-obstruction) | obstruction | one fixed guard has arbitrarily long off-reset primitive corridors with nonmaximal Smith allocation and rising carried and Smith coordinate runs | formalized | graduated |
| [`R32-O13`](#r32-o13-renewal-graph-collapse-and-reset-pullback) | obstruction | every aligned macro consumes shadow depth, local bounded depth does not bound height, and reset ancestry is one exact pulled-back determinant | formalized | graduated |
| [`R32-O14`](#r32-o14-fixed-reset-geodesic-and-complete-endpoint-language) | structure theorem and obstruction | endpoint terminality is exact and every actual reset prefix has the same distinguished-prime kernel direction | formalized | graduated |
| [`R32-O15`](#r32-o15-fixed-support-toric-compiler-obstruction) | obstruction | rational fixed-prime counter charts with affine waits admit neither a nontrivial monomial instruction nor a repeatable control cycle | audited | graduated |
| [`R32-O16`](#r32-o16-irreducible-cubic-punctuation-collapse) | structure theorem and obstruction | cubic returns have an arbitrary-twist trace form; the pure fork is GPI₂ while non-pure unit bridges can be free | formalized core; audited strengthening | graduated |
| [`R32-O17`](#r32-o17-angular-emergent-primes-and-endpoint-compactness-no-go) | obstruction | terminal angular poles create primes outside determinant support and the wait gauge has nontrivial directional adelic height | formalized | graduated |
| [`R32-O18`](#r32-o18-finite-rational-radial-atlas-obstruction) | obstruction | every finite rational carry-mode atlas with fixed additive wait shifts is eventually periodic | audited | graduated |
| [`R32-S07`](#r32-s07-decoded-residual-address-normal-form) | structure theorem | mortality is finite inverse-address membership in disjoint rational p-adic branch spheres | formalized | active |
| [`R32-M05`](#r32-m05-cyclotomic-reset-or-cancellation-sieve) | partial mechanism | every primitive reduction either resets modulo a cyclotomic prime or swallows it in the common cancellation | formalized | active |
| [`R32-S08`](#r32-s08-cumulative-endpoint-recurrence) | structure theorem | cumulative endpoint pairs absorb every normalization scalar into one deterministic exact-division recurrence | formalized | active |
| [`R32-S09`](#r32-s09-complete-cancellation-law) | structure theorem | every base-coprime cancellation depth is the minimum of the terminal-defect and displacement depths | formalized | active |
| [`R32-S10`](#r32-s10-logarithmic-wait-and-height-envelope) | structure theorem | legal waits are logarithmic in primitive height and every reduced step is uniformly height-Lipschitz | formalized | active |
| [`R32-S11`](#r32-s11-primitive-factor-terminal-gate) | structure theorem | primitive cyclotomic factors either survive as reset witnesses or are swallowed with full multiplicity and charged to height | formalized | active |
| [`R32-S12`](#r32-s12-exact-order-projective-automata) | structure theorem | primitive divisors induce finite projective automata with exact swallowed-factor semantics | formalized | active |
| [`R32-S13`](#r32-s13-canonical-decoded-integral-lift) | structure theorem | every decoded rational path lifts canonically to primitive integral execution | formalized | active |
| [`R32-S14`](#r32-s14-drift-divisor-certificate-classification) | decidable stratum | drift-divisor certificates are exactly finite cyclic-orbit avoidance | formalized | active |
| [`R32-S15`](#r32-s15-finite-quotient-completeness) | obstruction | terminal exclusion is cancellation exclusion; synchronized prime products cannot amplify certificates | formalized | active |
| [`R32-S26`](#r32-s26-evaluation-frame-gauge-closure) | structure theorem and closure | the parameter-jet transition is an exact frame coboundary, and deep frame defect localizes to the reset shell | formalized | graduated |
| [`R32-S27`](#r32-s27-rational-gap-macro-pumping) | structure theorem and obstruction | exact branch similarity and rational height separation bound every noncyclic repetition of one fixed macro | formalized | active |
| [`R32-S28`](#r32-s28-terminal-endpoint-and-complementary-content) | structure theorem and obstruction | a terminal gauge exposes complementary forward/reverse contents and coefficient-prime immortality certificates | formalized | active |
| [`R32-S29`](#r32-s29-adelic-content-and-repeated-factor-budget) | structure theorem and obstruction | content-weighted height, full cyclotomic complement, exterior conservation, and arbitrary repeated-factor pumping share one calculus | formalized core; audited corollaries | active |
| [`R32-S30`](#r32-s30-fixed-cusp-and-record-ascent-calculus) | structure theorem and obstruction | cumulative endpoints form a fixed-cusp continued fraction; one primitive prequotient coordinate is carried by an exact generalized-continuant block | formalized | active |
| [`R32-S31`](#r32-s31-smith-decoder-and-maximal-cancellation-throat) | structure theorem and obstruction | a positive unimodular content decoder contracts nonmaximal branches, while one fixed basis makes every wait gauge a pure base-prime dilation | formalized | active |
| [`R32-S32`](#r32-s32-rank-two-punctuation-and-graph-removal) | structure theorem and reduction | compatible one-loop rank-two edge squares are intrinsic generic projective incidence; every other edge-rank pattern is decidable | audited | graduated |
| [`R32-S33`](#r32-s33-terminal-casoratian-and-two-sided-order-allocation) | structure theorem and decidable stratum | terminal normalization comes only from earlier branches, and exact orders persisting to either boundary have forced content orientation | formalized | active |
| [`R32-S34`](#r32-s34-exact-moving-prime-ledger) | structure theorem | outside fixed support, a divisor enters forward content exactly at simultaneous endpoint and branch-boundary divisibility | formalized | active |
| [`R32-S35`](#r32-s35-positive-projective-incidence-genericization) | reduction and normalization | arbitrary PI₂ is a bounded positive-prefix disjunction of GPI₂ instances, and every generic instance has `α=β=1` | formalized | active |
| [`R32-S36`](#r32-s36-guarded-affine-projective-incidence) | compiler | p-adic denominator poisoning gives an all-word guarded affine compiler into normalized GPI₂ | audited | active |
| [`R32-S37`](#r32-s37-normalized-shortcut-collatz-incidence) | reduction and arithmetic benchmark | fixed projectivities encode pointwise shortcut-Collatz reaches-one exactly inside normalized GPI₂ | formalized | active |
| [`R32-S38`](#r32-s38-jacobi-schedule-incidence) | structure theorem and obstruction | every wait schedule has one p-adic Jacobi tail, while reset realization is one rational continued-fraction incidence requiring unbounded history-dependent handoffs | formalized core; audited strengthening | active |
| [`R32-S39`](#r32-s39-reset-companion-and-bilateral-shadow) | structure theorem and obstruction | every first-hit terminal address has a canonical reset companion transmuting reverse content, but its bilateral shadow need not contract even once | formalized core; audited strengthening | active |
| [`R32-S40`](#r32-s40-binary-affine-syracuse-collapse) | structure theorem and obstruction | parity-selected affine reachability is decidable outside one mixed-slope signed Syracuse family, where only nonhomomorphic carry dynamics remains | audited | active |
| [`R32-S41`](#r32-s41-parabolic-rational-subset-normal-form) | reduction and obstruction | PI₂ is a parabolic rational-subset problem, already containing fixed-subset shortcut Collatz inside the rank-two affine cusp `ℤ[1/6]⋊ℤ²` | audited | active |
| [`R32-S42`](#r32-s42-non-pure-cubic-endpoints-and-false-waits) | structure theorem and obstruction | actual singular endpoints support free selected dynamics, but a clean one-singular family has an exact zero made solely from unselected unit waits | formalized core; audited strengthening | active |
| [`R32-O19`](#r32-o19-projective-queue-centralizer-obstruction) | obstruction | an injective homomorphic projective word store with finite controller cannot recurrently delete and append queue data | audited | graduated |
| [`R32-O20`](#r32-o20-transverse-reverse-reservoir) | obstruction | a lawful fixed projective cycle accumulates unbounded reverse 13-adic mass on its transverse eigenline | formalized | graduated |
| [`R32-O21`](#r32-o21-finite-image-positivity-collapse) | obstruction | every finite ambient image identifies the positive Collatz monoid with the whole generated group | formalized core; audited application | graduated |
| [`R32-O22`](#r32-o22-congruence-blind-free-orbit) | obstruction | one free trivial-stabilizer rational orbit misses a target that lies in its projective orbit modulo every integer | formalized | graduated |
| [`R32-D03`](#r32-d03-bounded-denominator-periodicity) | decidable stratum | every infinite legal rational guard orbit with bounded reduced denominators is eventually periodic | formalized | graduated |
| [`M4-C01`](#m4-c01-two-state-pushout-compiler) | compiler | binary deterministic two-state scalar control compiles to three `4 × 4` matrices | formalized | graduated |
| [`M4-O01`](#m4-o01-exact-toggle-fusion-leaves-an-immortal-core) | obstruction | exact local toggle fusion preserves a nonzero common anchor | formalized | graduated |
| [`M4-O02`](#m4-o02-two-private-state-phase-signature) | obstruction | two private quotient states cannot isolate one exceptional cyclic phase | formalized | graduated |
| [`M4-S01`](#m4-s01-odd-phase-macro-cut) | structure theorem | paired Neary roles inherit a rigid macro-stroke language | reported | active |
| [`M4-O03`](#m4-o03-closed-serialization-collapse) | obstruction | finite closed-token queue serialization is decidable | formalized | graduated |
| [`M4-O04`](#m4-o04-exact-internal-final-code-defect) | obstruction | distinct exact binary codes for one macro force commuting upper images | formalized | graduated |
| [`M4-O05`](#m4-o05-direct-two-state-first-return-recoding) | obstruction | the present four Neary roles have no direct two-state first-return code | reported | active |
| [`M4-M01`](#m4-m01-mixed-cube-root-punctuation) | partial mechanism | rational cube-root toggles reduce mixed punctuation to incidence equations | audited | parked |
| [`M4-M02`](#m4-m02-universal-monomial-cube-root-blade) | partial mechanism | a finite-order mixed word has uniform rank one but misses the source boundary | audited | parked |
| [`M4-O06`](#m4-o06-punctuation-image-annihilator) | obstruction | every punctuation context must preserve both rank-one boundary rays | formalized | graduated |
| [`M4-O07`](#m4-o07-closed-residue-monomial-obstruction) | obstruction | ternary closed residues cannot align the monomial blade column | audited | graduated |
| [`M4-M03`](#m4-m03-parabolic-blade-and-bridge-grammar) | partial mechanism | an open cube root has one singular atom and exact `2 × 2` bridge semantics | formalized | active |
| [`M4-M04`](#m4-m04-retuned-semantic-boundary) | partial mechanism | a retuned root realizes the Neary terminal language as one fixed physical minor | formalized | parked |
| [`M4-M05`](#m4-m05-boundary-guarded-homogeneous-punctuation) | partial mechanism | fixed-boundary binary free-group equality compiles to three integer `4 × 4` matrices | audited | active |
| [`M4-O08`](#m4-o08-residue-two-necessary-wall) | obstruction | every residue-zero or residue-one atom preserves a nonvanishing two-ray quotient | formalized | graduated |
| [`M4-S02`](#m4-s02-residue-zero-safe-bridge-cone) | structure theorem | every nonempty residue-zero regular safe bridge has negative determinant | audited | active |
| [`M4-S03`](#m4-s03-one-defect-phase-cut) | structure theorem | a lone residue-two defect can survive only between opposite safe residues | formalized | graduated |
| [`M4-O09`](#m4-o09-one-coordinate-exterior-fracture) | obstruction | the wait-free scalar exterior coordinate does not close on residue-one `c` atoms | audited | graduated |
| [`M4-O10`](#m4-o10-irrational-rotation-cone-fracture) | obstruction | one legal safe cycle excludes finite wall-separated cone certificates | audited | graduated |
| [`M4-C02`](#m4-c02-positive-overlap-queue-compiler) | compiler | promised positive two-frame queue acceptance compiles exactly to three integer `4 × 4` matrices | formalized | graduated |
| [`M4-O11`](#m4-o11-pure-deletion-necessity) | obstruction | every long accepted overlap queue needs a state-preserving role empty on both correspondence sides | formalized | graduated |
| [`M4-S04`](#m4-s04-arbitrary-switching-three-adic-exterior-flag) | structure theorem | every regular safe word preserves an oriented two-sector `3`-adic flag | formalized | active |
| [`M4-S05`](#m4-s05-deletion-scanner-normal-form) | structure theorem | promised overlap queues contract to three exact deletion scanners | audited | graduated |
| [`M4-S06`](#m4-s06-arbitrary-defect-bridge-grammar) | structure theorem | arbitrary defect skeletons and bridge walls reduce to one consecutive projective incidence | formalized | active |
| [`M4-S07`](#m4-s07-one-sided-wall-orbit-normal-form) | structure theorem | every consecutive wall incidence is one explicit exterior point-to-ray reachability problem | audited | active |
| [`M4-S08`](#m4-s08-safe-wall-transport-chamber) | structure theorem | incidence with a safe right wall forces the transported kernel into one strict phase-selected `3`-adic chamber | formalized | active |
| [`M4-S09`](#m4-s09-minimal-all-b-bad-run-exclusion) | obstruction | neither orientation of the shortest bad defect run can close when all three atoms are `b` | formalized | graduated |
| [`M4-S10`](#m4-s10-phase-zero-c-defect-exclusion) | obstruction | the `0|2|1` shortest bad run cannot close with a `c` defect and `b` endpoints | formalized | active |
| [`M4-S11`](#m4-s11-opposite-c-defect-cylinder-exclusion) | obstruction | the `1|2|0` shortest bad run cannot close with a `c` defect and `b` endpoints | formalized | active |
| [`M4-S12`](#m4-s12-residue-zero-c-endpoint-exclusion) | obstruction | a shortest bad run with a `b` defect cannot close when its residue-zero endpoint is `c` | formalized | active |
| [`M4-S13`](#m4-s13-residue-one-left-c-endpoint-exclusion) | obstruction | the `1|2|0` shortest bad run with a `b` defect cannot close when its left endpoint is `c` | formalized | active |
| [`M4-S14`](#m4-s14-uniform-all-b-defect-run-exclusion) | structure theorem and obstruction | every regular all-`b` safe/defect/safe bridge is nonsingular for an arbitrary residue-two run | formalized | active |
| [`M4-S15`](#m4-s15-opposite-double-c-endpoint-exclusion) | obstruction | the `1|2|0` shortest bad run with a `b` defect cannot close when both endpoints are `c` | formalized | active |
| [`M4-C03`](#m4-c03-zero-framed-binary-two-lag-compiler) | compiler | the principal scanner is literally binary context-2 Lag and compiles to `M₄(3)` | formalized | graduated |
| [`M4-D01`](#m4-d01-zero-framed-binary-two-lag-decision) | decidable stratum | the entire zero-framed binary context-2 Lag kernel has an exact syntactic classification | formalized | graduated |
| [`M4-D02`](#m4-d02-zero-framed-reset-scanner-decision) | decidable stratum | zero-run reduction contracts the reset scanner to a regular two-token quotient | audited | graduated |
| [`M4-D03`](#m4-d03-periodic-conjugate-scanner-decision) | decidable stratum | primitive conjugacy and an odd-gap quotient decide the final periodic scanner | audited | graduated |
| [`M4-O12`](#m4-o12-terminal-frame-morphism-obstruction) | obstruction | a fixed morphism cannot map a shared terminal to its own compulsory return frame | formalized | graduated |
| [`M4-O13`](#m4-o13-retuned-pseudo-terminal-obstruction) | obstruction | a malformed terminal context defeats every fixed-row annihilator on an admissible no-instance | formalized | graduated |
| [`M4-C04`](#m4-c04-original-mixed-gap-endpoint-compiler) | conditional compiler | two explicit mixed-gap ray equations recognize the four-parameter Neary terminal equation | formalized | parked |
| [`M4-O14`](#m4-o14-original-semantic-endpoint-obstruction) | obstruction | fixed rays fail on the formal terminal plane and complete-gap contexts miss both compiler rays | formalized | graduated |
| [`M4-O15`](#m4-o15-original-pseudo-terminal-endpoint-obstruction) | obstruction | one regular gap-thirty pseudo-production defeats every instantiation of the original endpoint compiler | formalized | graduated |
| [`M4-O16`](#m4-o16-one-complement-spectral-checksum-obstruction) | obstruction | every rational one-complement cube root is resonant with affine aliases or yields an immortal family | audited | graduated |
| [`M4-O17`](#m4-o17-positive-nielsen-basis-obstruction) | obstruction | Carvalho's positive Nielsen basis has trivial positive-monoid intersection with every halting equalizer | audited | graduated |
| [`G3-O01`](#g3-o01-four-role-macro-irreducibility) | obstruction | exact nonerasing macros cannot reduce the four source roles to three letters | formalized | graduated |
| [`G3-O08`](#g3-o08-erasing-and-stationary-closed-block-obstruction) | obstruction | paired Parikh rank kills erasing exact macros and stationary closed-return block encoders | audited; formalized core | graduated |
| [`G3-S01`](#g3-s01-shift-equivariant-zero-incidence) | structure theorem | same-zero state dimension is equivariant projective incidence dimension | audited | active |
| [`G3-S02`](#g3-s02-rank-two-kernel-bifurcation) | structure theorem | common kernels erase route differences; transverse fibres retain one bilinear survivor | formalized | active |
| [`G3-O18`](#g3-o18-transverse-minimum-body-countermodel) | fixed-subclass compiler | distinct rank-two kernels encode every paired history and exactly recognize all minimum bodies | formalized | graduated |
| [`G3-O02`](#g3-o02-rational-phase-fracture) | obstruction | a mortal paired instance has no rational phase-state same-zero compression | audited | stock |
| [`G3-O03`](#g3-o03-history-sensitive-minimal-body-fracture) | obstruction | minimal bodies admit an exact history-sensitive three-state same-zero compiler | formalized | graduated |
| [`G3-O04`](#g3-o04-expanding-affine-history-no-go) | obstruction | finite-mode expanding one-coordinate history has decidable target reachability | audited | graduated |
| [`G3-O05`](#g3-o05-cancellative-projective-state-tax) | obstruction | inverse-saturated two-side projective dynamics need four states | audited | graduated |
| [`G3-O11`](#g3-o11-positive-shifts-do-not-force-saturation) | obstruction | positive common shifts need not be backward cancellative | formalized | graduated |
| [`G3-O12`](#g3-o12-positive-reset-dimension-tax) | obstruction | projectively full residual-local reset codes identify `q` with `ε` | formalized | graduated |
| [`G3-O13`](#g3-o13-rational-serializer-pumping) | obstruction | finite-control exact serialization pumps to an impossible stationary return | audited; formalized core | graduated |
| [`G3-D01`](#g3-d01-bounded-prefix-residuals) | decidable stratum | a supplied bound on every accepting prefix residual gives a finite decision graph | audited | stock |
| [`G3-D02`](#g3-d02-virtually-cyclic-prefix-discrepancy) | decidable stratum | finite-mode capped periodic residual rays reduce to one-counter reachability | audited; formalized core | graduated |
| [`G3-D03`](#g3-d03-one-sided-corrected-drift) | decidable stratum | one-sided positive weighted drift bounds every accepting residual | audited; formalized core | graduated |
| [`G3-D04`](#g3-d04-priority-affine-residual-atlas) | decidable stratum | finite-dimensional proper affine residuals with nested priority guards reduce to VASSnz | audited; formalized core | graduated |
| [`G3-D05`](#g3-d05-priority-triangular-transfer-atlas) | decidable stratum | fixed-priority destructive transfer and fanout reduce to VASSnz drain stages | audited; formalized core | graduated |
| [`G3-D06`](#g3-d06-functional-phase-transfer-guillotine) | decidable stratum | three functional positive phase transfers always admit one-sided drift | audited; formalized core | graduated |
| [`G3-D07`](#g3-d07-pure-phase-fork-closure) | decidable stratum | complete pure-phase forks reduce to closure reachability for an additive semilinear relation | audited; formalized arithmetic core | graduated |
| [`G3-C03`](#g3-c03-endpoint-prefix-compiler) | compiler | endpoint-forcing three-production normal systems compile directly to `GPCP(3)` | formalized | active |
| [`G3-C04`](#g3-c04-head-separated-endpoint-debt) | compiler criterion | a fresh output head makes every endpoint witness causally lawful | formalized | active |
| [`G3-O06`](#g3-o06-periodic-ray-completion-and-branching-fracture) | compiler and obstruction | `bcbb` has an exact three-state periodic compiler, while `bcbc` defeats every single affine positional section | formalized | graduated |
| [`G3-O07`](#g3-o07-near-fork-carry-collision) | obstruction | a terminal and nonterminal `bcbc` near-fork collide under the entire one-coordinate phase-line carry family | formalized | graduated |
| [`G3-C02`](#g3-c02-fixed-bcbc-singular-recognizer) | fixed-instance compiler | a transient guard over one affine carry recognizes the complete `bcbc` language | audited, with formalized core | graduated |
| [`G3-C05`](#g3-c05-equal-length-mixed-branching-recognizer) | fixed-instance compiler | three singular controls recognize the complete `bcbcbb` paired zero language | formalized | graduated |
| [`G3-M02`](#g3-m02-square-root-punctuation-fracture) | partial mechanism | a rank-two square root gives an exact `SS`-free mortality grammar | formalized | closed |
| [`G3-O10`](#g3-o10-square-root-boundary-saturation) | obstruction | every nondegenerate rank-one square root preserves boundary coefficient zeros | formalized | graduated |
| [`G3-M01`](#g3-m01-free-group-discrepancy-engine) | partial mechanism | Carvalho's transducer gives an all-word marker-tail equation and a cyclic exponent-one equalizer | audited | active |
| [`G3-M03`](#g3-m03-three-positive-affine-exponent-cover) | partial mechanism | three positive letters cover every affine first-exponent slice exactly | formalized | active |
| [`G3-O19`](#g3-o19-correlated-affine-slice-density) | obstruction | the coarse Carvalho promises permit a correlated graph whose every exponent slice is Zariski dense | audited | graduated |
| [`G3-O21`](#g3-o21-actual-carvalho-slice-density) | obstruction | every fixed-character slice of Carvalho's actual program graph is Zariski dense in `PSL₂²` | audited | graduated |
| [`G3-O22`](#g3-o22-invertible-fibre-span-rigidity) | structural reduction | invertible spelling fibres form computable line or plane group orbits | formalized core | graduated |
| [`G3-O23`](#g3-o23-singular-triangle-carrier-collapse) | structural reduction | every singular saturated three-state triangle carrier collapses effectively to an invertible two-state carrier | formalized core | graduated |
| [`G3-O24`](#g3-o24-directed-dyck-absorption-collapse) | obstruction | faithful finite-dimensional absorption of one-way Dyck cancellation forces the reverse cancellation | formalized core | graduated |
| [`G3-O20`](#g3-o20-consecutive-repeat-tail-closure) | obstruction | two consecutive solutions of a fixed-boundary one-block pump force every later exponent | formalized | graduated |
| [`G3-O09`](#g3-o09-quotient-blind-positive-boundary-collapse) | obstruction | all-loop-complete group-factorizing boundaries accept a nonempty identity spelling | formalized core | graduated |
| [`G3-O14`](#g3-o14-positive-cancellation-spelling-dichotomy) | obstruction | finite reversible spelling pumps, while singular one-coordinate spelling absorbs identity factors | formalized | graduated |
| [`G3-O15`](#g3-o15-triangle-normal-form-rank-six) | obstruction | a standalone same-zero guard for triangle-irreducible spellings needs six states | formalized | graduated |
| [`G3-O16`](#g3-o16-full-augmented-pair-dimension-tax) | obstruction | an independent `F×F×ℤ` detector cannot act faithfully in three dimensions | audited | graduated |
| [`G3-O17`](#g3-o17-paired-inverse-chamber) | obstruction | protected two-turn inverse states have no positive future in the actual paired residual chambers | formalized | graduated |
| [`D2-S01`](#d2-s01-projective-hard-core) | structure theorem | `M₂(3)` is equivalent to two-generator projective incidence | audited | active |
| [`D2-S02`](#d2-s02-monotone-affine-path-form) | structure theorem | normalized affine words form monotone exponent paths | audited | stock |
| [`D2-S04`](#d2-s04-real-trap-ternary-predecessor-nucleus) | structure theorem | real-trap positivity cuts every one-step reverse shell fan to a sharp computable window of three waits | formalized | active |
| [`D2-S05`](#d2-s05-fixed-source-real-trap-rays) | structure theorem | every real-trap source has a one-step orbit on one computable normalized-mantissa ray | formalized | active |
| [`D2-S06`](#d2-s06-spectator-prime-denominator-skeleton) | structure theorem | every denominator exponent away from `2`, `3`, and `5` is invariant through shell prefixes and first exits | formalized | active |
| [`D2-S07`](#d2-s07-period-ten-shell-guard) | structure theorem | the one-step shell guard has period ten, while a length-`ℓ` tail has sharp uniform precision exponent `ℓ+1` | formalized | active |
| [`D2-S08`](#d2-s08-twelve-class-target-depth-collapse) | structure theorem | guarded nonempty real-trap reachability reduces to twelve canonical target-depth classes while preserving the exact mantissa | formalized | active |
| [`D2-S09`](#d2-s09-centered-lower-mantissa-recurrence) | structure theorem | the exact reverse mantissa address has one centered lower branch whose sole secondary cancellation wall is `v₂(b)=1` | formalized | active |
| [`D2-D01`](#d2-d01-projectively-unimodular-stratum) | decidable stratum | projectively unimodular hard-core instances are decidable | audited | stock |
| [`D2-D02`](#d2-d02-invariant-pair-stratum) | decidable stratum | invariant projective pairs reduce to abelian-by-`C₂` reachability | reported | active |
| [`D2-D03`](#d2-d03-common-multiplier-stratum) | decidable stratum | rational affine maps with one multiplier are decidable under regular control | reported | active |
| [`D2-D04`](#d2-d04-single-base-affine-stratum) | decidable stratum | rational-subset incidence in `G_q^±` is decidable | reported | active |
| [`D2-D05`](#d2-d05-prescribed-translation-count) | decidable stratum | prescribed translated-letter count is decidable by rational-base carries | audited | stock |
| [`D2-D06`](#d2-d06-private-prime-peeling) | decidable stratum | a private multiplier prime decides every noncritical endpoint shell | audited | stock |
| [`D2-D07`](#d2-d07-bounded-valuation-orthants) | decidable stratum | bounded cooriented affine families have finite successful state spaces | audited | stock |
| [`D2-D10`](#d2-d10-real-trap-exterior) | decidable stratum | the mixed-prime shell has invariant real trap `[1/5,1/2]`; every exterior target imposes a computable translated-letter bound | formalized reduction; audited decision corollary | stock |
| [`D2-M01`](#d2-m01-benchmark-critical-shell) | partial mechanism | the mixed-prime benchmark reduces generically to one guarded `5`-adic shell | audited | active |
| [`D2-O01`](#d2-o01-canonical-collatz-reachability-is-not-automatic) | obstruction | full generalized-Collatz reachability is not synchronously recognizable in its canonical base | external theorem | active |
| [`D2-O02`](#d2-o02-critical-shell-periodic-saturation) | obstruction and rewrite seed | every nonempty finite wait schedule has a rational all-unit cycle; normalized nonfreeness persists under every generator scaling, while its odd family is a two-seed cancellative pump and the positive finite basis is complete only through length 30 | formalized core; audited strengthening | active |
| [`D2-O03`](#d2-o03-fixed-source-adjacent-saturation) | obstruction and fixed-source family | the source `43/24` supports infinitely many accepted chamber-contained adjacent collisions on the complementary target pole; the targets are distinct and membership in their ray is decidable | formalized | active |
| [`D2-O04`](#d2-o04-forced-exit-surface) | obstruction and decidable continuation cone | every next block leaves the accepted `43/24` collision ray at valuation minus one; target valuation fixes every post-exit length, making the whole controlled cone decidable | formalized reduction; audited decision corollary | active |
| [`D2-O05`](#d2-o05-universal-exit-suffix-collapse) | structure theorem and decidable suffix reduction | after any critical-shell exit, a fixed target permits at most two nonempty suffix lengths; the remaining master obstruction lies before or at the exit | formalized reduction; audited decision corollary | active |
| [`D2-O06`](#d2-o06-real-trap-backward-saturation) | obstruction and backward saturation | every rational `5`-adic unit target in the real trap has guarded rational predecessor schedules of every block length, with the source allowed to vary | formalized | active |
| [`D2-O07`](#d2-o07-guarded-real-pole-reset) | obstruction and depth reset | the deepest real-trap branch reaches every sufficiently deep Archimedean band, and an explicit unbounded subfamily survives the `5`-adic guard | formalized | active |

## Frankl Conjecture

### FC-S01: Bidual-Horn density dichotomy

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** stock

Let `h:2^[n]→{0,1}` be bidual Horn, with false points `F` and true points `T`. Then
`F` is intersection-closed and `T` is union-closed. If `|T|≥2^(n−1)`, Karpas’s
half-cube theorem gives an abundant coordinate in `T`, hence a rare coordinate in `F`.
Otherwise `|F|>2^(n−1)` and the set-complement family

```text
F* = {[n]∖A : A∈F}
```

is union-closed. An abundant coordinate in `F*` is rare in `F`. Therefore every bidual
Horn function with at least two false points satisfies Frankl’s conjecture; self-dual Horn
functions are an immediate subclass.

**Scope:** this proves the conjecture on the bidual class. It does not transform an arbitrary
Horn function into a bidual one, improve the universal abundance constant, or settle Frankl’s
conjecture.

**Use:** remove bidual and self-dual Horn functions from any proposed minimal counterexample
class. Any completion-based attack must preserve a counterexample while entering a class now
known to be impossible.

**Artifact:** [`audits/frankl-bidual-horn-density-2026-08-08.md`](audits/frankl-bidual-horn-density-2026-08-08.md#bidual-horn-theorem).

### FC-S02: Downward boundary obstruction

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let `C⊆2^[n]`, `n≥2`, have density `0<ρ≤1/2`. If every coordinate occurs in
strictly more than half of `C`, then its average downward external degree satisfies

```text
(1/|C|) Σ_{A∈C} |{i∈A : A∖{i}∉C}| > 2(1−ρ).
```

The proof uses the level-zero and level-one Walsh coefficients of `1−2·1_C`, Parseval,
and exact directional edge counts. It strengthens the `≤1` pointwise boundary condition
behind Karpas’s theorem whenever `ρ<1/2`.

**Scope:** the theorem is an obstruction, not a closure-derived upper bound. An arbitrary
intersection-closed family need not have sparse downward boundary.

**Use:** seek an independent meet-semilattice, lattice-minimality, or compression argument
forcing average downward degree at most `2(1−ρ)`.

**Artifact:** [`audits/frankl-bidual-horn-density-2026-08-08.md`](audits/frankl-bidual-horn-density-2026-08-08.md#boundary-theorem).

**Next:** express the downward boundary through meet-irreducibles or canonical implications and
test whether minimal counterexamples force a strict upper bound.

### FC-O01: Homogeneous tilt persistence fails

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

There is a 17-coordinate, nine-set intersection-closed family `R` with one coordinate `i`
occurring in `5/9` of its sets, yet under homogeneous product tilt `p=x/(1+x)` at
`x=11/10`,

```text
Pr_p(i∈A | A∈R) < 1−p.
```

Its exact residual weight polynomials are

```text
P(x)=(1+x)^2+x^16,
Q(x)=1+x^12(1+2x),
Q(11/10)−(11/10)^2P(11/10)
  = 146953492014968519/10^18 > 0.
```

**Scope:** other coordinates of `R` are rare, so this does not refute persistence under the
joint assumption that every coordinate is initially frequent. It refutes any coordinatewise
lemma based only on intersection closure and that coordinate’s uniform majority.

**Use:** a Gendler product-measure attack must exploit all strict-majority inequalities
simultaneously or choose coordinate parameters adaptively.

**Artifact:** [`audits/frankl-bidual-horn-density-2026-08-08.md`](audits/frankl-bidual-horn-density-2026-08-08.md#exact-failure-of-homogeneous-one-coordinate-persistence).

**Next:** derive the Jacobian of all conditional biases under coordinatewise log-odds and test
whether a separating direction exists whenever every uniform bias is positive.

### FC-S03: Binary semigroup weighted Frankl theorem

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

For every probability measure `μ` on `[0,1]` of mean `0<φ<1/2`, Zargar's
binary nilpotent entropy functional obeys the sharp lower bound

```text
F₂,₁(μ) ≥ φ(1−2φ) log 2 > 0.
```

Consequently, every finite intersection-closed family `C` with at least two members has a
coordinate `i` such that

```text
Σ_{A∈C, i∉A} 2^(−|A|)
  > (1/2) Σ_{A∈C} 2^(−|A|).
```

Dually, a nontrivial union-closed family has a coordinate strictly abundant under weights
`2^|A|`. Strictness follows because equality in the total entropy comparison would make the
uniform lifted law stationary under multiplication, while the one-coordinate stationarity
equations in `{0,ε,1}` force every base coordinate to be constant.

**Scope:** this closes the `k=2,m=1` analytic seam isolated by Zargar. It is a theorem at
nonuniform weight `1/2`, not at uniform weight `1`, and it does not improve the universal
uniform abundance constant.

**Use:** anchor a homogeneous or coordinatewise tilt at an exact half-frequency endpoint. A
universal attack must transport the simultaneous uniform strict-majority inequalities to this
endpoint or extract a contradiction at the first coordinate crossing.

**Artifact:**
[`audits/frankl-binary-semigroup-kernel-2026-08-08.md`](audits/frankl-binary-semigroup-kernel-2026-08-08.md#weighted-frankl-consequence).

**Next:** analyze a minimal counterexample at the first homogeneous crossing
`t∈(1/2,1)` and determine whether meet-irreducibility or coordinatewise tilts force a second
balanced coordinate.

### FC-S04: Cubical unique-root obstruction

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Normalize a hypothetical union-closed counterexample `G⊆2^[n]` by adjoining `∅`, set
`α=|G|/2^n`, and let `F=2^[n]∖G`. If `q(F)` counts members of the simply rooted
family `F` having exactly one root, then

```text
q(F)=D↓(F)>2α|F|.
```

The equality is exact: a member has a downward external edge precisely when its Bhasin root
set is a singleton. Set complementation transports this boundary to the small
intersection-closed family, where `FC-S02` supplies the strict lower bound. Moreover,
`X(F∪{∅})` is contractible; Bhasin's acyclicity induction upgrades because every piece and
intersection in the gluing proof is contractible.

**Scope:** contractibility or simple rootedness alone does not force the contrary upper bound.
For `G={∅}` in an ambient `n`-cube, `q(F)=n` while `2α|F|<2`. Strict coordinate
majorities, separation, or minimality must enter any successful estimate.

**Use:** translate the Fourier target into cubical language. Seek a Morse, Laplacian, or root
overlap inequality proving `q(F)≤2α|F|` for a normalized counterexample.

**Artifact:**
[`audits/frankl-cubical-unique-roots-2026-08-08.md`](audits/frankl-cubical-unique-roots-2026-08-08.md#counterexample-inequality).

**Next:** express `q(F)` through intersections of the root down-sets and test inequalities that
also use every strict coordinate majority; do not pursue homology alone.

### FC-S05: Exact-mean Yu repair

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For a finite symmetric coupling `P` whose marginal has mean `s<t`, mix in
`γ=(t−s)/(1−s)` mass at `(1,1)`. The new coupling has exact marginal mean `t`; its
independent entropy term is multiplied by `(1−γ)²`, while its marginal and dependent
entropy terms are multiplied by `1−γ`. The objective ratio cannot increase. Yu's cited
concavity theorem may therefore be applied only after this lift, on the fixed-mean slice where
it is valid. A negative gap then occurs at a symmetric extreme supported on at most two orbit
laws.

**Scope:** this repairs the functional reduction in Yu's Proposition 1 for finite couplings. It
does not certify the remaining extreme-point minimum or vindicate global concavity, which is
false.

**Use:** begin every Yu/Sawin finite optimization at exact marginal mean. Do not reuse the
printed global-concavity sentence.

**Artifact:**
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#repairing-the-exact-mean-reduction).

**Formalization:** `Frankl/MeanLift.lean` checks the exact-mean lift algebra.
`Frankl/FixedMeanConcavity.lean` proves the fixed-slice entropy concavity directly from its
power series, while `Frankl/MomentReduction.lean` and `Frankl/OrbitLaw.lean` give the elementary
finite extreme-point reduction and symmetric-orbit realization. The surviving law is formally
either one exact-mean orbit or two orbit means strictly straddling the target, with their masses
identified exactly. `Frankl/OrbitMeanLift.lean` realizes the `(1,1)` lift on symmetric orbit
laws, proves the quadratic/linear/linear scaling of the three entropy terms, and composes the
lift with the extreme reduction in one theorem.

### FC-S06: Half-support elimination

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For each marginal atom `y∈(1/2,1)`, the kernel

```text
y ↦ 2(1−y)δ_(1/2)+(2y−1)δ_1
```

preserves its mean and does not increase the max-entropy coupling cost pointwise. At the current
rational target and affine parameters, bilinear polarization gives the exact finite identity

```text
A(μ′)−A(μ)=λ(E_μg+E_μ′g).
```

Concavity and monotonicity of `g`, followed by the checked scalar inequality
`2g(t)<wg(0)`, show that the replacement cannot increase the independent-minus-marginal gap.
Iterating removes every support point strictly between one half and one.

**Scope:** the scalar derivative signs are specific to the current rational parameters,
though the kernel and pointwise dependent-cost inequality are general. This repairs Cambie's
infinitesimal argument without an uncontrolled `O(η)` term.

**Use:** classify exact-mean extremes using only `[0,1/2]∪{1}` before numerical work.

**Artifact:**
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#removing-support-above-one-half).

**Formalization:** `Frankl/HalfSupport.lean` checks the scalar sign, global shape of `g`, and
pointwise dependent-cost contraction. `Frankl/FiniteLaw.lean` checks the finite Jensen and
polarization argument. `Frankl/OrbitHalfSupport.lean` constructs the simultaneous finite
coordinatewise pushforward of an arbitrary symmetric orbit law, proves exact mass and mean
preservation, aggregates all source kernels without iteration, proves dependent-entropy and
complete-gap monotonicity, and re-reduces the transformed law to an identified restricted
extreme.

### FC-S07: Low-orbit contraction

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For `f_q(x)=h(x+q−xq)` on the low square,

```text
|f_q″(x)|/|h″(x)| ≤ (1−q)/(1+q) ≤ 1−4q/3.
```

A separate Bernstein-positive polynomial proves that contracting a symmetric low orbit to its
mean increases independent join entropy by no more than marginal entropy. In a two-low-orbit
extreme, contract the lower-mean orbit first and the upper-mean orbit second. Their normalized
costs are at most `1` and `2−8t/3<1`.

If the upper orbit contains `1`, the lower orbit contracts with cost at most one. Since the
dependent term is fixed by each low orbit's mean, every restricted extreme reduces to either a
diagonal–diagonal or diagonal–endpoint law.

**Scope:** the theorem concerns symmetric extremes supported on `[0,1/2]∪{1}` at the current
exact rational target. The curvature lemmas themselves have the wider domains stated in the
audit.

**Use:** replace Yu's four geometric orbit coordinates by the two bivariate objectives in
`FC-M01`.

**Artifact:**
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#contracting-the-surviving-low-orbits).

**Formalization:** `Frankl/Entropy.lean`, `Frankl/OrbitContraction.lean`,
`Frankl/SelfPair.lean`, and `Frankl/TwoOrbit.lean` check the curvature comparison, Bernstein
polynomial, both self-pair bounds, exact mean weights, and ordered two-step contraction.
`Frankl/OrbitCollapse.lean` expands the actual canonical low–low and low–endpoint orbit laws,
proves their exact marginal and independent entropy differences, proves the dependent term is
fixed, and lifts the scalar deficit estimates to monotonicity of the complete strict Yu gap.
`Frankl/OrbitReindex.lean` and `Frankl/OrbitClassification.lean` reindex and sort arbitrary
identified extremes, classify their half-supported coordinates, contract the one- and two-orbit
cases, and compose the entire bounded-mean analytic reduction to the diagonal,
diagonal–diagonal, or diagonal–endpoint objective family.

### FC-S08: Diagonal-family collapse

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

Let a binary law on `[0,1/2]` have masses `ℓ,u`, support `a,b`, and mean `t`. If
`Δ=h(t)−ℓh(a)−uh(b)`, sequential join-curvature comparison gives

```text
h(t∨t)−E h(X∨Y)
  ≤ ((1−t)/(1+t) + 1−4t/3)Δ.
```

For the capped diagonal cost, the function

```text
g(x)=2h(x)−h(min(2x,1/2))
```

lies below its affine support at `t`. Below `1/4`, this follows from convexity of
`2h(x)−h(2x)` and its endpoint values; above `1/4`, it is the ordinary entropy tangent
inequality. Averaging the support proves

```text
log 2−E h(min(2X,1/2)) ≤ 2Δ.
```

At the current `t`, dependent share `α`, and strict slack `ε`, exact rational arithmetic proves

```text
(1−α)((1−t)/(1+t)+1−4t/3)+2α < 1+ε.
```

Hence every two-diagonal objective is at least the point-mass objective. The centered-curve
proof gives the latter a strict positive lower bound. Both diagonal certificate rectangles are
therefore discharged analytically, without a subdivision verdict.

**Scope:** this eliminates the diagonal–diagonal family only. `FC-S11` discharges the
diagonal–endpoint surface, and `FC-S12` supplies the union-closed implication.

**Use:** remove two of the three compact certificate regions and concentrate all numerical or
analytic work on the endpoint family.

**Artifact:** `Frankl/DiagonalObjective.lean` and
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#analytic-collapse-of-the-diagonal-family).

### FC-S09: Endpoint-core contraction

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For the diagonal–endpoint certificate coordinates `(a,q)`, condition away the deterministic
endpoint coordinate. The remaining low law has mean

```text
r = (a(1−2t)+tq)/(1+q−a−t).
```

If `a≥1/4`, `0≤q≤1/2`, and `r≥13/50`, both the original diagonal atom and the centered
atom have saturated dependent cost `log 2`. The diagonal Jensen-deficit estimate then shows
that replacing the conditional low law by its point mass at `r` cannot increase Yu's gap. The
coefficient is largest at `r=13/50`, where

```text
(193/200)((1−t)/(1−r))((1−r)/(1+r)+1−4r/3)
  = 5826723461/5827500000
  < 10000001/10000000
```

with exact margin `3108487/23310000000`. Thus the full two-dimensional core is bounded below
by the centered curve `q=a`.

**Scope:** this was the first core contraction at the former target. The support-aware theorem in
`FC-S11` strictly subsumes its high-`a` role at `76469/200000`.

**Use:** retain its Jensen-deficit architecture; use `FC-S11` for the current bound.

**Artifact:** `Frankl/EndpointObjective.lean` and
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#endpoint-core-contraction).

### FC-S10: Centered endpoint positivity

**Kind:** analytic certificate
**Evidence:** formalized
**Disposition:** graduated

In complement coordinates `y=1−r`, multiply the saturated centered objective by `y²` and write

```text
K(y)=(1−α)(1−t)²h(y²)+α(2(1−t)y−y²)log 2−(1+ε)(1−t)yh(y).
```

At

```text
t=38234553336670271/10^17,
α=356069804374481/10^16,
ε=10⁻¹⁸,
```

the sign of the third derivative is governed by

```text
P(y)=4(1−α)(1−t)²(y²+1)
     +(1+ε)(1−t)(y³−3y−2).
```

The polynomial `P` is increasing on `1−t≤y≤21/25`. Thus `K'''` changes sign at most once,
from positive to negative, and `K''` reaches its minimum at an endpoint. Four-term atanh
enclosures prove `K''(1−t)>0` and `K''(21/25)>0`, so `K` is convex on the whole interval. At
`y₀=670545261496963/10^15`, 72-term rational logarithm enclosures give
`K(y₀)>1/(25·10^16)` and `0<K′(y₀)<1/(7·10^17)`; its supporting line remains positive.

The exact identity

```text
K(1−r)=(1−r)² G̃(r)
```

then proves positivity of the saturated centered objective for `4/25≤r≤t`. This lower endpoint
is exactly strong enough for every conditional center produced by `a≥1/4`.

**Scope:** this is the one-dimensional analytic component of the high-endpoint proof. It does
not cover `a≤1/4`, where the static low-rectangle certificate remains necessary.

**Use:** combine with the support-aware coefficient in `Frankl/SupportEndpoint.lean`; no
high-`a` residual subdivision is needed.

**Artifact:** `Frankl/CenteredEndpoint.lean` and
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#centered-endpoint-curve).

### FC-S11: Endpoint boundary certificate

**Kind:** certificate
**Evidence:** formalized
**Disposition:** graduated

Half support forces the endpoint coordinate into the exact dichotomy `q≤1/2 ∨ q=1`; the
apparent strip `1/2<q<1` is not realizable. On the whole high rectangle

```text
1/4≤a≤38234553336670271/10^17,    0≤q≤1/2,
```

condition away the deterministic coordinate, put `M=max(a,q)`, and compare the independent
loss with support-aware coefficient

```text
Ψ(M,r)=(1−α)(1−t)
  (M/(M+r−Mr)+(1−4r/3)/(1−r)).
```

The coefficient decreases in `r`. Splitting at `q≤a` and `a≤q` reduces it to two exact
rational polynomial signs, proving `Ψ≤1+10⁻¹⁸`. `FC-S10` then gives strict positivity throughout
the high rectangle. When `q=1`, replacing its deterministic endpoint atom by the symmetric
endpoint orbit at `q=a` preserves the marginal law and independent entropy while decreasing
the dependent entropy term. Thus the `q=1` objective is bounded below by a point already in the
low or high rectangle. Static reflected subdivisions remain only on

```text
0≤a≤1/4,       0≤q≤1/2.
```

Each generated leaf contains a closed rational subdivision term and a definitional equality
showing that the proved checker returns success. Coverage theorems compose them without a
runtime decision procedure. Together with `FC-S08` through `FC-S10`, this proves
`orbitYuGap_nonneg` for every finite symmetric orbit law of mean at most
`t=38234553336670271/10^17`.

**Scope:** this is the complete finite-coupling objective inequality at the displayed rational
parameters. `FC-S12` supplies the independent bridge to union-closed families.

**Use:** further parameter work need only regenerate the low rectangle while rechecking the
analytic scalar inequalities.

**Artifact:** `Frankl/OrbitClassification.lean`, `Frankl/EndpointCertificate.lean`,
`Frankl/EndpointTrace/`, `Frankl/EndpointBoundary.lean`, and
`tools/GenerateFranklEndpointTrace.lean`; see
[`audits/frankl-rational-abundance-2026-08-10.md`](audits/frankl-rational-abundance-2026-08-10.md#endpoint-closure).

### FC-S12: Finite entropy bridge

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For a finite law on an iterated Boolean cube, each coordinate's conditional success
probabilities form a finite marginal law. Two couplings are constructed: the independent
product and a recursive symmetric coupling whose local Boolean kernel maximizes the entropy of
the union. The orbit theorem applies to every coordinate because the mean of its conditional
law is exactly that coordinate's unconditional frequency.

The Shannon chain rule and conditioning monotonicity give lower bounds for the two union
entropies. If every coordinate frequency were at most `t`, summing the strict affine inequality
would force a convex combination of those union entropies to exceed the source entropy. Both
union laws remain supported on the original finite union-closed family, whose uniform law has
the maximal possible entropy. This is impossible.

**Scope:** the theorem is finite and fully handles null conditioning fibers. It concerns ordinary
families of distinct sets, not weighted multisets.

**Use:** any future finite affine-coupling certificate at another target can reuse the bridge
without change.

**Artifact:** `Frankl/FiniteEntropy.lean`, `Frankl/ConditionalEntropy.lean`,
`Frankl/FiniteCoupling.lean`, and `Frankl/AffineEntropyBridge.lean`; see
[`audits/frankl-rational-abundance-2026-08-10.md`](audits/frankl-rational-abundance-2026-08-10.md#finite-entropy-bridge).

### FC-S13: Rational universal abundance

**Kind:** theorem
**Evidence:** formalized
**Disposition:** graduated

Every finite union-closed family `F` with `F≠∅` and `F≠{∅}` contains an element occurring in
strictly more than

```text
(38234553336670271/10^17)|F|
```

members. The inequality `38234553336670271/10^17>(3−√5)/2` is also exact and kernel-checked.
This is an explicit rigorous advance over the AHS benchmark. `FC-O04` locates the affine
architecture's analytic wall less than `1.2×10⁻¹⁷` above the checked target. Liu's larger
`0.382709087…` candidate remains conditional.

**Scope:** the theorem does not settle Frankl's conjectured `1/2` bound and makes no absolute
priority claim beyond the audited literature comparison.

**Use:** this is the publication theorem and the baseline for every stronger-coupling attack.

**Artifact:** `Frankl.unionClosed_exists_abundant_coordinate` in
`Frankl/AffineEntropyBridge.lean` and
[`audits/frankl-rational-abundance-2026-08-10.md`](audits/frankl-rational-abundance-2026-08-10.md).

### FC-S14: Blocker pivot normal form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Normalize a hypothetical counterexample `F` on `U`, `|U|=n`, by adjoining `∅`, and put

```text
F₀ = {∅} ∪ {A⊆U : |A|≥2},
R = F₀∖F,
r = |R|,
r_i = |{A∈R : i∈A}|.
```

Then `R⊆{A:2≤|A|≤n−1}`, and the counterexample conditions are exactly

```text
2r_i−r ≥ n−1                                      for every i∈U,
C∈R and A∪B=C  implies  A∈R or B∈R               for A,B∈F₀.
```

The blocker clauses are equivalent to a local pivot normal form: for every `C∈R` there is
`x_C∈C` such that every non-singleton `A` with `x_C∈A⊆C` also lies in `R`. Consequently

```text
|R∩2^C| ≥ 2^(|C|−1)−1.
```

For distinct retained `A,B`, the cancellation profile

```text
{C∈F : A∪C=B∪C}
```

has size strictly below `|F|/2`, since it is contained in one coordinate star.

**Scope:** this is an exact reformulation and local obstruction, not a counterexample or a
proof of Frankl's conjecture. It does not force the report's proposed inflated-`B₃` shape. The
related exclusion of rank-three counterexample lattices is already stated through Tian's strict
height theorem; Colbert's dimension-two theorem independently corroborates the reduced
non-strict case.

**Use:** encode counterexample search with pivot variables, or seek a global double count
showing that the local pivot stars cannot satisfy every coordinate-bias inequality
simultaneously.

**Artifact:**
[`audits/frankl-counterexample-lunge-2026-08-10.md`](audits/frankl-counterexample-lunge-2026-08-10.md).

**Next:** derive or refute an inequality coupling pivot reuse across incomparable deleted sets;
do not enumerate vague high-collision lattices without first exploiting the exact pivot clauses.

### FC-M01: Rational Yu certificate

**Kind:** partial mechanism
**Evidence:** computational
**Disposition:** active

At `t=38234553336670271/10^17`, `α=356069804374481/10^16`, and `ε=10⁻¹⁸`, 160-bit Arb arithmetic
certifies

```text
(1−α)A+αC−(1+ε)B ≥ 0
```

on both reduced bivariate families. Two entropy-zero corner squares are discharged by explicit
analytic estimates. The run assesses 110,760 rational boxes and emits 55,413 certified leaves
with deterministic family hashes

```text
diagonal-endpoint:       1f49c7cafc3831fe32708f70609e08dd47fae3c8950dc34f44005205618594bb
diagonal-diagonal-lower: 725cac791c5d71c17fbfe39ef8aa4206cd0e324eb63ae3b146e40d21587f1174
diagonal-diagonal-upper: 015ae1cc40f89b679f814b41c7d3a86174d0d80b5659ae4aacf5bba3bc67ace1
```

**Scope:** this is an outward-rounded certificate for the reduced objectives, not by itself an
unbounded theorem. Promotion additionally requires the analytic reductions and numerical
certificate to pass the repository's strict Lean gate.

**Use:** retain it as an independent regression oracle and parameter-search adjudicator. The
Lean theorem does not depend on Arb.

**Artifact:** [`tools/certify_frankl.py`](tools/certify_frankl.py),
[`audits/frankl-yu-reduction-2026-08-08.md`](audits/frankl-yu-reduction-2026-08-08.md#outward-rounded-certificate),
and the `Frankl/Certificate*.lean`, `Frankl/Interval*.lean`, and `Frankl/LogBounds.lean`
checker modules.

**Next:** extend the oracle only for a genuinely new coupling protocol, or formalize the exact
wall if that becomes strategically useful. `FC-O04` rules out a material ratchet within the
present affine architecture.

### FC-O02: Uniform-fiber semigroup ceiling

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Let a finite semigroup map homomorphically onto Boolean conjunction, with zero and one fibers
of sizes `k` and `m`. Any uniform full-fiber entropy lift induces homogeneous set weight
`t=m/k`. At a point-mass conditional law of omitted probability `x`, maximal entropy inside
the product fibers gives

```text
entropy increment
  ≤ B(2x−x^2)−B(x)+x(1−x)log(k/m).
```

Positivity for every `0<x<1/2`, as required for a half-frequency theorem, is possible only if

```text
t≤16/27.
```

At uniform weight `t=1`, the ceiling changes sign at `x=(3−√5)/2`. Therefore arbitrary
finite-semigroup multiplication-table engineering inside this architecture cannot improve the
golden-ratio uniform abundance constant through a functional required to be positive on every
fixed-mean conditional law.

**Scope:** the obstruction assumes uniform laws within two fixed full fibers, independent
multiplication, and a coordinatewise Shannon-entropy comparison. It does not cover dependent
couplings, nonuniform or history-dependent labels, or genuinely multi-coordinate inequalities.

**Use:** retain `FC-S03` as a sharp tilt endpoint, but reject direct searches for a better
uniform-weight finite semigroup of the same form.

**Artifact:**
[`audits/frankl-semigroup-fiber-ceiling-2026-08-08.md`](audits/frankl-semigroup-fiber-ceiling-2026-08-08.md#point-mass-ceiling).

### FC-O03: Maximal self-dual completion fails

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

There is a 13-member intersection-closed, complement-free family on five coordinates that is
maximal under inclusion among families with those two properties. Every attempted adjunction,
after taking meet closure, creates a complementary pair. Since a self-dual Boolean function
would choose exactly one member of each of the 16 complementary pairs, maximality does not
produce a self-dual Horn completion.

**Scope:** this refutes only completion by inclusion on the same universe. It does not exclude a
frequency-preserving lift to a larger universe or another non-inclusion transformation into the
bidual class.

**Use:** do not infer self-duality from Zorn-style maximality. Any completion attack must control
the missing complementary pairs constructively and track coordinate frequencies.

**Artifact:**
[`audits/frankl-bidual-horn-density-2026-08-08.md`](audits/frankl-bidual-horn-density-2026-08-08.md#failure-of-naive-self-dual-completion).

### FC-O04: Affine two-coupling wall

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Let `h` be binary entropy, `ℓ=log 2`, and let `y⋆` be the locally unique zero of

```text
h(y)²−ℓ(2h(y)−h(y²))
```

inside the certified interval

```text
(0.6705452614969630276082946160,
 0.6705452614969630276082946162).
```

Put `s⋆=y⋆h(y⋆)/h(y⋆²)` and `c⋆=1−s⋆`. Outward-rounded Arb arithmetic gives

```text
0.38234553336670272114599300
  < c⋆ <
0.38234553336670272114599301.
```

For the centered endpoint objective `K`, exact algebra gives, at `s=1−t`,

```text
K(s,α,0;y⋆)=(s−s⋆)[(1−α)h(y⋆²)s+αy⋆(2log 2−h(y⋆))].
```

The bracket is positive for every `α∈[0,1]`. Hence every affine mixture of the independent and
max-entropy couplings fails throughout `c⋆<t≤1/2`, even before positive entropy slack is
imposed. The formal target in `FC-S13` lies between `11×10⁻¹⁸` and `12×10⁻¹⁸` below this wall.

**Scope:** this is an upper obstruction for the two-coupling affine architecture. It neither
rules out conditionally IID or other new couplings nor supplies an exact Lean theorem at `c⋆`.

**Use:** stop decimal ratcheting inside the exhausted architecture; new progress must alter the
coupling family or the entropy functional.

**Artifact:**
[`audits/frankl-affine-wall-2026-08-10.md`](audits/frankl-affine-wall-2026-08-10.md) and the
default wall check in [`tools/certify_frankl.py`](tools/certify_frankl.py).

## Matrix Mortality

### MM-C01: Unconditional rank-one separator

**Kind:** compiler  
**Evidence:** formalized
**Disposition:** graduated

For arbitrary square matrices `X_a` over a field, put `P=CL`. Then `{X_a}∪{P}` is mortal exactly
when `LX_wC=0` for some active word `w`. A zero product without `P` is itself a scalar-zero
witness. A product with separators factors as

```text
(∏ᵢ LX_{wᵢ}C) · (X_{w₀}C)(LX_{wₘ}).
```

An internal scalar zero is immediate. If either exterior vector vanishes, its exterior active
word is a scalar-zero witness. Thus singular controls, zero control-only products, adjacent or
exterior separators, and zero rows or columns require no hypotheses.

**Scope:** the field assumption supplies zero-product cancellation for the scalar factors. The
theorem does not construct a scalar recognizer or make its zero language undecidable.

**Artifact:** `MatrixMortality.mortal_adjoin_outer_iff` in
[`TerminalTile.lean`](MatrixMortality/TerminalTile.lean).

**Audit:**
[`m34-unconditional-separator-2026-08-07.md`](audits/m34-unconditional-separator-2026-08-07.md).

**Use:** adjoining one rank-one separator completely solves the scalar-to-mortality converse;
never spend compiler structure on invertibility, a fixed anchor, or separator placement.

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

### MM-C04: Internal-word sandwich minimization

**Kind:** compiler
**Evidence:** formalized
**Disposition:** graduated

Let `A : Σ → M_d(K)` and suppose a nonempty physical word `ω` has nonzero product

```text
E=A_ω=UW,
```

where `U : K^r → K^d` and `W : K^d → K^r` both have rank `r`. Define

```text
R=span{A_w im U : w∈Σ*},
N={x∈R : WA_wx=0 for every w∈Σ*},
H=R/N.
```

Both `R` and `N` are invariant. Let `B_a` be the action induced on `H`. Then

```text
{A_a} is mortal  ⇔  {B_a} is mortal.
```

The forward implication passes a zero product to every invariant subquotient. Conversely, if
`B_z=0`, then `A_zR⊆N`, so `WA_zU=0` and the entirely physical repair word satisfies

```text
A_{ωzω}=EA_zE=U(WA_zU)W=0.
```

No syntax or exterior nonvanishing hypothesis is required. Moreover,

```text
dim H = rank [WA_{uv}U]_{u,v∈Σ*},
```

the flattened block-Hankel rank of the matrix-valued series `F(w)=WA_wU`. The quotient is its
minimal exact linear realization.

**Scope:** the result is exact-linear. It does not preserve only the zero set, and it does not
lower dimension unless the sandwich series has smaller block-Hankel rank. If `H=0`, an
ambient mortal word already exists. Independent nonzero generator scaling preserves mortality,
which supplies the algebraic denominator-clearing step. Extracting a chosen rational basis and
concrete quotient matrices is not part of the generic theorem.

**Use:** search a known-safe mortality family for an internal low-rank word, minimize its
matrix-valued sandwich, and inherit a complete arbitrary-word converse without adding a
generator. For `M₅(3)`, compute rank-two sandwich realizations inside the established
six-state, three-generator families before designing another five-state parser.

**Artifact:** `MatrixMortality.InternalSandwich.mortal_quotient_iff`,
`MatrixMortality.InternalSandwich.ambient_mortal_of_quotient_subsingleton`,
`MatrixMortality.InternalSandwich.range_reachableBehavior_eq_span`,
`MatrixMortality.InternalSandwich.quotient_finrank_eq_blockHankel`, and
`MatrixMortality.InternalSandwich.quotient_finrank_le_of_represents` in
[`InternalSandwich.lean`](MatrixMortality/InternalSandwich.lean). The common exact-behavior
primitive is in [`ExactBehavior.lean`](MatrixMortality/ExactBehavior.lean); full generated
matrix algebras force ambient sandwich dimension through
`quotient_finrank_eq_card_of_wordProductSpan_eq_top` in
[`FullMatrixBehavior.lean`](MatrixMortality/FullMatrixBehavior.lean). Independent nonzero
generator scaling is `MatrixMortality.isMortal_smulMatrix_iff` in
[`MatrixSemigroup.lean`](MatrixMortality/MatrixSemigroup.lean). The independent reconstruction
and edge-case audit are in
[`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md).

### MM-O01: All-placement packing rank

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For every placement of the four ordinary `3 × 3` payloads and the rank-one separator in the
literal three-generator `6 × 6` CHHN packing, the selected scalar coefficient series has exact
linear-representation dimension six. A placement-dependent six-prefix family and a
semantically selected six-suffix family expose a nonsingular finite Hankel section.

**Scope:** this excludes exact five-state realizations of that coefficient series. It does not
exclude a different five-state series with the same zero set.

**Use:** reject further exact minimization of the literal CHHN packing and require a changed
coefficient series or punctuation architecture.

**Artifact:** `chhnNeary_exactRepresentation_six_le_card` in
[`MatrixMortality/CHHNPackingRank.lean`](MatrixMortality/CHHNPackingRank.lean), built on the
generic kernels in [`MatrixMortality/CHHNPacking.lean`](MatrixMortality/CHHNPacking.lean).
The reconstruction and independent 120-placement executable check are documented in
[`audits/chhn-all-placement-rank-2026-07-26.md`](audits/chhn-all-placement-rank-2026-07-26.md).

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

**Evidence:** formalized

**Disposition:** graduated

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

**Formalization:** `twoChannelBoundaryTax` proves the finite-dimensional core, and
`exactDiagonalTwoChannel_card_lower_bound` derives the all-word bridge theorem from an arbitrary
nonsingular finite Hankel section. The proof uses no infinite Hankel library. It is slightly
stronger than the reported statement: nonzero inactive row and column suffice; full boundary
rank two is unnecessary.

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O04: Uniform rank-four paired series

**Kind:** certificate
**Evidence:** formalized
**Disposition:** graduated

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

**Formalization:** `pairedRankReachable_det` and `pairedRankObservable_det` prove the two
determinant identities. `pairedRankHankel_det_ne_zero` certifies the integer Hankel section,
`paired_exact_state_lower_bound` gives the universal rational four-state lower bound, and
`paired_exact_diagonal_twoChannel_state_lower_bound` composes this record with `MM-O03` to rule
out every exact five-state diagonal two-channel bridge.

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

### MM-O08: Full-algebra prefix pair

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let `B₀,B₁` be the restricted ten-state prefix generators emitted by the current arithmetic
source envelope. The physical word `000` is nonzero rank one:

```text
B₀³=uvᵀ.
```

The ten columns

```text
u, B₁u, …, B₁⁹u
```

and the ten rows `vᵀB_p` for

```text
p∈{ε,1,10,11,101,110,1011,1101,10110,11010}
```

are bases. Their determinant certificates are nonzero uniformly for `β≥3` and
`body.length≥β−1`. The two large polynomial factors reduce respectively to residues `8`
and `3` modulo `9`; only the final reachable pivot uses that the body is nonempty. Hence the
one hundred physical products

```text
B₁ʲB₀³B_p=(B₁ʲu)(vᵀB_p)
```

span every outer product and therefore

```text
span_ℚ{B_w : w∈{0,1}*}=M₁₀(ℚ).
```

The pair has no nonzero proper common invariant subspace or quotient. More strongly, for every
nonzero internal word `E=UW`, the reachable space of `WA_wU` is all of `ℚ¹⁰`, its
unobservable subspace is zero, and its exact block-Hankel rank is ten.

**Scope:** this closes exact linear restriction, quotient, reachable/observable minimization,
and internal-sandwich compression of this physical pair. It does not exclude a different pair,
a different transducer, a same-zero nine-state series, or any nonlinear compiler.

**Use:** stop exact minimization of the present ten-state decoder. Any `M₉(2)` attack must
change the physical pair or change its nonzero behavior.

**Artifact:** the coordinate reconstruction, determinant factors, positivity proof, and
independent symbolic check are in
[`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md#the-ten-state-prefix-pair).

**Formalization:** [`MatrixMortality/PrefixContexts.lean`](MatrixMortality/PrefixContexts.lean),
[`MatrixMortality/PrefixContextsClosed.lean`](MatrixMortality/PrefixContextsClosed.lean),
[`MatrixMortality/PrefixContextsNonsingular.lean`](MatrixMortality/PrefixContextsNonsingular.lean), and
[`MatrixMortality/PrefixFullAlgebra.lean`](MatrixMortality/PrefixFullAlgebra.lean), through the
generic exact-behavior bridge in
[`MatrixMortality/FullMatrixBehavior.lean`](MatrixMortality/FullMatrixBehavior.lean);
`prefixAlgebra_zero_cube`, `prefixAlgebraReachable_isUnit`,
`prefixAlgebraObservable_isUnit`, `prefixAlgebra_wordProductSpan_eq_top`, and
`prefixAlgebra_exactSandwich_ten_le_finrank`.

### MM-O09: Two-state ternary prefix image

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

A complete ternary prefix tree with five leaves has exactly two internal states: the root has
two leaf children and one internal child, whose three children are leaves. Consider a literal
exact weighted decoder with one three-dimensional payload space at each state, four nonsingular
leaf payloads, and one singular separator.

At least one child leaf has a nonsingular decoded payload. Its factorization through the
root-to-child edge forces that edge matrix to be nonsingular. The physical generator carrying
that edge therefore supplies the complete root payload block to the joint image. A nonsingular
child completion either occurs on the same physical generator, making it full rank, or its
graph can be combined with the root block to isolate the complete child block. Thus the span
of the three generator images is the full six-state carrier.

**Scope:** literal exact two-state ternary prefix decoders with three-dimensional edge
matrices and exactly the stated four-nonsingular/one-singular source profile. Repairable
quotients, state-dependent gauges, same-zero decoders, and non-prefix codes remain open.

**Use:** a direct ternary recoding of the five-matrix source cannot reach five dimensions by
the common-image compiler [`MM-C02`](#mm-c02-common-image-restriction).

**Artifact:** [`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md#secondary-obstructions).

### MM-O10: Additive toggle fusion cycle

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Normalize the paired separator to an idempotent `P`, and let `T` be the involutive paired
toggle. Since the boundary row obeys `LT=L`, one has `PT=P`. Put

```text
Q=TP,      F=T−P.
```

Then `Q` is rank-one idempotent and

```text
F²=I−Q,      F³=F.
```

Both `F` and `F²` have rank three, so every positive power of `F` is rank three. No pure power
of the most direct additive toggle/separator fusion can punctuate or vanish.

**Scope:** the single ansatz `F=T−P` after idempotent normalization. Bordered couplings,
different perturbations, and mixed words containing data generators remain open.

**Use:** reject the additive fusion before any power search.

**Artifact:** [`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md#secondary-obstructions).

### MM-O11: Full-algebra paired-binary family

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Adjoin the canonical rank-one separator `P=CL` to the two transposed six-state paired-binary
controls. The columns

```text
C, A₀C, A₁C, A₀²C, A₁A₀C, A₀³C
```

and rows

```text
L, LA₀, LA₁, LA₀², LA₀A₁, LA₀³
```

are bases throughout the source envelope `β≥3`. Their determinant factors have final terms
congruent to `3 mod 9`, using only that the rule-`c` lower word ends in `10`. Consequently the
thirty-six physical contexts

```text
A_uPA_v=(A_uC)(LA_v)
```

span `M₆(ℚ)`.

Every nonzero internal word therefore has reachable space `ℚ⁶`, zero unobservable subspace,
and exact sandwich dimension six. [`MM-C04`](#mm-c04-internal-word-sandwich-minimization)
cannot reduce this family to five states.

**Scope:** the paired-binary mortality family only. A modular sweep found full algebra for all
120 literal CHHN packings at `β=3`, body `bb`, but that bounded computation is not an unbounded
theorem.

**Use:** close exact invariant restrictions, quotients, and internal-word sandwiches of the
canonical `Z₆(2)→M₆(3)` construction. A five-state proof must change the physical family or its
nonzero behavior.

**Artifact:** the symbolic determinant proof and bounded CHHN sweep are in
[`audits/six-state-sandwich-saturation-2026-07-25.md`](audits/six-state-sandwich-saturation-2026-07-25.md);
the executable certificate is
[`tools/audit_six_state_sandwich.py`](tools/audit_six_state_sandwich.py).

Lean proves the sparse context matrices invertible by eliminating their kernels. The final
reachability and observability pivots reduce to integer expressions of the form `9z+3`, using
the terminal lower suffix `10`. A generic rank-one-context theorem then turns the thirty-six
physical contexts into a spanning family.

**Formalization:** [`MatrixMortality/FullMatrixAlgebra.lean`](MatrixMortality/FullMatrixAlgebra.lean),
[`MatrixMortality/PairedBinaryContexts.lean`](MatrixMortality/PairedBinaryContexts.lean),
[`MatrixMortality/PairedBinaryContextsClosed.lean`](MatrixMortality/PairedBinaryContextsClosed.lean),
[`MatrixMortality/PairedBinaryContextsNonsingular.lean`](MatrixMortality/PairedBinaryContextsNonsingular.lean), and
[`MatrixMortality/PairedBinaryFullAlgebra.lean`](MatrixMortality/PairedBinaryFullAlgebra.lean),
through the generic exact-behavior bridge in
[`MatrixMortality/FullMatrixBehavior.lean`](MatrixMortality/FullMatrixBehavior.lean);
`pairedBinaryMortality_wordProductSpan_eq_top` and
`pairedBinaryMortality_exactSandwich_six_le_finrank`.

### MM-O12: Boundary-calibrated setter shear is gauge

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The five-state setter admits a one-parameter side-basis shear `α`. Its side-basis determinant is

```text
−r(scale−1−r·upper),
```

independent of `α`. The boundary-correct delimiter has cube
`firstAxis ⊗ terminalRow(hook(r,upper,α))`; after the physical calibration
`lambda·marker=1+r·upper`, its square sends the sheared distinguished column to
`lambda·separatorColumn(marker)`. Eliminating the two side-coordinate equations leaves the
transfer tail

```text
(scale−1−r·distinguishedUpper)·resolvedTail
  = (distinguishedUpper−1−r·upper)·a + value·x,
```

again independent of `α`.

**Scope:** the boundary-correct coordinate shear of the established five-state setter. The
result does not exclude a different delimiter, a nonlinear coordinate change, or another
five-state physical family.

**Use:** do not reopen the setter projective-avoidance problem by varying this shear. Boundary
calibration makes it a gauge: it changes coordinates but neither the mixed separator nor the
projective transfer obstruction.

**Formalization:** [`MatrixMortality/SetterShear.lean`](MatrixMortality/SetterShear.lean),
through `sideBasis_det`, `delimiter_cube`, `delimiter_square_distinguishedColumn`, and
`transfer_tail`.

### MM-O13: Finite positive-ray setter obstruction

**Kind:** obstruction
**Evidence:** audited
**Disposition:** graduated

In the decimal setter of [`MM-M05`](#mm-m05-decimal-swapped-setter), write every J-fraction
step as

```text
F_z(t)=u_z+v_z−v_z/t,       u_z,v_z>0.
```

The poles of blocks containing an unbounded number of `c` rules approach `1` from below.
Because any square-run block may follow any prior block, every source threshold in a finite
labelled positive-ray invariant `[r_i,∞]` must therefore satisfy `r_i≥1`.

The single `c` erasure has `a_c=u_c+v_c<1` throughout the compiler-emitted range. Hence, for
every `t≥1`,

```text
F_Dc(t)=a_c−v_c/t<a_c<1.
```

It cannot land in any of the required rays. Splitting labels by first role, last role, or the
low/high length shell does not alter the all-to-all transition law, so no finite family of such
rays can certify arbitrary-depth avoidance.

**Scope:** positive rays only. Two-sided domains, unbounded length rescaling, and arithmetic
invariants are not excluded.

**Use:** do not subdivide the decimal length shells into another finite last-block ray system.
The next certificate must retain sign cycles or exact radix carry.

**Artifact:**
[`audits/m53-decimal-setter-hyperbolicity-2026-08-30.md`](audits/m53-decimal-setter-hyperbolicity-2026-08-30.md#finite-ray-obstruction).

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-O14: Decimal setter elliptic product

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For the decimal setter [`MM-M05`](#mm-m05-decimal-swapped-setter), write

```text
J_z=[[u_z+v_z,−v_z],[1,0]].
```

At `β=10`, any defect-`11` block whose upper word is `cbⁿ` and whose lower spelling begins with
an encoded `b` has normalized lower decimal prefix `55 7¹⁰ 5`. Pair it with the single `c`
erasure. Exact rational intervals give

```text
disc(J_high)>0,       disc(J_low)>0,
disc(J_low J_high)<0.
```

The two checked compiler checkpoints realize the high block as
`R_cR_b¹⁰D_b⁸²⁸⁶` and `R_cR_b¹⁰D_b⁸⁸⁷¹`. The short body `bcbbbbbbc` already gives the
length-nine witness `(R_cD_b⁷,D_c)`.

**Scope:** this proves an elliptic product, not a pole collision. It excludes semigroup uniform
hyperbolicity and every common proper convex-cone proof derived from individual block
hyperbolicity. Arithmetic or suffix information may still prove exact pole avoidance.

**Use:** do not refine the real hyperbolic chambers. Move directly to the joint decimal
`2`/`5`-adic carry.

**Formalization:** `SetterJFraction.leadingB_elliptic_pair` in
[`MatrixMortality/SetterJFraction.lean`](MatrixMortality/SetterJFraction.lean).

**Artifact:**
[`audits/m53-decimal-setter-elliptic-product-2026-08-30.md`](audits/m53-decimal-setter-elliptic-product-2026-08-30.md).

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

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
**Disposition:** closed

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

**Use:** retain this as the first exact setter punctuation mechanism. The
swapped-digit setter [`MM-M04`](#mm-m04-swapped-digit-setter) preserves it while
removing the orientation-reversing transfer, so the unswapped route is closed.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#side-normal-data).

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-M04: Swapped-digit setter

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

Reverse the ordinary nonzero ternary digit embedding:

```text
0↦2,       1↦1.
```

Word equality, concatenation, length, and the entire Neary source theorem are
unchanged. Put

```text
ρ=3^β,       μ=2ρ−1,       t=3ρ,       r=t/μ,
H=5ρ−1,      R=2−ρ,
f=(1,0,r)ᵀ, p=(0,−1,0)ᵀ, q=(0,0,r(2−r))ᵀ.
```

The same five-state setter construction, with `α=1+r`, satisfies

```text
rank S=3,      rank S²=2,      rank S³=1,
Sⁿ=S³  for n≥3,
S²A_cS³=λC̃L̃.
```

The regular rule/erasure decoder and the source-halting-to-mortality
implication therefore survive exactly.

For every square-run block, the induced projective matrix has determinant

```text
κVA>0,       κ=(1+r)/(μ(2−r)).
```

Thus every transfer is orientation preserving. In the scaled coordinate its
common center is

```text
h=H/R<0,
```

whereas every pole `P/V` is positive.

**Scope:** the sign separation does not itself prove avoidance. Arbitrary
iterations can cross the center, and the remaining fixed-slope correspondence
equations are asynchronous.

**Use:** this is the preferred setter variant. Unlike
[`MM-M03`](#mm-m03-five-state-setter-punctuation), it has a one-sided centered
coefficient and the finite-slope theorem
[`MM-S07`](#mm-s07-swapped-digit-finite-slope-reduction).

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** formalize the parametric digit-order construction and decide the
finite nonterminal slopes exposed by `MM-S07`.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-M05: Decimal swapped setter

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

Evaluate binary words in radix ten with nonzero digits

```text
0↦7,       1↦5.
```

The setter basis admits the radix-parametric form

```text
f=(1,0,r)ᵀ,
p=(0,−1,0)ᵀ,
q=(0,0,r(B−1−rd₁))ᵀ.
```

Its determinant is nonzero for the displayed decimal parameters, and
`R_cf=D_cf=(1+rd₁)f+q`. The regular decoder, delimiter powers, and mixed separator therefore
survive exactly. In the coordinate `t=L/(y+L)`, every square-run transfer is

```text
F_z(t)=u_z+v_z−v_z/t,       u_z,v_z>0.
```

The decimal length shells make every such transfer strictly hyperbolic by
[`MM-S11`](#mm-s11-decimal-setter-hyperbolicity).

**Scope:** this preserves the five-state forward reduction but does not prove its arbitrary-word
converse. Hyperbolicity alone does not prevent a rational orbit from meeting a pole.

**Use:** retain this as the sharpest Archimedean setter variant. Keep the ternary swapped setter
for its mature suffix and `3`-adic lemmas; use the decimal variant when real length-shell
separation matters.

**Artifact:**
[`audits/m53-decimal-setter-hyperbolicity-2026-08-30.md`](audits/m53-decimal-setter-hyperbolicity-2026-08-30.md).

**Next:** apply the exact two-prime recurrence
[`MM-S12`](#mm-s12-decimal-two-prime-carry) to the surviving normalized suffix. Finite
positive-ray labels are excluded by [`MM-O13`](#mm-o13-finite-positive-ray-setter-obstruction),
and [`MM-O14`](#mm-o14-decimal-setter-elliptic-product) closes every argument from blockwise real
hyperbolicity alone.

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

### MM-S02: Reset-zero projective peeling

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Scale the projective coordinate in [`MM-S01`](#mm-s01-square-run-projective-normal-form) by
`y=μx` and put

```text
h=(17ρ−1)/(2(ρ+1)),      ρ=3^β.
```

For a nonempty role block `z`, let

```text
P_z=[spell(nearyUpper,z)·10^β]₃,
V_z=[spell(nearyLower,z)]₃,
A_z=3^|spell(nearyUpper,z)|.
```

Then

```text
Ψ_z(y)=h(1−μA_z/(P_z−V_zy)),      π_z=P_z/V_z.
```

Every pole lies in one of two exact `3`-adic shells:

```text
v₃(π_z−h)=β  if z is one erasure role,
v₃(π_z−h)=1  otherwise.
```

For an orbit leaving the ordinary reset,

```text
v₃(Ψ_u(0)−h)=|spell(nearyUpper,u)|.
```

Equality with a pole therefore forces that upper length to be `1` or `β`. Length one gives
`Ψ_u(0)=1`, and a pole at `1` is precisely a genuine terminal match. Length `β` forces `u`
to consist only of `c` roles, but its image is smaller than both single-erasure poles.

**Scope:** excludes a false pole after one preceding transfer from reset `0`. It does not
control longer orbits or one-transfer images from the distinguished boundary `1`.

**Use:** any counterexample to the setter candidate must contain at least two nontrivial
projective transfers after an ordinary reset. Future invariants should track `3`-adic mismatch
depth together with the pulse or suffix state.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md).

**Next:** lift the shell calculation from valuation alone to a finite suffix-carry state.
Residue-only projective abstractions saturate on the benchmark and cannot prove avoidance.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S03: Centered setter carry

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Retain the scaled coordinate and constants of
[`MM-S02`](#mm-s02-reset-zero-projective-peeling), and put

```text
H=(17ρ−1)/2,      R=ρ+1,      K=RHμ,
C_z=RP_z−HV_z,    m_z=|spell(nearyUpper,z)|.
```

Represent a finite projective state by integers `X,Y` through

```text
y−H/R=−HμX/Y.
```

One admissible square-run block acts exactly by

```text
X'=3^m_zY,
Y'=C_zY+KV_zX.
```

The two reset states are `(1,Rμ)` and `(3,RH)`. A pole is exactly a zero
second coordinate. If `d=v₃(X)−v₃(Y)` and
`s_z=v₃(C_z)∈{1,β}`, then away from the equal-valuation branch

```text
d'=m_z−min(d,s_z).
```

At equal valuation, the extra valuation is the carry created by the two
normalized units; infinite carry is precisely a pole. For blocks ending in an
erasure, the first unit test is fixed: a multi-role pole requires normalized
unit `1 mod 3`, while a single-erasure pole requires `2 mod 3`.

This recurrence yields two exact gates.

1. After two transfers from reset zero, outside the intermediate state `1`, a
   prospective third pole is possible only when the second block is two
   `c` roles, when it is `β+1` `c` roles, or when the first block is two
   `c` roles and the second block is the single `b` erasure.
2. From the distinguished boundary `1`, one completed block reduces
   projectively to `(3^m,R(P−V))`. If it is not already a terminal match, a
   following pole requires

   ```text
   v₃(P−V)=m−1     or     v₃(P−V)=m−β.
   ```

   This valuation is exactly the common binary-suffix length of the encoded
   upper boundary and lower spelling.

**Scope:** these are necessary gates, not a proof of arbitrary-depth
avoidance. The first and prospective pole blocks remain unbounded, and the
equal-valuation carry can retain an arbitrarily long synchronized suffix.

**Use:** replaces raw Möbius iteration by an integer carry automaton and
identifies the only place where the Neary pulse state must be attached. Search
the three two-transfer block shapes first; any general proof must control the
two suffix equations at the distinguished boundary.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#centered-integer-carry).

**Next:** apply [`MM-S04`](#mm-s04-reverse-suffix-discrepancy) to quotient the
word-valued suffix carry without forgetting the two resonant target families.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S04: Reverse suffix discrepancy

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let `M=10^β`, and compare the terminal words `U(z)M` and `V(z)` of an arbitrary
Neary role word `z`. Reading roles from right to left, maintain the pair
obtained by reversing both words and deleting their common prefix. Prepending
one role appends its reversed upper and lower images to the two residuals,
after which their new common prefix is deleted. Until the first mismatch, at
least one residual is empty; once both are nonempty, their first bits differ
and no unprocessed role can change the common suffix.

This recurrence computes exactly

```text
k=lcs(U(z)M,V(z)).
```

Put `m=|U(z)|` and `d=m−k`. If the first mismatch occurs in a processed suffix
`q`, with `z=pq`, then

```text
|U(p)|≤d+|M|.
```

If no mismatch occurs and `d>0`, the surviving upper residual has exactly
`d+|M|` bits. The only setter resonances are `d=1` and `d=β`, so their
unprocessed left fringes have upper length at most `β+2` and `2β+1`.

**Scope:** the natural exact state is a residual word. This theorem neither
bounds that queue before the first mismatch nor proves that no finite semantic
quotient exists. It proves no projective avoidance statement by itself.

**Use:** replaces the proposed finite pulse transducer by the correct
PCP-discrepancy object. A successful proof must recognize reachability of two
bounded residual target families through a quotient compatible with role
prepending. Phase, length, valuation, and fixed-modulus residue alone do not
retain the exact recurrence; the tested residue-only quotients saturate.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#reverse-suffix-discrepancy-queue);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** combine the discrepancy queue with
[`MM-S05`](#mm-s05-distinguished-boundary-beta-shell), then identify a semantic
quotient for the surviving valuation-one target.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S05: Distinguished-boundary β-shell

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

Start the setter carry at projective boundary `1`. For a nonterminal block
`v`, put

```text
m=|U(v)|,       k=lcs(U(v)M,V(v)),       d=m−k,
Δ=(P_v−V_v)/3^k.
```

Then `Δ` is an integer not divisible by `3`, and the resulting centered state
is projectively `(3^d,RΔ)`. If a following block `z` is a pole, it must satisfy

```text
C_zΔ+HμV_z3^d=0.
```

When `d=β`, the pole-shell theorem forces `z` to be a single erasure. The
`b` erasure requires

```text
Δ=−2Hμ/(45ρ²+53ρ−10),
```

which lies strictly between `−1` and `0`. The `c` erasure requires `Δ=−μ`.
The latter equality would make the addition

```text
P_v+μ3^{m−β}=V_v
```

force the binary factor `0·1·0^β` inside
`tagEncode β (v.map letter)·M`. That factor is impossible: every occurrence of
`1·0^β` begins a `b` codeword or the final marker and is never preceded by
`0`.

Therefore no finite nonterminal block in the distinguished-boundary
`β`-resonance can be followed by a pole.

**Scope:** this closes only the `d=β` branch immediately after boundary `1`.
It does not handle the surviving `d=1` discrepancy, nor β-shell states reached
after other malformed transfers.

**Use:** remove the single-erasure pole family from the boundary-one analysis.
The remaining semantic quotient needs to preserve only valuation-one target
blocks.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#elimination-of-the-beta-shell);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** apply
[`MM-S06`](#mm-s06-valuation-one-divisor-normal-form) to the surviving
valuation-one shell.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S06: Valuation-one divisor normal form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let a multi-role pole block have positive codes `P,V` and

```text
C=RP−HV,       v₃(C)=1.
```

Suppose an integer `3`-adic unit `Δ` reaches that pole:

```text
CΔ+3HμV=0.
```

Reduce `P,V` by their gcd:

```text
P=gp,       V=gv,       gcd(p,v)=1,
a=(Rp−Hv)/3.
```

Put `q=gcd(a,v)`. Then

```text
q=gcd(R,v),       q∣R.
```

Writing `a=qa₀`, `v=qv₀`, and `r=R/q` gives

```text
gcd(a₀,v₀)=gcd(r,v₀)=1,
a₀Δ=−Hμv₀,
rp=Hv₀+3a₀.
```

In particular,

```text
a₀∣Hμ,       v₀∣Δ.
```

Every integral pole therefore lies on one of finitely many arithmetic rays
indexed by divisors `q∣R` and `a₀∣Hμ`; only `v₀` remains unbounded.

Moreover,

```text
Δ=H       ↔       P=V.
```

Thus the distinguished integral value is exactly the genuine terminal-match
pole, not a malformed one.

For a boundary discrepancy with `d=1`, positivity also gives

```text
0<Δ<9ρ.
```

Values `Δ≤3μ` map to a nonpositive projective point and cannot be poles.
Hence the positive branch is confined to the finite interval
`3μ<Δ<9ρ`; only negative divisor rays remain unbounded.

**Scope:** the divisor normal form does not prove that the other rays are
empty. Their realizability by a common Neary role word remains open. The exact
benchmark search through target-block length `14` finds no false integral
unit pole, but that is computational evidence only.

**Use:** replace an unconstrained rational-pole search in the valuation-one
shell by finitely many divisor rays. Positive boundary discrepancies are
already bounded by their `β+2`-digit unmatched upper prefix; negative rays
remain the unbounded branch.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#valuation-one-divisor-normal-form);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** intersect the divisor rays with the reverse Neary role transducer.
Either prove that only `(a₀,v₀)=(-μ,1)` is realizable, or return the first
explicit false integral pole.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S07: Swapped-digit finite-slope reduction

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

For the swapped setter [`MM-M04`](#mm-m04-swapped-digit-setter), put

```text
D=ρ−2=−R>0.
```

Every nonempty block has

```text
C=RP−HV=−(DP+HV)<0.
```

At the distinguished boundary, a valuation-one pole reached from a normalized
integer discrepancy `Δ` must satisfy

```text
(DP+HV)Δ=3HμV.                              (1)
```

Consequently

```text
0<Δ<3μ.
```

Reduce `P=gp`, `V=gv`, with `gcd(p,v)=1`, and put

```text
q=gcd(D,v),       D=qd,       v=qv₀.
```

Equation (1) becomes

```text
Δ(dp+Hv₀)=3Hμv₀.
```

Because `gcd(dp+Hv₀,v₀)=1`,

```text
dp+Hv₀ ∣ 3Hμ.
```

Thus every integral valuation-one pole belongs to an effectively finite set:

```text
q∣D,       v₀<3μ,       p≤3Hμ/d.
```

There is no unbounded divisor ray. The distinguished value remains exact:

```text
Δ=H       ↔       P=V.
```

In the `β`-shell, the single `b` erasure requires a rational discrepancy
strictly between `1` and `2`, while the single `c` erasure requires `Δ=2μ`.
The latter is excluded by
[`MM-S08`](#mm-s08-swapped-distinguished-boundary-beta-shell).

**Scope:** finiteness of the primitive slopes is not finiteness of the target
role words: the common multiplier `g` remains unbounded. One of the slopes is
the original undecidable terminal equality. The theorem therefore narrows but
does not decide projective avoidance.

**Use:** replace the ordinary setter's unbounded negative rays by finitely many
fixed-ratio correspondence languages. The next proof should show that every
nonterminal accepted slope either contains a genuine terminal-match suffix or
violates the Neary pulse invariant.

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#one-sided-centered-carry);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** prove or refute the finite-slope endpoint theorem in the sole
remaining valuation-one shell.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S08: Swapped distinguished-boundary beta shell

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

For the swapped setter, suppose a distinguished-boundary block has resonance
gap `d=β`.  If it could hit the single `c`-erasure pole, its normalized
discrepancy would be `Δ=2μ`.  After deleting the common suffix, the upper and
lower binary prefixes would necessarily have the form

```text
A=T·00·z·10,       B=T·11·z·01,
|T|=β−1,           |z|=β−2.
```

This is the unique carry pattern for

```text
[A]₃−[B]₃=2μ
```

under the swapped nonzero-digit embedding.

The upper pattern forces its source-letter prefix to be

```text
c^s·b·c^(β−s−3),       0≤s≤β−3,
```

followed by another `b` or by the marker.  It therefore forces the lower
prefix

```text
1^(s+1)·0^(β−s−2)·11·0^s·1^(β−s−2)·01.
```

For `s=0`, neither lower image of a `b` role has the required prefix.  For
`s>0`, the first role must be the `c` rule.  Its body must begin
`c^(s−1)b`, after which the `b` code supplies `β` zeros where the target
prefix permits only `β−s−2`; the only alternative contradicts
`|body|≥β−1`.  Hence `Δ=2μ` is impossible.

The single `b`-erasure pole was already excluded because its required
discrepancy lies strictly between `1` and `2`.  Thus the complete
distinguished-boundary `β` shell is pole-free.

**Scope:** later malformed transfers can re-enter a `β`-adic valuation shell
from projective states other than the distinguished boundary.  This theorem
does not classify those states.

**Use:** all distinguished-boundary danger is now concentrated in the
valuation-one finite-slope languages of
[`MM-S07`](#mm-s07-swapped-digit-finite-slope-reduction).

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#elimination-of-the-beta-shell);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** intersect each surviving primitive slope with the reverse
discrepancy language; a hit need only imply a genuine terminal suffix.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S09: Canonical swapped residue cannot hit a pole

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

The distinguished-boundary word `D_c^(β+1)` has

```text
d=1,       Δ₀=(9ρ−5)/2.
```

If this state met a valuation-one pole with side codes `P,V`, the pole
equation would reduce to

```text
D(9ρ−5)P=H(3ρ−1)V.
```

Modulo `ρ`, the left coefficient is `10`, `P≡−1`, and the right coefficient
is `1`.  Hence

```text
V≡ρ−10 (mod ρ).
```

The corresponding binary suffix under the swapped digit embedding is

```text
0^(β−3)100.
```

An admissible target block ends in an erasure.  Its lower word either contains
no rule and hence no `1`, or its last rule followed by one erasure ends in
`1100`; any other number of trailing erasures gives the wrong terminal zero
run.  Therefore the required suffix is impossible for `β≥4`.

**Scope:** this excludes one recurrent positive boundary residue, not every
positive `d=1` discrepancy.  It uses the target block's final-erasure
grammar.

**Use:** the Neary compiler has `β=10·period`, so the canonical all-erasure
branch is harmless for every emitted instance.  Any remaining
distinguished-boundary pole must come from a noncanonical positive near-match,
which is now a semantic source-halting question.

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#canonical-valuation-one-residue).

**Next:** prove that every other positive `d=1` near-match already implies
source halting.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S10: Swapped target-suffix sieve

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let a positive `3`-adic unit `Δ` meet a valuation-one target pole with side
codes

```text
P=μ+tU,       V>0.
```

The pole equation is

```text
ΔDP=H(3μ−Δ)V.
```

Every nonempty upper role word ends in binary `1`.  Hence `P`, modulo
`9ρ=3^(β+2)`, is the swapped code of `11·0^β`, namely `H`.  Both `H` and
`3μ−Δ` are units modulo `3`, so cancellation gives the fixed target suffix

```text
V ≡ σ_Δ := ΔD(3μ−Δ)⁻¹ (mod 9ρ).
```

This is an effective necessary suffix test.  If the lower word has at least
`β+2` letters, all `β+2` digits of the fixed-width residue must be nonzero and
its swapped binary decoding must obey the lower-role suffix grammar.  If the
lower word is shorter, then necessarily `V=σ_Δ`; only the canonical
base-three digits are word digits, while the leading zero padding is
harmless.  Thus a residue with an internal zero digit is impossible, and a
shorter all-nonzero residue leaves only the single exact candidate
`V=σ_Δ`.

In particular, for

```text
Δ=ρ−1
```

one has

```text
σ_Δ=8ρ−1,
```

whose `β+2` ternary digits are `21·2^β` and whose swapped binary suffix is

```text
01·0^β.
```

No lower spelling can contain this factor.  Every occurrence of `1·0^β`
inside a rule word is preceded by `1`; after an erasure, the next rule begins
with `11`.  Thus `Δ=ρ−1` cannot meet any target pole.

**Scope:** this is a necessary suffix sieve, not a classification of all
positive boundary discrepancies.  Residues passing the sieve still require
semantic or higher-carry analysis.

**Use:** apply before any target-word search.  It eliminates the principal
nonhalting positive residue found in the `β=4` small-envelope census and turns
many other candidate values into immediate digit contradictions.

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#target-suffix-sieve).

**Next:** classify the boundary values whose `σ_Δ` is a legal lower suffix;
the surviving nonterminal values must then be intersected with the reverse
Neary discrepancy.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S11: Decimal setter hyperbolicity

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

For the decimal setter [`MM-M05`](#mm-m05-decimal-swapped-setter), put `ρ=10^β`. In the
negative-J-fraction coordinate, every block has

```text
F_z(t)=u+v−v/t,       disc(F_z)=(u+v)²−4v.
```

A `b`-leading block has `u>1` and is automatically strictly hyperbolic. A `c`-leading block
has

```text
u≥45ρ/(52ρ−7).
```

Every lower `5/7` code lies between one half and seven ninths of its radix scale. Hence the
length defect `δ=|lower|−|upper|` places `v` in one of two disjoint regimes:

```text
δ≤β−1  ⇒  v≤7ρC/90,
δ≥β    ⇒  v≥ρC/2,

C=(502ρ−7)/((2ρ−7)(52ρ−7)).
```

Exact endpoint evaluation gives a positive discriminant in both regimes for `ρ≥100`. Thus
every nonempty square-run transfer is strictly hyperbolic; there are no parabolic endpoints and
no balanced elliptic corridor.

**Scope:** individual real hyperbolicity is not uniform projective avoidance. Products may be
elliptic by [`MM-O14`](#mm-o14-decimal-setter-elliptic-product), and rational pole equality
remains possible.

**Use:** replace the ternary balanced-corridor problem by a clean low/high decimal length split.
Do not mistake this for the missing arbitrary-depth theorem; finite positive rays are already
excluded by [`MM-O13`](#mm-o13-finite-positive-ray-setter-obstruction).

**Artifact:**
[`audits/m53-decimal-setter-hyperbolicity-2026-08-30.md`](audits/m53-decimal-setter-hyperbolicity-2026-08-30.md#length-shell-theorem).

**Next:** combine the real shells with the reciprocal two-prime carry
[`MM-S12`](#mm-s12-decimal-two-prime-carry); the remaining state is the normalized suffix on
the multi-role `(1,1)` resonance. Real cone refinements are closed.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S12: Decimal two-prime carry

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For the decimal setter [`MM-M05`](#mm-m05-decimal-swapped-setter), put

```text
E=9(2ρ−7),       G=502ρ−7,       T=EP+GV.
```

The homogeneous J-fraction state `t=X/Y` has the exact lift

```text
X′=TX−GVY,       Y′=Eμ10^mX.
```

With `Δ=Y−X` and `Z=(G/E)Δ/X`, this becomes

```text
X′=EPX−GVΔ,
Δ′=E(μ10^m−P)X+GVΔ,
Z′=(G/E)(μ10^m−P+VZ)/(P−VZ).
```

The resets are `Z=0,1`; at `Z=1`, a pole is exactly the genuine equality `P=V`. The
reciprocal chart `W=GY/X=EZ+G` contracts the same law to

```text
W′=EGμ10^m/(T−VW),       pole ⇔ W=T/V.
```

Admissible transfer blocks end in an erasure. Their trace shells are exactly

```text
multi-role:       (ν₂(T),ν₅(T))=(1,1),
single erasure:   (ν₂(T),ν₅(T))=(β+1,β).
```

The multi-role proof needs only `P≡V≡77 (mod 100)`, not the false stronger claim
`V≡177 (mod 200)`. The two singleton traces factor as

```text
T_Dc=2ρ(502ρ−7),
T_Db=2ρ(5200ρ²−18398ρ+2443).
```

If the output of a length-`m` block is the next block's pole, then

```text
T_target X′=EGμV_target10^mX.
```

Thus each prime satisfies

```text
ν_p(T_target)+ν_p(X′)=m+ν_p(X),       p∈{2,5}.
```

The multi-role shell preserves `ν₅(X)−ν₂(X)`; a singleton shell raises it by one.

**Scope:** this classifies the exact arithmetic required by a pole but does not exclude it.
The multi-role shell also shares normalized first decimal unit `3` with the distinguished reset,
so valuations and one unit digit cannot close arbitrary depth. Rule-ending fragments are not
admissible carry transitions.

**Use:** replace separate real, `2`-adic, and `5`-adic tests by the reciprocal recurrence. Any
complete proof must decide the normalized suffix of `T−VW` on repeated multi-role resonances.

**Formalization:** [`MatrixMortality/DecimalSetterArithmetic.lean`](MatrixMortality/DecimalSetterArithmetic.lean),
through `centeredCoordinate_step`, `reciprocalCoordinate_step`,
`successive_pole_shellBalance`, `multiErasure_trace_hasDecimalShell`, and the two
`single*Erasure_trace_hasDecimalShell` theorems.

**Artifact:**
[`audits/m53-decimal-setter-arithmetic-2026-08-30.md`](audits/m53-decimal-setter-arithmetic-2026-08-30.md).

**Next:** construct or refute a backward normalized-suffix automaton on the `(1,1)` shell.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S13: Decimal first-transfer extinction

**Kind:** obstruction
**Evidence:** formalized core; audited assembly
**Disposition:** active

For a length-`m` source block `u` followed by a prospective pole block `z`, the two decimal
resets give exact equations

```text
Z=0:   P_u T_z=Gμ10^mV_z,
Z=1:   (P_u−V_u)T_z=Gμ10^mV_z.
```

At `Z=0`, the multi-role trace shell `(1,1)` forces `m=1`; admissibility leaves the single
`c` erasure, whose image is exactly `Z=1`, so the next pole is the genuine terminal equality
`P_z=V_z`. The singleton shell `(β+1,β)` would force both `m=β+1` and `m=β` and is impossible.

At `Z=1`, put `D_u=P_u−V_u`. A multi-role target forces

```text
ν₂(D_u)=ν₅(D_u)=m−1.
```

Exact two-depth exhausts the lower code as the complete common decimal suffix. The remaining
`β+2`-digit upper prefix `H` satisfies

```text
P_z/V_z=G(10μ−H)/(EH).
```

A leading `b` makes the right side negative. A leading `c` followed by `b` or by the marker
gives the genuine pole one. Two leading `c` letters force the right side above `58/55`, while
the target's `5/7` prefixes force it below `58/55`.

For a singleton target,

```text
ν₅(D_u)=ν₂(D_u)+1,
ν₂(D_u)=m−β−1.
```

Suffix exhaustion now leaves `2β+2` digits. After division by `ρ`, the induced pole is below
six, while either singleton target is above six. Thus neither reset reaches a false pole after
one completed transfer.

**Scope:** the theorem removes the entire depth-one boundary, not arbitrary depth. After two
transfers the live numerator is no longer a raw difference of punctuated `5/7` codes, so suffix
exhaustion does not iterate for free. Lean checks the successive-pole identities, joint shell
balances, suffix exhaustion and factorization, and every rational interval comparison. The
finite Neary prefix trichotomy and first-two-digit assembly remain audited rather than one
end-to-end declaration.

**Use:** start every remaining decimal attack at depth two and preserve normalized suffix
content, not only the valuation pair or its first unit digit.

**Formalization:** [`MatrixMortality/DecimalSetterCarry.lean`](MatrixMortality/DecimalSetterCarry.lean),
through `resetZero_successivePole_identity`, `resetOne_successivePole_identity`,
`poleEquation_shellBalance`, `suffix_exhaustion_factorization`,
`forcedPole_ne_prefixTarget`, and `forcedPole_ne_singletonTarget`.

**Artifact:**
[`audits/m53-decimal-setter-first-transfer-2026-08-30.md`](audits/m53-decimal-setter-first-transfer-2026-08-30.md).

**Next:** construct an iterated normalized-suffix state for the reciprocal carry, or exhibit the
first false pole at depth at least two.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S14: Ordinary depth-two shell forest

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For an ordinary-reset pole after two decimal setter transfers, eliminating the intermediate
denominator gives

```text
K₂R₁=μGV₂10^(m₁)T₃,
K₂=T₂T₃−EμG10^(m₂)V₃.
```

Here `R₁` is a decimal unit. Writing A=`(1,1)` for a multi-role trace shell and
B=`(β+1,β)` for a singleton-erasure shell, unequal valuations in the two terms of `K₂`
survive exactly. The complete shell forest is

```text
A → A:  m₂=2, or m₁=1;
A → B:  m₂∈{β+1,β+2}, or m₁=1;
B → A:  middle D_b and m₁=β;
B → B:  impossible.
```

The `m₁=1` alternatives enter the distinguished reset and are already peeled by
[`MM-S13`](#mm-s13-decimal-first-transfer-extinction). Upper-length accounting makes every
remaining multi-role block in the table all `c`. Thus the ordinary depth-two frontier has only
the two-role A/A family, the `β+1`- and `β+2`-role A/B families, and the
`β`-role/`D_b` B/A family.

**Scope:** this is complete for the joint valuation shells at ordinary depth two. It does not
decide the surviving phase words, the distinguished-reset normalized suffix, or deeper poles.

**Use:** delete every ordinary depth-two word outside the displayed families before symbolic or
exact search. The B-to-B branch requires no further analysis.

**Formalization:** [`MatrixMortality/DecimalSetterCarry.lean`](MatrixMortality/DecimalSetterCarry.lean),
through `twoTransferTrace_identity`, `twoTransferTrace_shell_of_nonresonant`,
`ordinaryTwo_shellBalance`, `ordinaryTwoMultiToSingleton_gate`,
`ordinaryTwoSingletonToMulti_gate`, and `ordinaryTwoSingletonToSingleton_impossible`.

**Artifact:**
[`audits/m53-decimal-depth-two-shell-forest-2026-08-30.md`](audits/m53-decimal-depth-two-shell-forest-2026-08-30.md).

**Next:** apply the chamber extinctions in `MM-S15` and `MM-S16`, then transfer the surviving
method to the distinguished reset.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S15: Ordinary A-to-A length-two extinction

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** active

Use the negative J-fraction chart

```text
F(u,v,t)=u+v−v/t,          q(u,v)=v/(u+v),
u=P/(μA),                  v=LV/(μA).
```

Every encoded upper spelling begins in digit `5` and satisfies `4/5<u<101/100`. Target lower
spellings begin in digit `7` or in digits `55`; exact length-shell bounds put every target pole
below `9/10` or above `963/1000`.

For the length-two block `D_cD_c`, direct rational bounds place the entire image of the source
window strictly in `(961/1000,963/1000)`, between the two pole chambers. For `R_cD_c`, the
compiler-emitted body begins in `b` and forces its normalized lower spelling above `55ρ²`.
The resulting weight exceeds `265ρ`: a `c`-leading source maps below zero and a `b`-leading
source maps above one, while every positive pole lies in `(0,1)`.

**Scope:** these two phase words exhaust the all-`c` middle block of upper length two. Combined
with [`MM-S13`](#mm-s13-decimal-one-transfer-extinction) and
[`MM-S14`](#mm-s14-ordinary-depth-two-shell-forest), this closes the ordinary-reset A-to-A
depth-two branch. It does not decide A-to-B, B-to-A, the distinguished-reset depth-two branch,
or arbitrary depth.

**Use:** remove the complete A-to-A family from the ordinary depth-two search. Any surviving
ordinary false pole must lie in an A-to-B or B-to-A resonant family; the unbounded decimal front
is the distinguished normalized suffix.

**Formalization:**
[`MatrixMortality/DecimalSetterChamber.lean`](MatrixMortality/DecimalSetterChamber.lean), through
`doubleDeletion_step_in_gap`, `doubleDeletion_avoids_falsePrefixPole`,
`doubleDeletion_avoids_trueTruePrefixPole`, `ruleDeletion_cLeading_avoids_positivePole`,
`ruleDeletion_bLeading_avoids_positivePole`, and `compiler_ruleDeletionLowerWord_shape`.

**Artifact:**
[`audits/m53-decimal-length-two-chamber-2026-08-30.md`](audits/m53-decimal-length-two-chamber-2026-08-30.md).

**Next:** combine with the A-to-B and B-to-A extinction in `MM-S16`, then attack the
distinguished-reset normalized-suffix successor.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S16: Complete ordinary depth-two extinction

**Kind:** obstruction
**Evidence:** formalized core; audited assembly
**Disposition:** active

The two ordinary resonances left by [`MM-S14`](#mm-s14-ordinary-depth-two-shell-forest) after
[`MM-S15`](#mm-s15-ordinary-a-to-a-length-two-extinction) are both empty.

For A-to-B, encode an all-`c` phase word by `false=D_c` and `true=R_c`. Every nonempty word is
either all deletion or has the exact form `D_c^i R_c s`. In the all-deletion case, its normalized
lower code is below `7/9`, its lower J-weight is below `1/200`, and its image is above `3/4`;
either singleton target pole is below `1/100`. If the word contains `R_c`, the compiler body
begins in `b` and its encoded length forces normalized lower weight at least `55ρ²`. The J-weight
then exceeds `265ρ`: a `c`-leading source maps below zero and a `b`-leading source above one.
This argument covers every positive all-`c` length, hence both `β+1` and `β+2` resonances.

For B-to-A, the first image of `β` all-`c` roles and the following singleton `D_b` satisfy

```text
t₁=(50ρ²+2ρ−7)/(ρ(52ρ−7)),
t₂−1=(10ρ−1)(502ρ−7)/(20(52ρ−7)(50ρ²+2ρ−7))>0.
```

Every encoded target pole lies strictly between zero and one, so this family is impossible.

**Scope:** together, `MM-S13` through `MM-S16` extinguish every false pole through two completed
transfers from the ordinary reset. They do not decide the distinguished-reset depth-two suffix
corridor or any orbit after three or more transfers.

**Use:** remove the entire ordinary depth-two tree. The next live decimal front is the
distinguished normalized-suffix successor, not another ordinary phase or length split.

**Formalization:**
[`MatrixMortality/DecimalSetterResonance.lean`](MatrixMortality/DecimalSetterResonance.lean),
through `allC_cLeading_avoids_singletonPole`, `allC_bLeading_avoids_singletonPole`,
`encodedSingleB_after_repeatedC_avoids_encodedPole`, and `compilerBody_resonanceEnvelope`.

**Artifact:**
[`audits/m53-decimal-ordinary-depth-two-extinction-2026-08-30.md`](audits/m53-decimal-ordinary-depth-two-extinction-2026-08-30.md).

**Next:** transfer the shell and chamber cuts to the distinguished-reset normalized suffix and
then derive a depth-uniform recurrence or invariant.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S17: Recursive decimal carrier

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

Represent an A-shell state by decimal units `(N,D)` through `t=N/(10μD)`. A block with trace
`T`, lower code `V`, and upper length `m` leaves the residual

```text
R=NT−10μGVD.
```

If the following block is a multi-role pole, then `R` has exact shell `(m−1,m−1)`. Factoring
`R=10^(m−1)N'` gives the next carrier `(N',EN)`. For a suffix-peeled distinguished source,
the depth-two trace identity reduces exactly to

```text
(HT₂−10μGV₂)T₃=HEμG10^(m₂)V₃,
```

so this carrier begins at the existing two-prime peel and then iterates without changing
coordinates.

The initial `β+2`-digit raw head is `bTag`, the terminal `c b` head, or a two-`c` head.
Equal `2`/`5` depth excludes `bTag` because its code ends in `5`; the terminal head returns to
the already peeled distinguished reset. Only the two-`c` raw head enters the new corridor.

For every later block of upper length at least three, the carrier forces `N≡7D (mod 10)`.
The update `D'=EN` advances the pair to `D'≡9D`, `N'≡3D`; a second update returns to
`D''≡D`, `N''≡7D`. The final digit is therefore a compatible period-two cycle, not a
contradiction. Later numerators are generalized product residuals and need not be encoded-word
heads. [`MM-S18`](#mm-s18-length-two-carrier-extinction) subsequently excludes upper length
two, so the modulo-`100` premise holds on every surviving non-singleton transition.

**Scope:** this is an all-depth normal form for consecutive multi-shell resonances and a complete
unit-digit audit. It does not bridge generalized residuals back to raw heads, decide singleton
targets, or prove projective avoidance.

**Use:** carry `(N,D)` as the canonical state in every deeper decimal attack. Reject any proof
that reapplies the raw head trichotomy to `N'` without a structural bridge, or claims that the
last decimal digit descends.

**Formalization:**
[`MatrixMortality/DecimalSetterDepth.lean`](MatrixMortality/DecimalSetterDepth.lean), through
`peeledNumerator_multi_shell`, `peeledStep_factor`, `depthTwo_suffix_to_peeled`,
`peeledHead_trichotomy`, `bTag_cannot_head_equalDepth`,
`peeledNumerator_forces_lastDigit`, and `peeledLastDigit_twoStep`.

**Artifact:**
[`audits/m53-decimal-recursive-carrier-2026-08-30.md`](audits/m53-decimal-recursive-carrier-2026-08-30.md).

**Next:** after `MM-S18`, attach a higher decimal suffix language to generalized residuals of
upper length at least three.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S18: Length-two carrier extinction

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** active

Let `(N,D)` be a decimal-unit carrier and let the current and prospective target blocks both
have multi-role trace shell `(1,1)`. If the current block has upper length `m`, its residual is

```text
R=NT₂−10μGV₂D.
```

A following multi-role pole forces `R` to have exact shell `(m−1,m−1)`. At `m=2`, this would
make `R/10` a `2`-adic unit. But

```text
R/10=N(T₂/10)−μGV₂D,
```

and both terms on the right are `2`-adic units. Their difference cannot be a `2`-adic unit:
after division by the second term, that would make a rational number and its predecessor both
units at two, which would force the prime two to be odd. Hence `m≠2`; every non-singleton
transition has `m≥3`.

The proof is rational and insensitive to signs, integrality, or the choice of reset. The initial
peeled carrier has decimal-unit coordinates; `peeledDenominator_decimalUnit` preserves the
denominator condition, and factoring the forced residual shell preserves the numerator
condition. Thus no normalization step reopens the excluded transition.

**Scope:** this removes the exceptional length-two transition from every consecutive
multi-shell carrier orbit. It does not recognize the higher suffix of the remaining generalized
residuals, decide a transition into a singleton target, or prove projective avoidance.

**Use:** every surviving multi-shell transition satisfies the modulo-`100` premise of
`peeledNumerator_forces_lastDigit`. Higher-suffix attacks may start at upper length three.

**Formalization:**
[`MatrixMortality/DecimalSetterDepth.lean`](MatrixMortality/DecimalSetterDepth.lean), through
`peeledNumerator_twoAdic_deepens`, `peeledMultiPole_length_ne_two`, and
`peeledMultiPole_three_le_length`.

**Artifact:**
[`audits/m53-decimal-length-two-carrier-extinction-2026-08-30.md`](audits/m53-decimal-length-two-carrier-extinction-2026-08-30.md).

**Next:** classify the higher decimal suffix of the generalized residual on the now-uniform
`m≥3` corridor.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

## Rank-Three Binary Frontier

### R32-S01: Split return normal form

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

Let `A` be a unit and let `B=UV`, where `U` and `V` have explicit left and right inverses.
Every binary word containing `B` fractures into powers of `A` between copies of `B`, and

```text
B A^n₁ B ⋯ A^nₖ B = U (VA^n₁U) ⋯ (VA^nₖU) V.
```

Therefore `{A,B}` is mortal exactly when a finite product of return matrices `VAⁿU` is zero.
The converse covers every physical word, including empty runs and exterior powers of `A`.
The statement is dimension-free and valid over every nontrivial commutative semiring with the
displayed splittings.

**Scope:** a rank-two `3 × 3` cut over a field satisfies the splitting hypotheses after choosing
bases for its image and coimage. The theorem does not decide the resulting infinite return
family.

**Artifact:** `ReturnFamily.pairGenerator_isMortal_iff`,
`blockedProduct_eq_zero_iff`, and `returnHankel_card_le` in
[`ReturnFamily.lean`](MatrixMortality/ReturnFamily.lean).

**Use:** this is the canonical rank-`(3,2)` normal form. New attacks should modify or classify
the third-order return recurrence `VAⁿU`, not parse binary words again.

### R32-S02: Two-plane edge square

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For split finite-rank generators `Aᵢ=UᵢVᵢ`, every nonempty word is zero exactly when the
corresponding adjacent-edge product is zero:

```text
Cᵢⱼ = VᵢUⱼ,       Aᵢ₁⋯Aᵢₙ=0  ↔  Cᵢ₁ᵢ₂⋯Cᵢₙ₋₁ᵢₙ=0.
```

Conversely, four `2 × 2` edges indexed by two vertices assemble into two `3 × 3` generators
whenever the two edges entering each target agree on one shared source line. If one incoming
edge per target is split, both ambient generators have rank exactly two and their mortality is
the constrained edge-path problem.

**Scope:** this is an exact graph reduction and realization theorem. It does not erase the
two-vertex path constraint or prove that every resulting constrained projective problem is
equivalent to unconstrained `M₂(3)`.

**Artifact:** `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero`,
`TwoPlaneEdges.output_mul_input`, `TwoPlaneEdges.generator_rank`, and
`TwoPlaneEdges.isMortal_iff_exists_edgeProduct_eq_zero` in
[`EdgeCompression.lean`](MatrixMortality/EdgeCompression.lean) and
[`TwoPlaneEdges.lean`](MatrixMortality/TwoPlaneEdges.lean).

**Use:** analyze rank-`(2,2)` pairs as a two-node graph of invertible and rank-one Möbius edges.
Do not attribute an independent controller bit to the two planes.

### R32-O01: Rank-one profile collapse

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

If one binary generator is invertible and the other has rank one, the split-return theorem
reduces mortality to one scalar return

```text
vAⁿu = 0.
```

Cayley–Hamilton makes this an algebraic linear recurrence of order at most three. Skolem
decidability through order four therefore decides the profile. If both generators have rank
one, one-dimensional edge compression reduces mortality to finitely many adjacent scalar
tests.

**Scope:** the unit/rank-one return algebra is Lean-checked. The case of a second singular
generator and the decision theorem are independently audited; the latter is imported from
[Bacik](references/bacik-2025-order-four-skolem.md). This record does not supply a Lean
implementation of the Skolem algorithm.

**Artifact:** `ReturnFamily.rankOnePair_isMortal_iff` and
`ReturnFamily.wordProduct_unitSquare_eq_zero_iff` in
[`ReturnFamily.lean`](MatrixMortality/ReturnFamily.lean).

**Use:** remove every rank-one binary profile from the undecidability search. The only
structurally new profile is one unit and one rank-two matrix.

### R32-S03: ReturnSquare normal form

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

ReturnSquare takes

```text
A=diag(1,q,q²),       B=UV,
VAⁿU = T_c(qⁿ) =
  [(c+1)q²ⁿ−1   qⁿ]
  [c              qⁿ].
```

For integer `q≥2` and `c≠−1`, `A` is a unit and `B` has rank two. The zero-wait return
`T_c(1)=[1,1]ᵀ[c,1]` is an internal rank-one separator; every positive-wait return is a unit.
Physical mortality is therefore equivalent to one scalar bridge

```text
[c,1] T_c(q^n₁)⋯T_c(q^nₖ) [1,1]ᵀ = 0,       nᵢ≥1.
```

The projective action, squaring rail, target strip, reachable determinant, observable
determinant, exceptional parameter `c=−1`, and arbitrary-word converse are exact Lean
theorems.

**Scope:** ReturnSquare is a candidate family, not an undecidability reduction. Its parameter is
a fixed rational input, not writable storage.

**Artifact:** `ReturnSquare.physical_isMortal_iff_positiveBridge`,
`physical_isMortal_iff_oneReturn_or_longBridge`, `cut_rank`, and the projective identities in
[`ReturnSquare.lean`](MatrixMortality/ReturnSquare.lean).

**Use:** test arithmetic walls and same-zero modifications on a fully normalized rank-`(3,2)`
laboratory without reopening the physical-word grammar.

**Next:** [#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

### R32-O02: Two-return square cage

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The scalar coefficient of two positive returns factors through a quadratic in `c`. For integral
return scales `x,y≥2`, its discriminant lies strictly between `N²` and `(N+2)²`; parity excludes
the middle square. Hence the quadratic has no rational root. Every nonresonant ReturnSquare zero
contains at least three positive returns.

**Scope:** this excludes two-return bridges only. One-return resonances
`c=−q^−n` are genuine zeros. Prime-power bases are completely classified by `R32-D02`; a
length-at-least-three residue remains only for bases with several prime factors.

**Artifact:** `ReturnSquare.twoReturnDiscriminant_not_isSquare`,
`twoReturnCore_ne_zero`, `positiveBridge_pair_ne_zero`, and
`positiveBridge_zero_shape` in [`ReturnSquare.lean`](MatrixMortality/ReturnSquare.lean).

**Use:** any proposed kill must first exhibit a genuinely three-return mechanism or change the
return pencil.

### R32-O03: Reversible stack state tax

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The literal reversible projective operation exchanging `t` with `κt²` has return matrix

```text
[1−κt   −t]
[−κ    κt−1].
```

Its two-time block Hankel determinant is `κ²(q−1)⁴`. For `κ≠0` and `q≠1`, every exact return
realization therefore needs at least four ambient states.

**Scope:** this is an exact-series lower bound for the displayed reversible push/pop operation.
It does not exclude a different three-state series with the same zero behavior.

**Artifact:** `ReturnSquareTax.finiteReturnHankel_det` and
`reversibleStack_card_lower_bound` in
[`ReturnSquareTax.lean`](MatrixMortality/ReturnSquareTax.lean).

**Use:** do not add a literal reversible stack to ReturnSquare. A viable storage mechanism must
change nonzero values, use arithmetic residue, or abandon this two-mode return operation.

### R32-O04: Quadratic-pencil verification collapse

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let

```text
K(t)=C₀+tC₁+t²C₂.
```

Two complementary rigidity theorems hold over every linear ordered field.

1. If every `Cᵢ` is singular and `K(t)` projectively exchanges `t` with `κt²` for every `t`,
   where `κ≠0`, then all three coefficient matrices vanish.
2. If `K(t)` sends `t` to `t²` while `K(qt)` sends `t` to `qt²` for every `t`, where
   `q∉{0,1}`, then

   ```text
   K(t)=h(t) diag(t,1)
   ```

   for one scalar linear polynomial `h`. Projectively this is blind scaling `z↦tz` on every
   input, not an equality test.

**Scope:** these are exact projective identities for quadratic pencils. The first theorem
models a diagonal three-state realization whose three spectral coefficients each have rank at
most one. Neither theorem excludes a same-zero pencil, a nonsplit cubic action, or verification
restricted to a sparse set rather than a polynomial identity.

**Artifact:** `ReturnSquareNoGo.threeMode_swap_eq_zero` and
`verifiedPush_eq_blindScale` in
[`ReturnSquareNoGo.lean`](MatrixMortality/ReturnSquareNoGo.lean).

**Use:** abandon reversible stack completion inside the split `1,t,t²` architecture. A surviving
return pencil must use an irreducible ambient action, arithmetic carries, or changed nonzero
behavior.

### R32-O05: Jordan parity verifier collapse

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

A nonsemisimple ambient mode can carry the term `n(−1)ⁿ`, so the split quadratic-pencil
obstructions do not apply. Imposing the exact natural-number rails

```text
n even: n ↦ n/2,       n odd: n ↦ 3n+1
```

on `Kₙ=C₀+(−1)ⁿC₁+n(−1)ⁿC₂` first forces a five-parameter coefficient normal form. Requiring
the constant and drift modes to be singular, the zero return to be a separator, the alternating
mode to be tangent to the rank-one locus, and the first positive return in each parity to be
invertible leaves one nondegenerate branch up to scalar.

That branch is not a mortality compiler. Its integral physical pair preserves the line through
`(0,1,0)ᵀ` modulo seven: the Jordan generator acts by `−1` and the cut by `1`. Every product is
therefore nonzero in the finite quotient, hence nonzero over `ℤ`.

**Scope:** the uniqueness theorem is conditional on the displayed exact rails and explicit
rank-compatibility hypotheses. It does not classify every Jordan pencil, sparse rail, or
same-zero realization.

**Artifact:** `ReturnJordan.rail_normal_form`, `normalForm_unique`, and
`not_isMortal_generator` in
[`ReturnJordan.lean`](MatrixMortality/ReturnJordan.lean).

**Use:** do not reopen the literal parity-Collatz Jordan branch. A nonsemisimple candidate must
alter the rail, relax exact values, or defeat the finite-ray certificate.

### R32-D01: ReturnSquare immortality walls

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** stock

ReturnSquare is immortal in two large parameter regions:

```text
c ≥ 0,
c = −d  with  d > 1 + (q−1)/q².
```

The second wall is projective. Put

```text
s_d(t)=(d−1)t²+1,       β_d(q)=q/s_d(q).
```

The double cone representing slopes `(0,β_d(q)]` is backward invariant under every positive
return with scale `t≥q`. Pulling a zero bridge through its first return places the residual
vector in that cone; repeated backward invariance would place `[1,1]` there, contradicting
`β_d(q)<1`. The homogeneous proof is sign-invariant and never divides by a projective
denominator.

**Scope:** the inequality is a sufficient uniform wall, not a claimed optimal boundary.
[`R32-D02`](#r32-d02-prime-power-returnsquare-classification) closes the entire middle strip at
prime-power bases. The unresolved strip now concerns bases with at least two distinct prime
factors.

**Artifact:** `ReturnSquare.not_physical_isMortal_of_nonneg`,
`negativeStep_preimage_trap`, `transfer_neg_preimage_signedTrap`, and
`not_physical_isMortal_of_beyond_negative_wall` in
[`ReturnSquare.lean`](MatrixMortality/ReturnSquare.lean) and
[`ReturnSquareDynamics.lean`](MatrixMortality/ReturnSquareDynamics.lean).

**Use:** remove broad sign regions from searches and reuse the signed-cone pullback pattern for
other rank-two return pencils.

### R32-D02: Prime-power ReturnSquare classification

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** graduated

Let `q=pʳ`, where `p` is prime and `r>0`. Then the complete rational parameter classification
is

```text
ReturnSquare(q,c) is mortal  ↔  c=−q⁻ᵐ for some m≥0.
```

The proof normalizes `c=−d`. A return word with scale product `T` produces an integral bridge
polynomial whose constant coefficient is `T` and whose leading coefficient is `±T²`. The
rational-root theorem therefore forces a positive root `d` to be a power of `p` or its
reciprocal. Positive powers lie beyond `R32-D01`. A reciprocal `p⁻ᵏ` is a one-return resonance
when `r∣k`; otherwise a finite quotient preserves one or two nonzero projective rays and
certifies immortality.

The quotient supply is complete. The corpus proves Bang–Zsigmondy for every base `a>1` and
exponent `n>2`, with sole exception `(a,n)=(2,6)`. The exceptional pair is separated by
primitive factors of orders two and three. Exponent two uses a signed two-ray quotient.

**Scope:** the matrix classification requires a prime-power base. A ReturnSquare base with at
least two distinct prime factors can have rational roots supported on several primes and is not
classified here. The general Bang–Zsigmondy theorem is arithmetic infrastructure, not a
decision theorem for arbitrary return pencils.

**Artifact:** `exists_primitivePrimeDivisor`,
`ReturnSquare.physical_isMortal_primePower_iff`, and the bridge-polynomial and finite-wall
theorems in [`PrimitiveDivisor.lean`](MatrixMortality/PrimitiveDivisor.lean),
[`PolynomialPencil.lean`](MatrixMortality/PolynomialPencil.lean),
[`ReturnSquarePrimePower.lean`](MatrixMortality/ReturnSquarePrimePower.lean), and
[`ReturnSquareClassification.lean`](MatrixMortality/ReturnSquareClassification.lean).

**Use:** prime-power ReturnSquare is closed. Search multi-prime or genuinely multi-scale
families instead of longer words in this family.

### R32-M01: Generic reverse edge compiler

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

For a projective-incidence instance `G,H∈GL₂(ℚ)`, row `ℓ`, and column `c`, put

```text
α=ℓH⁻¹c,       β=ℓH⁻¹GH⁻¹c.
```

When `αβ≠0`, a rank-one loop `P`, two cross-edges, and one invertible loop can be chosen so that
successive visits to `P` test exactly `ℓWc=0` for `W∈{G,H}*`. The four edges satisfy the
one-line compatibility needed by [`R32-S02`](#r32-s02-two-plane-edge-square), hence assemble
into two rank-two `3 × 3` matrices.

The basis adaptation and arbitrary-path converse are now checked. Every path fractures at the
rank-one loop. Empty bridges evaluate to a nonzero multiple of that loop; every completed
nonempty bridge erases its invisible plane changes to `WH`, where `W∈{G,H}*`; unfinished
exterior blocks remain nonzero products of units. Thus a constrained path vanishes exactly when
one original incidence coefficient vanishes.

**Scope:** the theorem assumes `αβ≠0`. [`R32-S32`](#r32-s32-rank-two-punctuation-and-graph-removal)
proves that every rank-(2,2) pair reduces to one such generic instance after decidable edge
strata are discharged. [`R32-S35`](#r32-s35-positive-projective-incidence-genericization) now
reduces arbitrary PI₂ to at most two generic instances. This identifies their decidability
status but is not a many-one equivalence with unrestricted PI₂.

**Artifact:** `ReverseEdge.isMortal_adaptedGenerator_iff` and
`adaptedGenerator_rank` in [`ReverseEdge.lean`](MatrixMortality/ReverseEdge.lean).

**Use:** compile generic PI₂ into rank-(2,2); use `R32-S32` in the forward direction. Work now
belongs on normalized GPI₂ itself, not on exceptional-scalar transport or the two-vertex edge
language.

**Next:** decide or prove undecidable normalized GPI₂.
Tracked in
[#11](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/11).

### R32-M02: Finite-quotient sieve

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

Every zero-preserving monoid homomorphism sends mortal families to mortal families. Therefore
one finite quotient in which the image family is immortal is a complete no-certificate for the
original family. This includes reduction of integral candidates modulo primes and finite
projective-state quotients.

**Scope:** the theorem is one-sided. Survival modulo every tested modulus is evidence only and
does not imply rational mortality. No local-global completeness theorem is claimed. Moreover,
[`R32-O21`](#r32-o21-finite-image-positivity-collapse) proves that every finite ambient image is
automatically useless for the fixed Collatz positive-coset benchmark: there the image of the
positive monoid is already the whole generated group.

**Artifact:** `MatrixMortality.isMortal_map` and
`not_isMortal_of_map_not_isMortal` in
[`MatrixSemigroup.lean`](MatrixMortality/MatrixSemigroup.lean).

**Use:** use exact finite quotients to kill candidate return pencils before symbolic work, and
record any persistent residue automata as conjectural invariants rather than proofs. For
positive-coset membership, retain the spelling in a syntax-sensitive automaton; do not quotient
only the ambient group.

**Next:** build a typed finite-quotient census for irreducible cubic and two-prime return
families; promote only invariants that admit an unbounded lifting theorem.

### R32-M03: Two-scale return conversion

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

Replacing ReturnSquare's modes `(1,q,q²)` by `(1,p,q)` gives

```text
Rₙ =
  [(c+1)qⁿ−1   pⁿ]
  [c              pⁿ].
```

The zero return remains the internal rank-one separator and every positive return is invertible
for integral `p,q≥2` and `c≠−1`. The complete physical mortality problem is therefore still one
scalar bridge. Projectively, the exact defect identity

```text
Nₙ(z)−qⁿDₙ(z)=(qⁿ−1)(z−pⁿ)
```

verifies the rail `pⁿ↦qⁿ`; the terminal pullback tests `cqⁿz+pⁿ=0`. A nonsingular coefficient
Hankel section proves that this return series genuinely needs three states when
`p,q,1` are distinct and `c≠−1`.

Unlike ReturnSquare, this pencil has nonresonant multi-return zeros. At
`p=3`, `q=6`, `c=−1/9`, the integral physical pair satisfies

```text
B² A B A² B² = 0,
```

while both central positive returns are invertible and `−1/9` is not a one-return resonance.

**Scope:** one explicit nonresonant zero is not a computation. No self-verifying configuration
set, illegal-wait trap, or undecidability reduction is claimed.

**Artifact:** `ReturnConvert.physical_isMortal_iff_positiveBridge`,
`three_le_card_of_exact_realization`, `projective_rail`, `projective_target_defect`,
`example_zero`, and `example_nonresonant` in
[`ReturnConvert.lean`](MatrixMortality/ReturnConvert.lean).

**Use:** this is the preferred constructive `M₃(2)` laboratory. Seek a valuation-coded legal
rail whose wrong waits enter a permanent trap; test finite quotients before expanding the
architecture.

**Next:** classify the semigroup generated by the projective returns at multiplicatively
independent scales, or exhibit a guarded arithmetic simulation with an all-waits converse.
Tracked in
[#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

### R32-M04: Amalgamated valuation guard

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

For a prime `p`, depth `s≥2`, center `α`, and reset `ρ`, put `δ=ρ−α`. The split
three-mode return family has ambient action

```text
A = diag(1,p⁻¹,p^(s−1))
```

and exact rescaled returns

```text
Gₙ =
  [α+δpˢⁿ    −αpⁿ−δpˢⁿ]
  [1                    −pⁿ].
```

The zero return is the nonnilpotent rank-one outer product
`(ρ,1)ᵀ(1,−1)`; every positive return is invertible. The physical cut has rank exactly two,
the coefficient Hankel certificate has rank three, and the existing split-return compiler
reduces every arbitrary physical zero word to one scalar bridge.

Assume `α`, `α−1`, and `δ` are p-adic units and `ρ` has positive valuation. On `ℙ¹(ℚ)`, the
positive return obeys the cross-multiplied verifier

```text
Φₙ(z)−α = δpˢⁿ(z−1)/(z−pⁿ).
```

Every nonterminal point outside the positive-valuation region forms a forward-invariant trap.
For a live point `z`, surviving a selected wait `n` forces both

```text
n = vₚ(z),                  vₚ(z−pⁿ)=sn.
```

Thus independently selected wrong waits are permanently poisoned without another state or
generator.

**Scope:** this is not an undecidability theorem. It converts physical mortality exactly into
target reachability for one deterministic rational p-adic map. No source computation has yet
been compiled into that map, and no decision algorithm for its orbit is known.

**Artifact:** `ReturnGuard.physical_isMortal_iff_positiveBridge`,
`ReturnGuard.trap_forward`, `live_step_forces_ready`,
`parameters_three_le_card_of_exact_realization`, and the exact integer example
`ReturnGuard.Examples.integer_zero_word` in
[`ReturnGuard.lean`](MatrixMortality/ReturnGuard.lean),
[`ReturnGuardDynamics.lean`](MatrixMortality/ReturnGuardDynamics.lean), and
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean).

**Use:** the separator-verifier-trap amalgamation problem is closed. Future attacks should work
on the deterministic tail recurrence, not add parser states or repair malformed wait words.

**Next:** classify or universalize the guarded arithmetic orbit in
[`R32-S04`](#r32-s04-guarded-return-normal-form).
Tracked in
[#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

### R32-S04: Guarded return normal form

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Write a ready point uniquely as

```text
E(a,X)=pᵃ+pˢᵃ/X,            vₚ(X)=0.
```

The sole legal wait is `a`, and its payload update is

```text
E(a,X) ↦ α+(ρ−α)(pˢᵃ+(pᵃ−1)X).
```

Every positive ready cylinder can reach every other: the inverse unit tail is an explicit
fractional-linear expression. The terminal tail is likewise explicit and unique. Nevertheless,
all arbitrary physical paths are already covered. Lean proves

```text
physical mortality
  ↔ some positive-return projective word reaches 1
  ↔ TransGen LegalStep ρ 1.
```

The last relation is functional. Its proof reads physical matrix products in their actual
right-to-left action order, propagates trap invariance through every suffix, and forces every
surviving step to be ready. The construction therefore has neither an intended-word loophole
nor a hidden regular-language restriction.

**Scope:** the complete inverse grammar shows local symbolic freedom, not computational
universality. The rational tail couples successive cylinder choices globally.

**Artifact:** `readyTail_isUnit`, `readyState_readyTail`, `readyState_ready`,
`ready_transition`, `legalValue_eq_one_iff`, `legalStep_functional`, and
`physical_isMortal_iff_guardedReachable` in
[`ReturnGuardDynamics.lean`](MatrixMortality/ReturnGuardDynamics.lean).

**Use:** formulate the surviving `M₃(2)` attack entirely as reachability for this deterministic
arithmetic system. Matrix rank, punctuation, malformed words, illegal waits, and exact
three-state minimality no longer belong to the open obligation.

**Next:** either reduce a universal deterministic computation to `GuardedReachable`, or find a
finite-height, p-adic contraction, or continued-fraction invariant deciding it.

### R32-S05: Prefix shift and affine residual

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

In the shifted projective coordinate

```text
x=z/(z−1),
```

one legal guard step factors into a variable-length affine prefix decoder and one fixed
fractional-linear map:

```text
Dₐ(x) = (pᵃ+(1−pᵃ)x)/pˢᵃ,
K(w)  = (αw+δ)/((α−1)w+δ),
x'    = K(Dₐ(x)).
```

Readiness is exactly the assertion that `Dₐ(x)` is a p-adic unit. Parameterizing one branch by

```text
Φₐ(v)=(pˢᵃv−δ)/(α−pᵃ)
```

turns the reciprocal residual update into

```text
1/Rₐ(Φₐ(v))
  = [δ(1−pᵃ)/(α−pᵃ)] · 1/v
    + [(α−1)pˢᵃ/(α−pᵃ)].
```

The Lean statements retain every required denominator hypothesis. The shift identity itself
uses total rational division at a terminal output; it is interpreted projectively only away
from the input target and pole.

**Scope:** affine residual transport can propagate unbounded carries, but it does not provide a
finite-token compiler or a decision procedure.

**Artifact:** `ReturnGuard.shift_step`, `ready_iff_prefixDecode_isUnit`,
`residualStep_branchCylinder`, and `reciprocalResidual_affine` in
[`ReturnGuardShift.lean`](MatrixMortality/ReturnGuardShift.lean).

**Use:** work on the arithmetic residue as a prefix/carry transducer. Any proposed finite-token
simulation must still evade the closed-substitution collapse.

**Next:** classify the iterated affine residuals on the resonant cylinders isolated by
[`R32-S06`](#r32-s06-resonance-localization).

### R32-S06: Resonance localization

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Let `u=α/δ`, and write a unit tail at exact depth `n` as

```text
X=u+pⁿY,                  vₚ(Y)=0.
```

For a current wait `a`, the three summands of the legal output have valuations `a`, `sa`, and
`n`. Lean proves the complete trichotomy:

```text
n<a  ⇒ every ready continuation has next wait n<a;
n>a  ⇒ the output is not ready, and every further positive step lies in the trap;
n=a  ⇒ the sole branch on which the wait can be preserved or increased.
```

The exact center `X=u` also admits no ready continuation. Consequently every infinite ready
chain meets the equal-depth resonance shell arbitrarily far along the chain; otherwise its
positive waits would descend forever in `ℕ`.

At resonance the output factors as `pᵃ C`. If `C=pʰU` with `U` a unit, readiness at the next
wait `a+h` is equivalent to

```text
vₚ(U−1)=(s−1)(a+h).
```

This corrects the reported depth `(s−1)a+sh`, which was too large by `h`.

**Scope:** resonance localization does not classify the resonant itinerary. It proves that all
nondecreasing or infinite behavior is confined to the nested equal-depth shell.

**Artifact:** `ReturnGuard.nonresonant_nextWait_lt`,
`infinite_ready_chain_resonates`, `primePower_mul_ready_iff`, and
`resonance_ready_iff` in
[`ReturnGuardResonance.lean`](MatrixMortality/ReturnGuardResonance.lean).

**Use:** discard generic unit tails. Universality or decidability must be proved inside the
iterated resonance carry.

**Next:** seek an effective nucleus or nonperiodic rational itinerary for the nested normalized
residual.

### R32-O06: Rational affine-wait rail rigidity

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let a reduced rational chart be `f=P/Q`, with `P,Q∈ℚ[X]`, `P(0)≠0`, and let the proposed wait
update be

```text
a ↦ da+h,                 t=pᵃ ↦ λtᵈ,   λ=pʰ.
```

If the guarded rail equation holds at infinitely many defined prime-power samples, clearing
denominators gives one polynomial identity. The formal proof extracts the stronger divisibility

```text
P(λXᵈ) ∣ Q(X).
```

Degree comparison first forces `d=1` and `deg P=deg Q`. Constant and leading coefficients then
force

```text
α=λ^(s+deg P).
```

Since `α` is a p-adic unit, this contradicts `vₚ(λ)≠0`. Thus no rational ready-tail chart can
implement a nontrivial affine change of wait on infinitely many configurations. The intermediate
degree theorem already excludes every `d>1` for any nonzero `λ`.

This proof is shorter and stronger than the reported algebraic-closure root count: reducedness
and polynomial divisibility suffice.

**Scope:** the theorem concerns one reduced rational chart. A finite-control cycle is excluded
only after its charts are shown to compose to this rail equation; that compiler-level corollary
is not represented as a Lean type. Identity-wait charts and genuinely nonrational nested
resonance remain possible.

**Artifact:** `ReturnGuard.Rail.scalePower_numerator_dvd_denominator`,
`identity_forces_linear_center`, `no_rational_affineWait_rail`, and
`no_infinite_primePower_affineWait_rail` in
[`ReturnGuardRail.lean`](MatrixMortality/ReturnGuardRail.lean).

**Use:** abandon rational monomial counter rails, rational increment/decrement gauges, and
rational affine counter cycles. The live construction must use the nested resonance itself.

**Next:** decide whether rational resonant itineraries have an effective eventual-periodicity
theorem, or construct a rational nonperiodic resonance stack.

### R32-S07: Decoded residual address normal form

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

The reciprocal center displacement

```text
w = (ρ−α)/(z−α),             z = α+(ρ−α)/w
```

is the canonical global state. Reset is `w=1`; the terminal point is
`τ=−(ρ−α)/(α−1)`. For every positive wait `a`, the exact legal domain is one rational p-adic
sphere

```text
Bₐ = βₐ+pˢᵃ ℤₚ×,            βₐ=−(ρ−α)/(α−pᵃ).
```

On rational points the inverse branch

```text
gₐ(v) =
  (ρ−α)(pˢᵃv−1) /
  (α−pᵃ−(α−1)pˢᵃv)
```

maps the rational unit shell bijectively onto `Bₐ`. The spheres are pairwise disjoint, so the
state itself determines the wait. Lean transports every original legal step through this
coordinate and proves

```text
physical mortality
  ↔ ∃ nonempty positive address (a₀,…,aₙ), 1=gₐ₀∘⋯∘gₐₙ(τ).
```

Distinct positive branches have no common finite fixed point. Hence their nonlinear interaction
cannot be removed by choosing one finite affine chart. The exact rational period-three orbit

```text
1 ─1→ 5/17 ─2→ 43/283 ─3→ 1
```

is also checked. Its first two legs are equal-depth resonances and its third is a strict
nonresonant descent. Rational survival is therefore not confined to fixed points or two-cycles.

**Scope:** the Lean theorem is rational and exact. It does not claim a topological conjugacy on
all of `ℚₚ`, nor eventual periodicity of rational addresses.

**Artifact:** `ReturnGuard.residualEquiv`,
`residualBranch_iff_exists_inverseResidual`,
`residualBranch_wait_unique`, `guardedReachable_iff_decodedReachable`,
`physical_isMortal_iff_inverseAddress`, `residualFixed_exclusive`,
`ReturnGuard.Examples.cycle_decoded_orbit`, and `cycle_first_two_resonant` in
[`ReturnGuardGauss.lean`](MatrixMortality/ReturnGuardGauss.lean),
[`ReturnGuardAddress.lean`](MatrixMortality/ReturnGuardAddress.lean), and
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean).

**Use:** replace the wait-tail bookkeeping by one countably branched Möbius system. The remaining
decision question is finite inverse-address membership of one rational point, not legality of
arbitrary physical words.

**Next:** attack rational address arithmetic with the local-global sieve in
[`R32-M05`](#r32-m05-cyclotomic-reset-or-cancellation-sieve), or exhibit a rational
non-eventually-periodic address carrying universal computation.

### R32-M05: Cyclotomic reset-or-cancellation sieve

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

Write `α=A/L`, `ρ−α=D/L`, and a primitive decoded residual as `m/n`. One surviving wait `a`
has the exact integral recurrence

```text
pˢᵃ m̃ = (A−Lpᵃ)m+Dn,
ñ      = (A−L)m+Dn.
```

Lean proves that projectivizing `(m̃,ñ)` recovers the decoded residual map exactly. More
generally, a common divisor of the image of any primitive pair under a `2 × 2` integer matrix
divides its determinant. Applied here, every common reduction factor `g` coprime to `p` satisfies

```text
g ∣ DL(pᵃ−1).
```

If a prime `ℓ` divides `pᵃ−1`, then one exact dichotomy holds after primitive reduction:

```text
ℓ ∣ g
  or
m′ ≡ n′ (mod ℓ).
```

Thus every cyclotomic prime either disappears into a visible common cancellation or resets the
reduced projective point to one. There is no third escape.

The cancellation branch itself is now exact. For every positive wait and every divisor
`d ∣ pᵃ−1`, primality is unnecessary: `d` is automatically coprime to `p`. If

```text
(m̃,ñ)=g(m′,n′),    gcd(m′,n′)=1,
```

then Lean proves

```text
d ∣ g
  ↔
(A−L)m ≡ −Dn (mod d).
```

The right side is precisely projective congruence of the source residual `m/n` with the terminal
residual `−D/(A−L)`. A swallowed cyclotomic factor is therefore not an opaque failure of
reduction: the source state already shadows the terminal divisor modulo that entire factor.

**Scope:** this is a one-step local-global theorem, not a decision algorithm. Terminal
congruence may recur at unbounded orders, and no bound on the accumulated cyclotomic factors or
the terminal defect is yet proved.

**Artifact:** `ReturnGuard.integralStep_realizes_residualStep`,
`commonDivisor_dvd_det`, `integralStep_commonDivisor_dvd_cyclotomicSupport`, and
`integralStep_cyclotomic_reset_or_cancel`, together with the stronger
`divisor_pow_sub_one_isCoprime_base` and
`integralStep_cyclotomic_cancel_iff_terminalCongruent`, in
[`ReturnGuardArithmetic.lean`](MatrixMortality/ReturnGuardArithmetic.lean).

**Use:** finite quotients should track a projective residue plus an explicit cancellation state.
An unreachable terminal residue certifies immortality. Reaching the cancellation state now
certifies terminal congruence upstairs and charges the swallowed factor to the integral terminal
defect.

**Next:** track primitive parts of `pᵃ−1` against the height of the terminal defect, or prove that
the resulting terminal-congruence histories form an effective finite nucleus.

### R32-S08: Cumulative endpoint recurrence

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For `α=A/L` and `ρ−α=D/L`, retain every signed primitive reduction factor in one cumulative
endpoint pair `(Rᵢ,βᵢ)`. Its reset is `(A+D−L,1)`, and one wait `aᵢ` obeys

```text
p^(saᵢ)βᵢ₊₁ = Rᵢ − L(p^aᵢ−1)βᵢ,
Rᵢ₊₁ = D Rᵢ + (A−L)βᵢ₊₁.
```

The target is unique for a fixed source and wait. Every primitive residual reduction induces
this step after its removed signed content is absorbed into the target pair. Content is therefore
a local Smith factor derived from the pair, not an independent dynamical register.

Two steps eliminate the intermediate numerator:

```text
p^(saᵢ₊₁)βᵢ₊₂
  = (A + Dp^(saᵢ) − Lp^aᵢ₊₁)βᵢ₊₁ + DL(p^aᵢ−1)βᵢ.
```

Equivalently, with `R₋₁=1`, the cumulative numerator alone satisfies

```text
p^(saᵢ)Rᵢ₊₁
  = (Dp^(saᵢ)+A−Lp^aᵢ)Rᵢ + DL(p^aᵢ−1)Rᵢ₋₁.
```

Terminality is `Rᵢ=0`; the first row of the full endpoint product is
`p^(sΣaᵢ)Rᵢ`.

Primitive reduction remains recoverable: removed content is the gcd of the endpoint prequotient
with `DL(pᵃ−1)`, consecutive primitive denominators are coprime, and the next denominator is
coprime to the complementary content. Reverse reconstruction gives a fixed target resultant.
Its proof requires `pᵃ−1 ∣ p^(sa)−1`; omitting that geometric factor is invalid.

Lean checks two terminal executions and the projective period-three return:

```text
(308,1) → (−12152,−4) → (0,−1240),
(−67704,1) → (7041216,−504) → (0,41664),
(−2720,1) → (1267840,−800) → (−15411200,192640)
          → −15411200·(−2720,1).
```

**Scope:** the recurrence is exact and content-free, but it does not bound integral height or
prove that every infinite rational execution returns projectively. Primitive content theorems
remain useful as derived local arithmetic; they no longer define the state.

**Artifact:** `ReturnGuard.primitiveIntegralStep_cumulativeEndpointStep`,
`CumulativeEndpointStep.target_unique`, `cumulativeNumerator_recurrence`, and
`terminalTruncant_eq_cumulativeNumerator` in
[`ReturnGuardCumulative.lean`](MatrixMortality/ReturnGuardCumulative.lean); exact executions in
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean); audit in
[`m32-fixed-cusp-record-ascent-2026-08-01.md`](audits/m32-fixed-cusp-record-ascent-2026-08-01.md).

**Use:** study one second-order exact-division recurrence. Quotient and height arguments should
be stated on `(Rᵢ,βᵢ)` and derive primitive contents only when charging local cancellation.

**Next:** prove that every infinite rational cumulative execution has proportional consecutive
pairs effectively, or construct one nonperiodic rational execution. A proof must control blocks
whose wait reaches a new maximum; this is the live mountain-gap problem.

### R32-S09: Complete cancellation law

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Let one integral step send a source pair `(m,n)` to a raw pair `(m̃,ñ)`, and write

```text
(m̃,ñ)=g(m′,n′),    gcd(m′,n′)=1.
```

For every integer divisor `d` coprime to the base `p`, Lean proves the exact equivalence

```text
d ∣ g
  ↔
d ∣ T(m,n)
  and
d ∣ L(1−pᵃ)m,
```

where `T(m,n)=(A−L)m+Dn` is the terminal defect. The theorem contains both previously separated
mechanisms:

- if `d ∣ pᵃ−1`, the displacement condition is automatic and cancellation is terminal
  congruence;
- if `d` lies in the fixed support of `L` or the source numerator `m`, cancellation need not be
  cyclotomic, but it is still charged to the same terminal defect.

Prime-power divisibility makes the local multiplicities exact. For every prime `ℓ≠p`, assuming
the three relevant integers are nonzero,

```text
vℓ(g)=min(vℓ(T(m,n)), vℓ(L(1−pᵃ)m)).
```

No further common-factor mechanism exists away from the base prime. In particular, the
determinant-support theorem is a consequence-level bound; the intersection law is the local
normal form.

**Scope:** the exact displacement valuation contains `vℓ(m)`, but this does not survive as an
unbounded size contribution on primitive legal states. The determinant-support theorem bounds
the attained cancellation by `vℓ(DL(pᵃ−1))`; [`R32-S10`](#r32-s10-logarithmic-wait-and-height-envelope)
records the resulting logarithmic law. The source valuation still decides whether the bound is
attained.

**Artifact:** `ReturnGuard.integralStep_cancel_iff_terminalDefect_and_displacement` and
`ReturnGuard.integralStep_commonFactor_padicValInt` in
[`ReturnGuardArithmetic.lean`](MatrixMortality/ReturnGuardArithmetic.lean).

**Use:** replace every coarse gcd estimate by a prime-local equality. Outside fixed support this
recovers cyclotomic terminal shadowing; inside fixed support it isolates the exact valuation
state that a normalization quotient must retain.

**Next:** combine the exact attainment condition with the global logarithmic height envelope.
The unresolved state is terminal congruence, not the magnitude of fixed-prime cancellation.

### R32-S10: Logarithmic wait and height envelope

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For a primitive integral source pair of height

```text
H(m,n)=max(|m|,|n|),
```

every base-coprime primitive-reduction factor satisfies

```text
|g| ≤ |DL| |pᵃ−1|.
```

Prime locally,

```text
vℓ(g) ≤ vℓ(D)+vℓ(L)+vℓ(pᵃ−1).
```

Thus the source term in the complete displacement formula affects attainment but not size. For
an odd fixed prime `ℓ`, if `r` is any seed period with `ℓ ∣ pʳ−1`, lifting the exponent gives

```text
vℓ(p^(rk)−1)=vℓ(pʳ−1)+vℓ(k)
            ≤vℓ(pʳ−1)+logℓ(k).
```

Lean proves the corresponding logarithmic bound at `ℓ=2`, separating odd and even multipliers
through the two-adic lifting formula.

The same integral recurrence has a uniform archimedean envelope. If the depth `s≥2` and the next
numerator is nonzero, then

```text
a ≤ log_p((|A|+|D|+|L|)H(m,n)).
```

Before and after primitive reduction,

```text
H(m′,n′) ≤ (|A|+|D|+|L|)H(m,n).
```

The wait therefore grows at most logarithmically in current height, while height grows by at
most one fixed factor per transition. Along an orbit, waits can grow at most linearly in elapsed
steps.

**Scope:** this is not a finite nucleus. Linear wait growth and exponential height growth remain
ample enough for counter-like computation. The theorems bound cancellation and scale but do not
decide the terminal congruences that select a rational inverse address.

**Artifact:** `ReturnGuard.integralStep_commonFactor_padicValInt_le_support`,
`integralStep_commonFactor_natAbs_le_support`, `padicValNat_pow_mul_sub_one_le`,
`padicValNat_two_pow_mul_sub_one_le`, `integralStep_wait_le_log_height`, and
`integralStep_reduced_height_le` in
[`ReturnGuardValuation.lean`](MatrixMortality/ReturnGuardValuation.lean).

**Use:** exclude any universality proposal requiring one step to generate a superlinear clock or
super-Lipschitz rational height. For a decision proof, combine the envelope with terminal-defect
congruence to seek a finite set of recurrent projective residues.

**Next:** derive an iterated terminal-defect height or finite-quotient recurrence that uses the
linear wait bound. Conversely, construct a legal rational orbit whose terminal congruences
saturate that envelope and encode an unbounded counter.

### R32-S11: Primitive-factor terminal gate

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For one legal integral step, let `g` be the primitive-reduction factor and let `T` be the source
terminal defect. Given any finite family `S` of distinct cyclotomic primes dividing `pᵃ−1`,
Lean combines pairwise coprimality with the reset-or-cancellation theorem to prove

```text
|T| < ∏_{ℓ∈S} ℓ
  ⇒
T=0
  or
∃ℓ∈S, ℓ∤g and m′≡n′ (mod ℓ).
```

Thus a family whose squarefree product is larger than the terminal defect cannot disappear
silently. Either the source is already the true terminal projective point, or one factor
survives primitive reduction and resets the reduced state to one in a finite projective
quotient. This squarefree interface is deliberately strong: the witness prime is known not to
divide `g` and therefore survives as a quotient transition.

The canonical family consists of the prime factors of `Φ_a(p)` which do not divide `a`. Every
such factor is formally proved to be a primitive prime divisor of `pᵃ−1`. Writing

```text
radₚᵣᵢₘ(Φ_a(p)) = ∏ {ℓ : ℓ∣Φ_a(p), ℓ∤a},
```

the checked height form is

```text
radₚᵣᵢₘ(Φ_a(p)) >
  (|A−L|+|D|)H(m,n)
⇒
T(m,n)=0
or
some exact-order quotient sees m′≡n′.
```

Equivalently, on a nonterminal step for which every primitive quotient reset is ruled out,

```text
radₚᵣᵢₘ(Φ_a(p))
  ≤ |T(m,n)|
  ≤ (|A−L|+|D|)H(m,n).
```

The complementary interface now retains multiplicity. Define

```text
Pₐ(p)=∏ ℓ^vℓ(Φₐ(p)),
```

over the prime factors `ℓ` of `Φₐ(p)` which do not divide `a`. If no such prime resets the
reduced target, the whole prime power is swallowed:

```text
Pₐ(p) ∣ g.
```

Consequently a nonterminal, nonzero step at depth `s` satisfies both

```text
Pₐ(p) ≤ (|A−L|+|D|)H,
p^((s−1)a)Pₐ(p) ≤ (|A|+|D|+|L|)H.
```

The first inequality charges the full part to the terminal defect. The second charges it to the
same content budget as the distinguished p-adic wait scale. Unlike the squarefree theorem, this
does not assert that a reset prime survives reduction: it says that absent every reset, no
primitive multiplicity can disappear without being paid by `g`.

Glasby-Lübeck-Niemeyer-Praeger identify the corresponding strong primitive part as `Φₐ(p)` or
`Φₐ(p)/r` for `a>2`, where `r` is the largest prime divisor of `a`. Lean now reconstructs the
weaker exact interface needed for growth,

```text
Φₐ(p) ∣ aPₐ(p),
(p−1)^φ(a) ≤ aPₐ(p),
```

and hence proves

```text
p^a(p−1)^φ(a) ≤ a(|A|+|D|+|L|)H
```

at depth two on every no-reset branch.

This is the precise local-global gate sought by [`R32-M05`](#r32-m05-cyclotomic-reset-or-cancellation-sieve).
It removes repeated prime powers as an uncontrolled escape and splits the arithmetic into a
surviving finite quotient or full strong-primitive absorption.

**Scope:** inherited height can still pay the full factor; the inequality is local and must be
combined with global adelic amortization. The exact equality with the published `Φ⁎ₐ(p)` is not
formalized, but is no longer needed for the displayed growth bound. A surviving reset likewise
supplies a finite exact-order transition, not automatic rejection of the terminal residue.

**Artifact:** `primitiveCyclotomicPrimes`, `primitiveCyclotomicRadical`,
`primitiveCyclotomicPart`, `primitiveCyclotomicPart_pos`,
`cyclotomicValue_dvd_exponent_mul_primitiveCyclotomicPart`,
`sub_one_pow_totient_le_exponent_mul_primitiveCyclotomicPart`,
`primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes`,
`terminal_or_exists_cyclotomic_reset`, `cyclotomicProduct_le_terminalDefect_of_no_reset`,
`terminalDefect_zero_or_exists_primitive_reset`,
`primitiveCyclotomicRadical_le_height_of_no_reset`,
`primitiveCyclotomicPart_dvd_common_of_no_reset`, and
`primitiveCyclotomicPart_le_height_of_no_reset` in
[`ReturnGuardTerminalGate.lean`](MatrixMortality/ReturnGuardTerminalGate.lean), together with
`primitiveCyclotomicPart_mul_wait_le_height_of_no_reset` and
`strongPrimitivePressure_le_height_of_no_reset` in
[`ReturnGuardAdelic.lean`](MatrixMortality/ReturnGuardAdelic.lean). Independent synthesis:
[`m32-number-theory-triangulation-2026-08-06.md`](audits/m32-number-theory-triangulation-2026-08-06.md).

**Use:** split the remaining decision attack cleanly. A surviving primitive factor enters a
finite projective graph of exact multiplicative order `a`; if every primitive reset is absent,
the entire strong primitive part is charged to one explicit content and height budget.

**Next:** combine the checked strong primitive pressure with either a positive Smith-block
height descent or the exact gauged Smith cocycle in an adelic continued-fraction inequality.
Do not return to a squarefree-radical lower-bound problem unless a surviving quotient witness
is specifically required.

### R32-S12: Exact-order projective automata

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Let `ℓ` be a primitive prime divisor of `pᵉ−1`. Clearing denominators in the decoded residual
recurrence gives one homogeneous `2 × 2` transfer matrix. Modulo `ℓ`, every entry depends only
on the wait modulo `e`; projectivization therefore produces a finite automaton on

```text
ℙ¹(𝔽ℓ) ⊔ {cancelled}.
```

The extra state is exact arithmetic, not an overapproximation. For every primitively reduced
integral step, the quotient enters `cancelled` if and only if `ℓ` divides the common reduction
factor. Otherwise it follows the reduced projective point exactly. Consequently, any finite set
of quotient states which contains the reset, is closed under all `e` residue transitions, and
contains neither `cancelled` nor the terminal ray is a kernel-checked certificate excluding
every primitive integral terminal execution.

There is a uniform rank-one subfamily. If additionally `ℓ∣D`, every transfer loses its second
column. Assume `A−L` is nonzero modulo `ℓ` and

```text
A−Lpʳ ≠ 0  for every 0≤r<e.
```

Then every residue transition sends every nonzero affine ray to another nonzero affine ray,
while the terminal residual `−D/(A−L)` becomes zero. The entire nonzero affine shell is a safe
invariant, yielding an immediate no-certificate. Equivalently, the center ratio `A/L` must avoid
the cyclic subgroup generated by `p`.

For the rational period-three survivor with parameters

```text
p=3, s=2, A=−953, D=473, L=2240,
```

the primitive quotient `ℓ=11`, of exact order five, collapses all five residue transfers onto
the four affine rays `{1,4,6,10}`. This set is closed, while the terminal ray is `0` and
`cancelled` is absent. Lean therefore excludes every primitive integral execution from reset
pair `(1,1)` to terminal pair `(−473,−3193)`, not merely the displayed period-three orbit.
Independently, determinism of the decoded relation and the same three-state rational invariant
prove that the corresponding physical matrix pair is immortal.

**Scope:** this proves a finite certificate language, not its completeness. Many primitive
quotients are saturated and admit both terminal and cancellation paths. The concrete
modulo-eleven collapse is unusually strong because `11∣D`, making every residue transfer rank
one with zero second column. [`R32-S13`](#r32-s13-canonical-decoded-integral-lift) now supplies
the formerly missing bridge from every decoded rational execution to primitive integral
execution. Quotient invariants are therefore physical immortality certificates, but no theorem
asserts that every immortal parameter set admits one.

**Artifact:** `ReturnGuard.quotientTransfer_mod_of_primitive`,
`quotientTransition_integralStep_eq_cancelled_iff`,
`no_primitiveExecution_of_quotientInvariant`,
`no_primitiveExecution_of_drift_divisor`, and
`ReturnGuard.Examples.cycle_no_primitive_integral_terminal_execution` in
[`ReturnGuardQuotient.lean`](MatrixMortality/ReturnGuardQuotient.lean) and
[`ReturnGuardQuotientExamples.lean`](MatrixMortality/ReturnGuardQuotientExamples.lean).

**Use:** search exact-order finite quotients for a closed safe invariant. A successful invariant
is a proof object with a finite transition table; failure identifies whether the escape is
terminal reachability or actual cyclotomic swallowing.

**Next:** separate the special rank-one quotients arising from parameter divisors from genuinely
projective exact-order certificates, and test whether either family is complete.

### R32-S13: Canonical decoded-integral lift

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For a rational residual `w`, let

```text
pair(w)=(num(w),den(w))
```

be its canonical reduced integer pair. Suppose the guarded coefficients have a common integral
presentation

```text
α=A/L,        ρ−α=D/L,        L≠0.
```

On a legal decoded branch of wait `a`, direct denominator clearing gives

```text
S_a(w)=N / (p^(sa)T),
N=(A−Lpᵃ)num(w)+D den(w),
T=(A−L)num(w)+D den(w).
```

The target is a p-adic unit. Its canonical denominator is therefore prime to `p`. When raw
fraction reduction writes

```text
N=c·num(S_a(w)),
p^(sa)T=c·den(S_a(w)),
```

Euclid's lemma forces `p^(sa)∣c`. Removing that forced power yields exactly the integer
recurrence `PrimitiveIntegralStep`; both source and target pairs are primitive by rational
normalization. This construction is canonical and transports every exact decoded execution
step for step without changing its length.

Consequently, a closed exact-order quotient invariant containing the canonical reset pair and
excluding both cancellation and the canonical terminal pair proves decoded unreachability and
hence physical immortality. The drift-divisor subfamily needs no coprimality assumption on the
chosen coefficients: the raw terminal pair and its canonical reduction represent the same
finite projective point whenever `A−L` survives the quotient.

**Scope:** the lift is one-way because that is the soundness direction needed by finite
no-certificates. It does not say that every abstract `PrimitiveIntegralStep` is a legal decoded
step, nor that the finite quotient family is complete.

**Artifact:** `ReturnGuard.rationalPair`,
`rat_denominator_not_dvd_of_isUnit`,
`decodedStep_primitiveIntegralStep`,
`decodedExecution_primitiveIntegral`,
`not_physical_isMortal_of_quotientInvariant`, and
`not_physical_isMortal_of_drift_divisor` in
[`ReturnGuardIntegralLift.lean`](MatrixMortality/ReturnGuardIntegralLift.lean);
`ReturnGuard.Examples.cycle_not_physical_isMortal_by_quotient` in
[`ReturnGuardQuotientExamples.lean`](MatrixMortality/ReturnGuardQuotientExamples.lean).

**Use:** every quotient invariant may now be read literally as a finite certificate about the
physical matrix pair. Search and classification can operate on finite projective automata
without reopening rational-normalization soundness.

**Next:** characterize which guarded parameters possess a drift-divisor certificate; then seek
generic primitive quotients for the complement and determine whether repeated cancellation
forces an effectively recognizable arithmetic history.

### R32-S14: Drift-divisor certificate classification

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** active

Fix a primitive divisor `ℓ` of `pᵉ−1` and assume `ℓ∣D`. The residual transfer modulo `ℓ` has
only its first column. Define the scaled center orbit

```text
O={L pʳ : 0≤r<e}⊆𝔽ℓ.
```

Then the following are equivalent:

1. some quotient invariant contains the reset and excludes both annihilation and the terminal
   ray;
2. the nonzero affine survivor shell is such an invariant;
3. `A∉O`;
4. when `A` and `L` survive, `A/L∉⟨p⟩⊆𝔽ℓ×`;
5. the executable Boolean classifier `driftDivisorCertifies` returns true.

The necessity is stronger than the earlier construction. If `A=Lpʳ`, closure from the reset
under residue `r` reaches either annihilation, when the first column vanishes, or the terminal
zero ray. Hence no alternative smaller invariant can repair a failed orbit test.

The primitive-divisor hypothesis gives multiplicative order exactly `e`, with `e∣ℓ−1`. If
`L≠0` modulo `ℓ`, the orbit has exactly `e` elements. Precisely `ℓ−e` center residues therefore
admit drift-divisor certificates. This quantifies the stratum: a large factor of small order
certifies most center classes, while a primitive-root factor (`e=ℓ−1`) certifies only the zero
class.

**Scope:** this classifies every safe invariant for quotients which divide `D`; it says nothing
about primitive quotients with nonzero drift, combinations of several quotient factors, or
completeness of the whole finite-quotient method. Failure of the Boolean test means that this
one drift-divisor quotient cannot certify immortality, not that the physical pair is mortal.

**Artifact:** `IsPrimitivePrimeDivisor.unit_orderOf_eq_exponent`,
`IsPrimitivePrimeDivisor.exponent_dvd_prime_sub_one`,
`ReturnGuard.affineSurvivors_quotientInvariant_iff_centerPowerOrbit_avoids`,
`hasQuotientCertificate_iff_centerPowerOrbit_avoids`,
`mem_centerPowerOrbit_iff_centerRatio_mem_zpowers`,
`card_centerPowerOrbit`, `card_certifyingCenters`,
`hasQuotientCertificate_iff_driftDivisorCertifies`, and
`not_physical_isMortal_of_driftDivisorCertifies` in
[`PrimitiveDivisor.lean`](MatrixMortality/PrimitiveDivisor.lean) and
[`ReturnGuardDriftCertificate.lean`](MatrixMortality/ReturnGuardDriftCertificate.lean).

**Use:** factor the nonzero drift numerator in a fixed integral presentation, test each primitive
factor once, and discard the entire parameter set as immortal as soon as one factor accepts.
Search effort on failed factors is now provably wasted; the next quotient must have nonzero
drift.

**Next:** study generic exact-order quotients with nonzero drift. By
[`R32-S15`](#r32-s15-finite-quotient-completeness), ordinary synchronized products cannot
strengthen a failed factor; any further local-global method must retain information across
primitive cancellation.

### R32-S15: Finite-quotient completeness

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** active

For integral residual parameters `(A,D,L)`, the zero-wait quotient transfer is

```text
⎡ A−L  D ⎤
⎣ A−L  D ⎦.
```

Its projective kernel is the terminal residual `τ=−D/(A−L)`. The canonical primitive integer
pair of `τ` is therefore sent to the absorbing cancellation state by residue zero in every
prime quotient. It follows that any transition-closed set containing the terminal already
contains cancellation.

Consequently the following are equivalent for every exact-order quotient:

1. a safe invariant contains reset and excludes cancellation and terminality;
2. a cancellation-free invariant contains reset;
3. cancellation is unreachable from reset in the finite quotient automaton.

The target-absence premise in the earlier certificate interface was redundant. A
cancellation-free invariant alone is a physical immortality certificate through the canonical
decoded-integral lift.

This also closes the obvious multi-prime composition. A synchronized two-factor invariant must
exclude cancellation in each coordinate. Projecting it onto either coordinate yields a
single-factor cancellation-free invariant, because every raw wait remains available after
projection. Hence a synchronized product cannot certify any instance missed by either
component; it is strictly no stronger than its projections.

**Scope:** this obstruction applies to products which track ordinary prime projective states
and reject any swallowed factor. It does not exclude an enriched local state which records the
factor's cancellation exponent and resumes after primitive renormalization, nor a composite
ring model retaining such valuation data.

**Artifact:** `ReturnGuard.quotientTransition_zero_terminal_eq_cancelled`,
`terminal_mem_forces_cancelled`,
`hasQuotientCertificate_iff_hasCancellationFreeInvariant`,
`hasCancellationFreeInvariant_iff_cancelled_unreachable`,
`hasQuotientCertificate_iff_cancelled_unreachable`,
`not_physical_isMortal_of_cancellationFreeQuotient`,
`not_physical_isMortal_of_cancelled_unreachable`,
`hasSynchronizedCancellationFreeInvariant_imp_components`, and
`hasSynchronizedCancellationFreeInvariant_imp_quotientCertificates` in
[`ReturnGuardQuotientCompleteness.lean`](MatrixMortality/ReturnGuardQuotientCompleteness.lean).

**Use:** reduce every ordinary finite-quotient search to one graph question: can any residue
word annihilate the reset ray? Do not build products of cancellation-rejecting automata.

**Next:** enrich the quotient state across swallowed factors. Track the exact valuation removed
by primitive reduction and test whether bounded cancellation memory yields a finite nucleus or
whether unbounded cancellation carries the missing computational stack.

### R32-S26: Evaluation-frame gauge closure

**Kind:** structure theorem and closure
**Evidence:** formalized
**Disposition:** graduated

For a normalized mass/reset jet `j` and payload `H`, put

```text
F(j,H) = [j₀  1]
         [j₁  H],

κ(j,H) = det F(j,H) = Hj₀−j₁.
```

If the integrating factor changes to `q′` and

```text
j′ = j + (1,H)/q′,
```

then the formerly independent Cramer-frame transition is exactly

```text
T(q′,H,H′,j) = F(j,H)⁻¹ F(j′,H′).
```

Its products telescope. The moving matrix cocycle is therefore a coordinate coboundary, not
an additional dynamical state. The determinant `κ` is only the denominator for recovering two
fixed parameter coordinates from their evaluation values.

Fix an anchor `α` and write `A(j)=j₁+αj₀`. The same determinant has the intrinsic form

```text
κ(j,H) = j₀(H+α)−A(j).
```

If `j₀` is a p-adic unit and `A(j)` has anchor depth `d`, then

```text
vₚ(κ)>d  ⟹  vₚ(H+α)=d.
```

At a unit terminal payload and a positive-depth anchor, `κ` is a unit. Thus arbitrarily deep
Cramer denominators occur only on the reset-return shell; they are not an independent carry
reservoir.

**Scope:** the frame identities are exact over `ℚ`; the shell theorems require the displayed
nonzero and p-adic unit hypotheses. They do not bound the number or geometry of reset returns.

**Artifact:** `ReturnGuard.evaluationFrameTransition_eq_coboundary`,
`evaluationFrameTransition_det`, `deep_frameDefect_forces_stateDepth_eq_anchorDepth`, and
`terminal_frameDefect_isUnit` in
[`ReturnGuardFrame.lean`](MatrixMortality/ReturnGuardFrame.lean).

**Use:** reason in fixed residual coordinates. Do not retain Cramer-frame digits, parameter
jets, or denominator expansions as independent state.

### R32-S27: Rational-gap macro pumping

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

Two rational residuals following the same legal wait `a` satisfy the exact similarity law

```text
vₚ(Sₐ(x)−Sₐ(y)) = vₚ(x−y)−sa.
```

For a wait word `w`, the loss is `s·sum(w)`. A perturbation deeper than that weight follows the
same branch word. Hence a return of depth `N` to one rational checkpoint pumps every bounded
number of repetitions of the same macro, losing exactly `s·sum(w)` depth per repetition.

Archimedean height prevents this from continuing indefinitely without equality. For distinct
p-adic unit rationals `x,y`,

```text
p^vₚ(x−y) ≤ 2 H(x)H(y),
```

where `H` is primitive projective height. One decoded step multiplies height by at most

```text
C = |A|+|D|+|L|.
```

Consequently, if a fixed wait macro `w` can be repeated `r>0` times from checkpoint `1`, then
either its first return is already exact or

```text
p^((r−1)s·sum(w)) ≤ 2 C^length(w).
```

A numerical violation forces an exact cycle after the first macro.

**Scope:** the pumping law works at any rational checkpoint. The final gap bound is stated at
checkpoint `1`, under one integral presentation of the guard parameters and legality of all
repetitions. It excludes storage by increasingly deep returns of one fixed macro; it does not
bound a nonperiodic schedule or a moving checkpoint.

**Artifact:** `ReturnGuard.residualRun_sub_hasValue`,
`followsResidualSchedule_of_deep_sub`, `primePower_le_rationalPairHeight`,
`residualMacroOrbit_follows_and_separates`, `repeatedMacro_exact_or_power_le`, and
`repeatedMacro_exact_of_power_gt` in
[`ReturnGuardGap.lean`](MatrixMortality/ReturnGuardGap.lean); independent synthesis in
[`m32-reset-gap-pumping-2026-07-30.md`](audits/m32-reset-gap-pumping-2026-07-30.md).

**Use:** any proposed universal orbit must move its checkpoint, change its macro, or use a
genuinely nonperiodic wait schedule. Any decision proof may instead show that sufficiently
deep returns contain a repeated macro and invoke the gap theorem.

**Next:** derive a combinatorial recurrence theorem for the canonical wait word strong enough
to force a powered factor at return depths exceeding the explicit height bound, or construct a
rational canonical orbit whose deep returns remain power-free.

### R32-S28: Terminal endpoint and complementary content

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

For an integral parameter presentation `α=A/L`, `ρ−α=D/L`, the fixed coordinate

```text
x = L(z−1) = A−L+D/w
```

sends reset to `A+D−L` and terminality to zero. A wait `a` acts by the homogeneous transfer

```text
Mₐ =
  [ A−L + Dp^(sa)   −(A−L)L(pᵃ−1) ]
  [ 1                −L(pᵃ−1)       ],
```

whose determinant is `−DLp^(sa)(pᵃ−1)`. This transfer is conjugate to the existing integral
residual transfer; the coordinate is a gauge, not another state.

If primitive normalization removes signed content `h` and

```text
h k = DL(pᵃ−1),
```

then the explicit adjugate reconstructs the source ray with scalar `−k`. For a complete
terminal word, if the forward and reverse contents partition every branch determinant, the
first-row coefficient of the product is exactly

```text
(−1)^N ∏ kᵢ.
```

Coefficient specializations yield finite necessary conditions. Most sharply, a prime dividing
`A−L` but neither `D` nor `p` makes the first coordinate nonzero after every word and therefore
certifies immortality. This excludes the former collision-ladder candidate modulo five and
the period-three survivor modulo 31 without orbit enumeration. Exact two-step terminal
examples with waits `[3,1]` and `[2,3]` prove that the aligned residue is nonempty and that
terminal waits need not be monotone.

**Scope:** the endpoint theorems retain exact word products and complementary contents. The
coefficient-prime theorem is sufficient, not complete; passing every coefficient boundary
does not imply mortality.

**Artifact:** `ReturnGuard.terminalCoordinate_residualStep`,
`endpointTransfer_mul_endpointGauge`, `endpointProduct_det`,
`endpointProduct_first_eq_complementProduct`,
`endpointAdjugate_mulVec_of_complementaryContent`, and
`not_endpointTerminalWord_of_prime_dvd_centerDifference` in
[`ReturnGuardEndpoint.lean`](MatrixMortality/ReturnGuardEndpoint.lean); the exact examples and
compact exclusions are in
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean). Independent synthesis
is recorded in
[`m32-endpoint-content-2026-07-30.md`](audits/m32-endpoint-content-2026-07-30.md).

**Use:** run coefficient-boundary tests before any orbit-specific analysis. Carry primitive
normalization as the pair `(h,k)` rather than as an auxiliary tangent state.

**Next:** turn the scale and drift boundary product identities into complete executable
subgroup tests, then combine all three coefficient boundaries with denominator growth.

### R32-S29: Adelic content and repeated-factor budget

**Kind:** structure theorem and obstruction
**Evidence:** formalized core; audited corollaries
**Disposition:** active

If one integral step reduces as `(M,N)=h(m′,n′)`, primitive height satisfies

```text
|h|H(m′,n′) ≤ C H(m,n),
p^((s−1)a)|h| ≤ C H(m,n),
C=|A|+|D|+|L|.
```

Thus cancellation and wait depth consume one Archimedean resource. The complete portion of
`pᵃ−1` coprime to `h`, including prime-power multiplicity, divides `m′−n′`; the old primewise
reset-or-cancel theorem was only its radical shadow.

For two primitive trajectories using the same wait, with removed contents `g,h`, the exact
exterior law is

```text
p^(sa) g h (v′∧u′) = DL(1−pᵃ)(v∧u).
```

Every local factor therefore goes to left cancellation, right cancellation, or increased
projective coincidence. There is no fourth destination. Separately, exact branch similarity
and rational separation apply at arbitrary checkpoints: a legal block shared by two orbit
states either begins at the same rational point or its p-adic expansion weight fits inside the
product of their projective heights.

**Scope:** these are one-step and repeated-factor budgets. They do not force a repeated factor
to occur in an arbitrary wait word and do not bound a schedule whose reduced denominators grow
without bound.

In the endpoint-adapted norm

```text
Ψ(r,t)=max(|D||t|,|r−(A−L)t|),       Γ=|A|+|D|+|L|,
```

the same one-step calculus gives `|h|Ψ⁺≤ΓΨ` and `pᵃ|D||h|≤ΓΨ` at depth two. Iteration from
reset yields

```text
(∏_{n<N}|hₙ|)Ψ_N ≤ |D|Γᴺ,
Q_N∏_{n<N}|hₙ| ≤ |L|Γᴺ,
p^aⁿ∏_{j≤n}|hⱼ| ≤ Γⁿ⁺¹.
```

Consequently distinct activated fresh primes occur only `O(N/log N)` times before return `N`;
on an aperiodic orbit every activated packet `d_i` satisfies `d_i=o(Ψ_{n_i})`, and regaining its
pre-activation height takes at least `⌈log_Γ d_i⌉` returns. Two consecutive steps which swallow
their entire source numerators also have a coefficient-effective second-wait bound. These are
audited corollaries, not a second formal recurrence API. They still permit a sparse microscopic
doubly order-broken genealogy.

For reset defect `Δ=r−(A+D−L)t`, one also has `pᵃ−1∣hΔ⁺`. A reset-avoiding prefix therefore
has a coefficient-effective quadratic bound on total wait mass, and a first-hit terminal word
has an exponential bound on its complete forward-content product and terminal
scalar/coefficient gcd. These remain bounds in the unknown length. `R32-O20` proves that the
unreactivated reverse product cannot be bounded from the projective endpoints: a fixed lawful
cycle hides an arbitrary 13-power on its transverse eigenline.

**Artifact:** `ReturnGuard.integralStep_content_mul_height_le`,
`integralStep_wait_content_le`, `cyclotomicComplement_dvd_targetDifference`, and
`primitiveSteps_projectivePairCross` in
[`ReturnGuardAdelic.lean`](MatrixMortality/ReturnGuardAdelic.lean);
`sharedSchedule_exact_or_power_le_pairHeights` and
`sharedSchedule_exact_or_power_le_heightEnvelope` in
[`ReturnGuardPumping.lean`](MatrixMortality/ReturnGuardPumping.lean). Independent synthesis is
recorded in [`m32-endpoint-content-2026-07-30.md`](audits/m32-endpoint-content-2026-07-30.md) and
[`m32-sparse-genealogy-budget-2026-08-10.md`](audits/m32-sparse-genealogy-budget-2026-08-10.md).

**Use:** charge every swallowed factor immediately and apply pumping to repeated factors
wherever they occur, not only to powers from reset.

**Next:** prove a reset-anchored recurrence-or-escape certificate for the sparse microscopic
two-sided-order-break residue, or construct an exact orbit which realizes that residue.

### R32-S30: Fixed-cusp and record-ascent calculus

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

For a primitive endpoint reduction, let `t` be the unreduced endpoint quotient and let `h` be
the removed signed content. The normalization is exact:

```text
t = hβ′,
|h| = gcd(|Dr|, |t|).
```

If `k` is the complementary reverse content, the reset defect factors as

```text
L(r′−(A+D−L)β′) = k(Lβ + Sₐt),
Sₐ = 1 + pᵃ + ⋯ + p^((s−1)a).
```

At a terminal target this removes the wait entirely: `k ∣ L(A+D−L)`. This is a constraint on
content, not on the last wait. Indeed every positive wait has an explicit integral terminal
predecessor, so backward enumeration by wait cannot terminate.

The canonical complete quotient

```text
Zᵢ = −DL Rᵢ₋₁/Rᵢ
```

obeys the cross-multiplied generalized continued-fraction law

```text
((pᵃ−1)Zᵢ − A + Lpᵃ)Zᵢ₊₁ = Dp^(sa)(Zᵢ₊₁+L).
```

The distinguished fixed cusp is `Z=−L`, and

```text
Zᵢ₊₁+L = L(A−L)βᵢ₊₁/Rᵢ₊₁.
```

Thus the cusp is forbidden whenever `L(A−L)βᵢ₊₁≠0`. Under the guard's unit hypotheses, the
wait itself is the approximation depth to one fixed rational ray:

```text
vₚ(A Rᵢ − DL Rᵢ₋₁) = aᵢ.
```

There is also a primitive coordinate carried through consecutive reductions without choosing a
reverse content. Put `q=p^a`, `Q=p^b`, `sᵢ=hᵢtᵢ₊₁`, and `Xᵢ=(tᵢ,sᵢ)ᵀ`. Existing
prequotient coprimality gives `gcd(Xᵢ)=1`, while Lean now proves at every depth `s`

```text
Q^s hᵢ Xᵢ₊₁ =
  [[0,Q^s],[DL(q−1),A+Dq^s−LQ]] Xᵢ.
```

Thus the global projective transfer is a generalized continuant with no complementary-content
or tangent state. The coordinate is attached to an outgoing edge and its second entry has the
sign of `hᵢ`; a local floor selector and a common positive cone are not yet proved.

At the critical depth `s=2`, two consecutive primitive steps with nondecreasing waits `a≤b`
satisfy the exact local mountain budget

```text
p^(a+b)|hh′| ≤ C₂ H(r,β),
C₂ = |D| + (1+|L|)(|A|+|L|).
```

The intermediate height has vanished. Algebraically, the critical decoder factors into one
fixed order-three core and a wait-dependent shear:

```text
C(p⁻ᵃ) = J · [[1,0],[-p⁻ᵃ,1]],
J³ = −I.
```

**Scope:** the carried coordinate removes a state-transport obstruction but supplies no global
height descent. The record estimate remains an absolute two-step budget at the start of a local
ascent and does not compare the charged power with inherited height. The reported full “fresh
cyclotomic core” lower bound was not promoted: two versions use incompatible loss exponents,
and neither supplies the missing valuation bookkeeping.

**Artifact:** `PrimitiveEndpointReduction.content_natAbs_eq_gcd_driftSource_prequotient`,
`PrimitiveEndpointReduction.resetDefect_eq_complement_mul`,
`PrimitiveEndpointReduction.complement_dvd_terminalBoundary`, `terminalPredecessorPair_step`,
`cumulativeCompleteQuotient_recurrence`, `cumulativeCompleteQuotient_sub_forbiddenCusp`,
`cumulativeWaitForm_hasValue`, `PrimitiveEndpointReduction.twoStep_prequotient_transport`,
`PrimitiveEndpointReduction.twoStep_contentBudget`,
`criticalDecoder_factor`, and `criticalDecoderCore_cube` in
[`ReturnGuardContinued.lean`](MatrixMortality/ReturnGuardContinued.lean). Independent audit:
[`m32-fixed-cusp-record-ascent-2026-08-01.md`](audits/m32-fixed-cusp-record-ascent-2026-08-01.md)
and [`m32-prequotient-adelic-2026-08-06.md`](audits/m32-prequotient-adelic-2026-08-06.md).

**Use:** carry terminal corridors in the primitive prequotient coordinate; use the fixed-cusp
quotient for wait selection and charge every nondecreasing pair before importing a
primitive-divisor estimate.

**Next:** prove a coefficient-effective positive or adelic block theorem for the displayed
generalized continuant. It must control the edge-coordinate sign and removed scalar and compare
each record charge with inherited height; another absolute estimate cannot close the orbit.

### R32-S31: Smith decoder and maximal-cancellation throat

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

At critical depth two, complementary endpoint contents admit the signed split

```text
h=ηu,    k=θv,    ηθ=DL,    uv=q−1,
u,v>0,      gcd(u,θ)=1.
```

The corresponding endpoint decoder

```text
C(q,u,v) = [[v,q²],[1,(q+1)u]]
```

has determinant `−1` and the exact continuant cut

```text
C(q,u,v) = [[1,v],[0,1]] [[0,1],[1,(q+1)u]].
```

Thus the moving Smith factors are a positive shear and one Gauss digit, not an opaque matrix
norm. On positive coprime input, Lean verifies that the decoded pair remains coprime and its
primitive max-height strictly increases. The inverse proves that every common reduction factor in the decoded
pair divides the fixed coefficient `Lη`. More generally, for every `core∣q−1`, the part

```text
Ω=core/gcd(core,|h|)
```

divides `|k|`, is coprime to the reduced target denominator, and satisfies
`core≤|h|Ω`. This folds the proposed primitive-core allocation into one exact gcd theorem
with multiplicity.

For `q≥3`, the weighted norm `||(x,y)||=|x|+4|y|` obeys

```text
4||C(q,u,v)x|| ≤ 3q²||x||
```

whenever `v≥2`. Hence the sole noncontracting local throat is `v=1`, where `u=q−1` and

```text
m=Lt+q²ηt′,
r=(q−1)m,
ηr′=Dm+(A−L)ηt′.
```

The submitted variable-wait cocycle required correction. In the frame
`F_q(m,n)=(n,q²m−n)`, one step maps `F_q` to the same lagged frame `F_q`; changing the target
to `F_Q` requires an explicit rational gauge `J(q,Q)`. Lean checks the lagged identity, the
gauge, and their composition. One fixed basis now sharpens the gauge exactly:

```text
[[1,0],[1,1]] J(q,Q) [[1,0],[−1,1]] = diag(1,Q²/q²).
```

The moving frame defect is therefore a pure base-prime dilation, not an irreducible shear. The
ungauged concatenating identity and all global tropical estimates derived from it are false in
general and were rejected.

**Scope:** contraction is local after natural `q²` rescaling. Diagonalizing the gauge does not
diagonalize the intervening Smith cocycles or bound their product. The formerly open infinite
chain of `v=1` steps is excluded by
[`R32-O07`](#r32-o07-parity-immortality-and-maximal-isolation).

**Artifact:** `exists_smithRubanSplit`, `smithRubanDecoder_det`,
`smithRubanDecoder_continuant_cut`,
`smithRubanQuotient_isCoprime`, `smithRubanQuotient_height_gain_of_pos`,
`smithRubanDecoder_weight_contraction`,
`PrimitiveEndpointReduction.coreQuotient_dvd_complement`,
`PrimitiveEndpointReduction.smithRuban_resetDefect`,
`PrimitiveEndpointReduction.maximalCancellation`, `integralStep_laggedReturnCocycle`, and
`returnWaitFrameChange_diagonal`, `gaugedReturnCocycle_mulVec` in
[`ReturnGuardSmith.lean`](MatrixMortality/ReturnGuardSmith.lean). Independent reconstruction:
[`m32-smith-ruban-2026-08-02.md`](audits/m32-smith-ruban-2026-08-02.md) and
[`m32-prequotient-adelic-2026-08-06.md`](audits/m32-prequotient-adelic-2026-08-06.md).

**Use:** split every large cyclotomic factor into a contracting branch or the exact maximal
throat before applying height or primitive-divisor arguments. Never concatenate lagged frames
without the intervening gauge.

**Next:** orient the carried prequotient coordinate through the signed Smith charts as an inverse
positive macro, or calculate the full adelic factor of its exact generalized continuant. The
missing theorem must control cone entry, the moving chart diagonal, and primitive reduction;
positivity of an abstract two-decoder product is not enough.

### R32-O07: Parity immortality and maximal isolation

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The adjacent p-adic unit hypotheses on `α` and `α−1` force the guard prime `p` to be odd. For
integer endpoint coefficients put

```text
R=A+D−L.
```

If `R` is odd, parity propagates through every primitive integral guard step at every depth:
an odd source endpoint numerator forces the scaled target denominator and numerator odd, hence
the primitive target numerator itself is odd. The reset numerator is `R`; the canonical
physical target has endpoint numerator zero. Physical mortality is therefore impossible.

It remains to consider even `R` at critical depth two. A maximal Smith step has `v=1` and,
after substituting its quotient and cancelling `η`, satisfies

```text
r′ = θt + (Dq²+A−L)t′.
```

Here `t` and `θ` are odd, while the second coefficient is even. Thus `r′` is odd and the
maximal step cannot terminate. If a next primitive step exists, its forward content and Smith
coordinate `u` are odd; since `uv=q′−1` is even, the next `v` is even. Consecutive maximal
steps are impossible.

**Scope:** the odd-resultant theorem excludes physical mortality for an actual guard through
the checked decoded-to-primitive execution lift. The maximal-isolation theorems concern
consecutive primitive depth-two endpoint reductions with their Smith splits. They do not
globalize the local contraction on `v≥2` branches.

**Artifact:** `PadicValuation.odd_prime_of_adjacent_units`, `Parameters.prime_odd`,
`not_physical_isMortal_of_resetResultant_odd`,
`PrimitiveEndpointReduction.maximalCancellation_targetNumerator_odd`, and
`PrimitiveEndpointReduction.maximalCancellation_next_v_even` in
[`PadicValuation.lean`](MatrixMortality/PadicValuation.lean),
[`ReturnGuardDynamics.lean`](MatrixMortality/ReturnGuardDynamics.lean),
[`ReturnGuardCumulative.lean`](MatrixMortality/ReturnGuardCumulative.lean), and
[`ReturnGuardSmith.lean`](MatrixMortality/ReturnGuardSmith.lean). Independent audit:
[`m32-parity-maximal-isolation-2026-08-04.md`](audits/m32-parity-maximal-isolation-2026-08-04.md).

**Use:** discard residue characteristic two, the entire odd-resultant mortality stratum, and
every eventually maximal schedule. Any surviving undecidability construction or decision
argument must live in even `R` and traverse a `v≥2` branch after each maximal step.

### R32-O08: Recurrent boundary divisors stay reverse

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Consider consecutive primitive endpoint reductions with signed forward and reverse contents

```text
h k   = DL(pᵃ−1),
h′ k′ = DL(pᵇ−1),
R     = A+D−L.
```

For every signed divisor `d`, Lean proves

```text
d∣k,  d∣L(pᵇ−1),  gcd(d,LR)=1
  ⇒ gcd(d,h′)=1 ∧ d∣k′.
```

The result retains multiplicity and assumes neither that `d` is prime nor that the carry depth
is two. It reverses the proposed prime-handoff rule: a recurring boundary factor already on the
reverse side cannot switch to forward cancellation outside the fixed scale-reset support.

**Scope:** the theorem concerns consecutive reductions for which the divisor occurs in the
next boundary. A primitive divisor of a maximal wait is absent from every intervening smaller
wait, so an intervening invertible projective bridge can still change the incidence at its next
occurrence. The theorem supplies no global allocation law across such a bridge.

**Artifact:** `PrimitiveEndpointReduction.recurrentBoundaryDivisor_persists` in
[`ReturnGuardContinued.lean`](MatrixMortality/ReturnGuardContinued.lean). Independent audit:
[`m32-jacobi-handoff-2026-08-05.md`](audits/m32-jacobi-handoff-2026-08-05.md).

**Use:** do not model repeated primitive factors as alternating tokens. At an immediate repeated
boundary they persist on the reverse side; across a smaller-wait bridge, use the existing
exact-order projective automaton and prove the required incidence or valuation statement.

### R32-O09: Universal-boundary reset ball

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

At depth two, choose an integral coefficient presentation

```text
center=A/L,    drift=D/L,    R=A+D−L.
```

For any prime `ℓ`, put

```text
λL=vℓ(L),   λR=vℓ(R),   λD=vℓ(D),
e=vℓ(p−1), ε=vℓ(2).
```

If `R≠0` and

```text
λR < λL+e,
2λR < λD+e+min(λL,λR+ε),
```

then the open `ℓ`-adic ball of depth `λR` around reset is invariant under every positive
decoded branch. The exact mechanism is

```text
(F_q(z)−R)(z−L(q−1)) = D(q−1)((q+1)z+L),    q=pᵃ.
```

Reset belongs to the ball and terminal `0` does not, so the physical guard is immortal. If the
last blade vanishes, the branch returns exactly to reset; this case must be separated before
using finite valuations.

Every prime `ℓ∣p−1` of a mortal guard consequently divides `R`; hence `rad(p−1)∣R`. The full
valuation wall is stronger than this squarefree sieve and is unchanged by common rescaling of
`A,D,L`.

**Scope:** the invariant begins at reset. A tail whose waits are all multiples of `m` inherits
the analogous `pᵐ−1` wall only if its entry endpoint is already in the corresponding ball. The
theorem neither proves that entry nor amortizes a later wait outside `mℕ`.

**Artifact:** `ReturnGuard.not_physical_isMortal_of_resetBall` and
`ReturnGuard.universalBoundary_dvd_resetResultant_of_physical_isMortal` in
[`ReturnGuardBoundary.lean`](MatrixMortality/ReturnGuardBoundary.lean). Independent audit:
[`m32-universal-boundary-2026-08-05.md`](audits/m32-universal-boundary-2026-08-05.md).

**Use:** reject depth-two coefficient laws below the wall before any orbit analysis. Do not infer
trapping from a common-period tail alone; [`R32-O10`](#r32-o10-ready-order-breaking-bridge-ejection)
also excludes a uniform charge on its first order-breaking bridge.

### R32-O10: Ready order-breaking bridge ejection

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

At depth two, the coefficient law

```text
p=3,   A=R=249398,   D=L=1
```

has the ready prefix

```text
249399 ─4→ 4863261/19 ─1→ 67384284465/270178,
```

and the final target is itself ready at wait one. The auxiliary prime `5` is a primitive divisor
of `3⁴−1`. In endpoint coordinates, wait four moves from reset into its strict `5`-adic
ball, while the order-breaking wait one returns to the boundary:

```text
v₅(R)=0,   v₅(z₁−R)=1,   v₅(z₂−R)=0.
```

The bridge's raw endpoint pair has gcd `18`, coprime to `5`; no auxiliary content is swallowed.
Its primitive denominator grows from `19` to `270178`. The reset resultant is even and the law
passes every universal-boundary wall.

**Scope:** this is a continuing legal prefix, not an infinite orbit. It refutes every uniform
first-bridge invariant-ball, auxiliary-content, repetition, or denominator-descent charge, even
when the target remains ready. It does not refute a global amortization theorem over complete
surviving executions.

**Artifact:** `ReturnGuard.Examples.orderBreaker_shatters_resetBall` in
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean). Independent audit:
[`m32-order-breaking-bridge-2026-08-05.md`](audits/m32-order-breaking-bridge-2026-08-05.md).

**Use:** retire the first order-breaking bridge as an independent local consumer. Any exact-order
proof must amortize an unbounded bridge sequence in one global invariant and is therefore part of
the existing nonmaximal-amortization problem.

### R32-O11: Terminal-only pole contraction is a decision oracle

**Kind:** obstruction
**Evidence:** audited
**Disposition:** graduated

For a legal terminal execution, write `T=2∑aᵢ`, let `m` count its nonmaximal Smith steps, and
let `π` be the pole of the complete endpoint product. The proposed fixed-frame contraction was

```text
H(π) ≤ C p^T ρ^m,    C>0, 0<ρ<1,
```

with constants depending on the fixed coefficient law. The guard is deterministic, so a fixed
law has at most one first-hit terminal execution. Pointwise existence is therefore automatic:
take `ρ=1/2`; in the immortal case any positive `C` works, while after a terminal word is known
one may take

```text
C=max(1,H(π)2^m/p^T).
```

Calling each resulting rational number computable does not make the dependence on the
coefficients effective. The missing datum is a single total algorithm which receives
`(p,A,D,L)` and returns valid rational `C,ρ` without first solving terminal reachability.

Such an algorithm is already a guard decider. The audited pole lower bound and checked
maximal-step isolation give

```text
p^T/(1+|R|) ≤ H(π) ≤ C p^T ρ^m,    N≤2m.
```

Successive powers of rational `ρ` then compute a terminal-length bound. Conversely, a guard
decider computes valid constants: output arbitrary constants in the immortal case, or simulate
to the first terminal hit and use the displayed formula. Thus uniform terminal-only pole
contraction is equivalent in effective content to the desired guard decision, not a smaller
arithmetic lemma.

The report's fixed-frame algebra is correct but does not escape this quantifier wall. For a
terminal product the checked endpoint transport already forces

```text
M=[[εK,−εRK],[c,S−Rc]],    π=R−S/c.
```

Orbit-adapted triangularization rewrites `−c/S` as a mixed-radix extension sum. The Smith
reconstruction identity

```text
[[R,−(A−L)v],[1,−v]] C(q,u,v)
  = [[Dv,A−L+Dq²],[0,1]]
```

identifies `c` as the channel through which inherited height can repay local contraction, but
supplies no bound on that channel. The prefix congruence gives exact approximation depth and
only the natural height corridor

```text
p^T/(1+|R|) ≤ H(π) ≤ C_E^N p^T.
```

This excludes closure by bare rational approximation at the natural exponent. It does not
exclude a semigroup-specific estimate.

**Scope:** this record rejects the pointwise terminal formulation as frontier movement. It does
not refute an explicit coefficient formula proved from the recurrence, a uniform inequality on
a nonterminal class broad enough to have independent content, or a constructive infinite
orbit. The elementary dual, triangular, and reconstruction identities were culled rather than
installed as an unconsumed Lean API.

**Artifact:** independent reconstruction in
[`m32-fixed-frame-pole-2026-08-06.md`](audits/m32-fixed-frame-pole-2026-08-06.md).

**Use:** require the next decision attack to output an explicit coefficient algorithm or
terminal-length function and prove its estimate without invoking the terminal time. Do not
accept existential constants chosen after the unique execution is known.

### R32-O12: Periodic-shadow obstruction

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The fixed depth-two guard

```text
p=3,   A=17,   D=−5,   L=16,   reset=3/4
```

has ready wait one at reset and maps reset back to itself. Nevertheless, for every `B` it has a
legal corridor of length greater than `B` all of whose states lie off reset. The family is
indexed by an odd shadow depth `K≥3`:

```text
t(K,n)=4−9^(K+1)+10^n9^(K+1−n),
E(K,n)=(32t(K,n)−36t(K,n+1),t(K,n)).
```

Every internal edge is the actual wait-one guard step induced by the exact primitive endpoint
reduction

```text
E(K,n) --h=−4--> E(K,n+1).
```

Its carried pair `(t(K,n),−4t(K,n+1))` is primitive. The fixed Smith split is

```text
(u,η,θ,v)=(1,−4,20,2),
```

and the raw Smith decoder output is exactly four times the primitive pair

```text
(8t(K,n)−9t(K,n+1), 4(t(K,n)−t(K,n+1))).
```

Both primitive-pair heights rise strictly along arbitrarily long runs of consecutive edge
coordinates. The audit identifies the mechanism as a `3`-adic shadow of the fixed carried ray
`x=−4`: each wait-one step removes exactly two units from `v₃(x+4)`. Hence no bound depending
only on the coefficients can ensure a descending carried or Smith-height block inside every
legal corridor, even when every edge has `v=2` and the wait gauge is constant.

**Scope:** these are finite off-reset corridors. The reset orbit of this guard is fixed; the
theorem neither reaches terminal nor constructs an infinite unbounded-denominator orbit. It
does not refute an estimate anchored at reset, conditioned on first-hit terminality, or run in
reverse from the terminal boundary.

**Artifact:** `ReturnGuard.PrimitiveEndpointReduction.guardedStep_endpointState` in
[`ReturnGuardCumulative.lean`](MatrixMortality/ReturnGuardCumulative.lean) and
`ReturnGuard.Examples.periodicShadow_obstruction` in
[`ReturnGuardPeriodicShadow.lean`](MatrixMortality/ReturnGuardPeriodicShadow.lean). Independent
audit: [`m32-periodic-shadow-2026-08-06.md`](audits/m32-periodic-shadow-2026-08-06.md).

**Use:** retire coefficient-uniform descent quantified over all legal corridors. A surviving
decision proof must use reset or terminal history and retain the unbounded arithmetic depth of a
near-periodic shadow; the opposing construction must make one fixed reset orbit concatenate such
episodes rather than merely exhibit them off orbit.

### R32-O13: Renewal-graph collapse and reset pullback

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The proposed episode-local renewal dichotomy has no surviving arm. Its reset-anchored bounded-
depth arm could survive only by using full ancestry absent from a local renewal graph. For every
legal wait word `w`, the already-checked exact similarity gives

```text
vₚ(F_w(x)−F_w(y))=vₚ(x−y)−s∑w.
```

Every honest aligned renewal edge therefore has negative depth weight, and every finite aligned
cycle has strictly negative total weight. A misaligned ray switch caps sufficiently deep inputs
at the fixed separation of the transported and target rays; extra depth occurs only on one
threshold shell through leading-residue cancellation and is not an iterable macro weight.

The opposite implication also fails locally. In the fixed guard of
[`R32-O12`](#r32-o12-periodic-shadow-obstruction), for every bound there is a legal off-reset
wait-one edge with content `−4`, Smith coordinate `v=2`, primitive carried pair `X`, and

```text
v₃(X₂/X₁+4)=2
```

whose endpoint and carried heights both exceed the bound. Thus bounded shadow depth plus every
finite local label does not yield a finite endpoint box.

Reset history is retained exactly by the new cumulative pullback law. If

```text
M_uP₀=p^(s∑u)Pᶜ_u,
```

then for every integral reference ray `V`,

```text
Δ(P₀,adj(M_u)V)=p^(s∑u)Δ(Pᶜ_u,V).
```

When `Pᶜ_u=H_uP_u`, this is the primitive-content form with the additional factor `H_u`. A deep
shadow reached from reset is therefore one high-power divisibility condition on a moving
pulled-back ray, not a finite renewal-state label.

**Scope:** no compactness extraction has been proved. An infinite orbit may have unbounded
height while remaining at bounded depth from every fixed rational periodic ray, or may visit
infinitely many rays and threshold residues. Varying factors `p^a−1` prevent a fixed-support
`S`-unit conclusion from the pullback identity alone.

**Artifact:** `CumulativeEndpointExecution.pullback_projectivePairCross` in
[`ReturnGuardCumulative.lean`](MatrixMortality/ReturnGuardCumulative.lean),
`Examples.periodicShadow_shatters_localCompactness` in
[`ReturnGuardPeriodicShadow.lean`](MatrixMortality/ReturnGuardPeriodicShadow.lean), and
[`m32-renewal-collapse-2026-08-07.md`](audits/m32-renewal-collapse-2026-08-07.md).

**Use:** retire fixed positive-depth renewal cycles and episode-local finite-box arguments.
[`R32-O14`](#r32-o14-fixed-reset-geodesic-and-complete-endpoint-language) subsequently proves
that radial reset ancestry is already fixed. The surviving use of this record is therefore the
threshold-cancellation obstruction: a decision proof must bound the global angular determinant
or carry, while an opposing construction must vary waits or auxiliary allocation essentially
aperiodically. Repeating one finite shadow gadget cannot work.

### R32-O14: Fixed reset geodesic and complete endpoint language

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** graduated

For every positive wait word `w`, the endpoint terminal equation is complete:

```text
EndpointTerminalWord(w) ↔ inverseAddress(w,terminalResidual)=1.
```

The inverse branches recover a lawful decoded execution, and their disjoint positive branch
spheres make the terminal word unique. Thus the positive endpoint zero language is singleton-
or-empty, and physical guard mortality is exactly the existence of a nonempty word in that
language. Endpoint algebra creates no witnesses through a pole, an incorrect wait, or a
malformed intermediate state.

Modulo the distinguished prime, every nonempty positive endpoint product is

```text
A^(|w|−1) · [[A−L,(A−L)L],[1,L]].
```

In the normalized presentation, `A` is a p-unit, so this is one fixed nonzero rank-one flag.
If `D` and `L` are p-units, the determinant valuation is exactly the full schedule weight
`Ω=s∑w`. More strongly, every cumulative execution from the reset pair satisfies

```text
ker(M_w mod p^Ω) = (ℤ/p^Ωℤ) · (A+D−L,1).
```

The reset direction is therefore fixed at every depth. The moving determinant in
[`R32-O13`](#r32-o13-renewal-graph-collapse-and-reset-pullback) varies only through its angular
reference, not through a radial ancestral ray at `p`. A primitive positive-depth pullback also
retains its full `p^(Ω+δ)` factor: its transverse coordinate is a p-unit, so primitive
normalization removes no distinguished-prime power. This last consequence was audited from the
checked pullback identity and not installed as a duplicate API.

The lawful coefficients

```text
(p,s,A,D,L)=(3,2,122753,−17,39232)
```

have exactly one positive terminal word, `[1,1,1]`. Lean checks both the product and uniqueness,
and derives mortality of the associated rational rank-`(3,2)` pair. This refutes every universal
one- or two-return terminal bound.

**Scope:** neither endpoint uniqueness nor the fixed reset geodesic bounds terminal length. The
unresolved data are angular: factors of `p^a−1` split between forward and reverse contents and
can finance an unbounded mixed-radix carry across auxiliary places. No effective carry bound and
no aperiodic unbounded-denominator reset orbit has been obtained. Deciding this guard would still
leave generic PI₂ before full `M₃(2)`.

**Artifact:** `ReturnGuard.endpointProduct_mod_prime`,
`ReturnGuard.endpointProduct_det_hasValue`,
`ReturnGuard.CumulativeEndpointExecution.endpointKernel_eq_resetLine`,
`ReturnGuard.endpointTerminalWord_iff_inverseAddress_eq_one`,
`ReturnGuard.endpointTerminalWord_unique`, and
`ReturnGuard.physical_isMortal_iff_endpointTerminalWord` in
[`ReturnGuardEndpointCompleteness.lean`](MatrixMortality/ReturnGuardEndpointCompleteness.lean);
`ReturnGuard.Examples.threeReturn_endpointTerminalWord_iff` and
`ReturnGuard.Examples.threeReturn_physical_isMortal` in
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean). Independent audit:
[`m32-fixed-geodesic-endpoint-completeness-2026-08-07.md`](audits/m32-fixed-geodesic-endpoint-completeness-2026-08-07.md).

**Use:** retire malformed endpoint witnesses, moving radial reset ancestry, hidden positive-depth
primitive-normalization savings at `p`, and a universal two-return bound. Analyze the remaining
one-dimensional angular carry globally across its moving auxiliary prime support, or construct
an exact aperiodic reset-started orbit that uses it to sustain unbounded denominators.

### R32-O15: Fixed-support toric compiler obstruction

**Kind:** obstruction
**Evidence:** audited
**Disposition:** graduated

Write a ready state as

```text
R_a(t)=p^a+p^(sa)/t.
```

Suppose finitely many control charts store counters in a fixed set of auxiliary-prime powers,
their canonical tails are rational functions of those powers, their waits are affine in the
counter exponents, and every instruction translates the counter vector by a fixed amount on a
cofinal orthant. Zariski density of the paired prime-power grid and Laurent-support comparison
force both endpoint wait slopes of every instruction to vanish. If the charts are Laurent
monomials, the p-unit constant term in the exact tail transition then forbids every nonconstant
instruction; one affine monomial ray can meet its instruction equation at no more than five
counter values.

Arbitrary rational charts cannot restore iteration. Every fixed-wait tail matrix has one common
rank-one reduction modulo `p`. A nonempty control-cycle product has unit trace and positive
determinant valuation, hence a projective eigenvalue quotient of nonzero p-adic valuation. A
toric chart shift scales every variable by a p-unit and preserves the Gauss valuation, which
contradicts that quotient.

**Scope:** this excludes separated rational charts over fixed auxiliary-prime support with
affine wait dependence. It does not exclude an input-specific history with non-affine waits,
continually changing factors of `p^a−1`, or angular state not rationally determined by a fixed
torus.

**Artifact:** independent reconstruction in
[`m32-fixed-support-toric-obstruction-2026-08-08.md`](audits/m32-fixed-support-toric-obstruction-2026-08-08.md).
The existing single-chart formal obstruction remains
`ReturnGuard.Rail.no_infinite_primePower_affineWait_rail`; no parallel multivariate API was
retained.

**Use:** retire orthodox fixed-prime FRACTRAN and Minsky encodings in the guard. Any aperiodic
counter-orbit must use genuinely moving cyclotomic support and unbounded history rather than a
stationary prime-exponent register.

### R32-O16: Irreducible-cubic punctuation collapse

**Kind:** structure theorem and obstruction
**Evidence:** formalized core; audited strengthening
**Disposition:** graduated

Let `A ∈ GL₃(ℚ)` have irreducible cubic characteristic polynomial and put `Mₙ=VAⁿU`
for rank-two interfaces `U,V`. The cubic-field sandwich map `z ↦ Vm_zU` is injective. Thus no
return is zero, every singular return has rank one, every nonzero scalar observation has exact
recurrence order three, and `det Mₙ` has exact irreducible order three under `∧²A`.

Root-of-unity degeneracy occurs exactly for the pure cubic `χ_A=X³−N`, equivalently
`A³=NI`. Otherwise the singular waits form a finite effectively enumerable set, and distinct
waits give distinct projective returns. In the pure case Lean proves, for arbitrary words,

```text
M_(3q+r)=N^q M_r,
mortality of {Mₙ : n≥0} ↔ mortality of {M₀,M₁,M₂}.
```

Every irreducible-cubic return family has a computable common-left reflection form
`Mₙ=QJₙ`, where each `Jₙ` is traceless. Unit indices are projective involutions and singular
indices are square-zero rank-one maps. The non-pure residue is therefore exact reachability
between finitely many forced endpoint lines under an order-three recurrence of reflections.

This reflection form has a canonical trace model. If `K₀` is the trace-zero plane of the cubic
field and `Tₓ(u)=π(xu)` is projected multiplication, then, after interface conjugation,

```text
Mₙ=F T_(γθⁿ).
```

The twist `F∈GL₂(ℚ)` is arbitrary: every such tuple has a rank-two physical realization. The
singular conic is parametrized by inversion, `Tₓ` is singular exactly when `x⁻¹∈K₀`, and its
kernel is `⟨x⁻¹⟩`. Clifford normalization turns the remaining bridge equation into reachability
on that rational null conic under the adjoint twist of an arbitrary `Q` interleaved with the recurrence
reflections.

No algebraic finite-state collapse follows. The explicit non-pure family

```text
A=[[0,0,1],[1,0,1],[0,1,0]],
U=[[0,−2/3],[1,0],[0,1]],
V=[[0,0,31],[1,0,0]]
```

has `χ_A=X³−X−1`, a singular return `M₀`, and unit returns

```text
M₁=F=diag(31,1),    M₄=FR,
R=[[1,1/3],[1,1]].
```

Real ping-pong proves that `F,R` generate their free product. Hence `M₁,M₄` generate a free
binary submonoid with an injective rational-line orbit. This kills bounded bridge length or a
finite set of projective bridge states as consequences of cubic recurrence and involutivity
alone; it does not decide reachability between the actual singular endpoint lines.

The pure residue triple is still more rigid. Three determinant-polarization equations give the
normal form

```text
(P R, P, P Jμ),
R=[[1,1],[0,0]],   Jμ=[[0,μ],[1,0]],   μ∈ℚ× ∖ ℚ×³.
```

Zero singular residues give immortality and two singular residues reduce to four
order-at-most-two recurrence tests. In the unique one-singular stratum, Lean proves that both
exceptional scalars of the existing reverse-edge compiler are exactly `μ⁻¹`. Hence this entire
pure fork is already one GPI₂ instance, not an independent involutive-ratio problem.

**Scope:** Lean checks the pure-cubic arbitrary-word collapse and the exact genericity scalars of
the one-singular normal form. Field faithfulness, singular-time classification, canonical trace
and null-conic forms, arbitrary twist, and the free physical bridge are independently audited.
The free witness in this record did not use a singular endpoint. `R32-S42` subsequently closes
that placement seam and isolates arbitrary unselected waits as the surviving obstruction.
GPI₂ itself remains open.

**Artifact:** `CubicReturn.returnProduct_eq_smul_residues`,
`CubicReturn.pairGenerator_isMortal_iff_residue`, and
`CubicReturn.pureOneSingular_reverseEdgeScalars` in
[`CubicReturn.lean`](MatrixMortality/CubicReturn.lean), with the reconstructions in
[`m32-cubic-punctuation-collapse-2026-08-08.md`](audits/m32-cubic-punctuation-collapse-2026-08-08.md)
and
[`m32-cubic-reflection-generic-bridge-2026-08-09.md`](audits/m32-cubic-reflection-generic-bridge-2026-08-09.md).
The arbitrary-twist, null-conic, and free-bridge strengthening is reconstructed in
[`m32-cubic-null-conic-orbit-2026-08-10.md`](audits/m32-cubic-null-conic-orbit-2026-08-10.md).

**Use:** retire cubic singular timing as an unbounded store and merge the pure one-singular fork
into GPI₂. Do not seek a finite bridge-state collapse from recurrence order or involutivity.

**Next:** superseded by `R32-S42`: decide the endpoint-faithful all-waits recurrence, or compile
universality while making every unselected recurrence index harmless.

### R32-S32: Rank-two punctuation and graph removal

**Kind:** structure theorem and reduction
**Evidence:** audited
**Disposition:** graduated

For a rank-(2,2) pair, all four compressed `2 × 2` edges are nonzero. Split every constrained
path at its rank-one punctuation edges. The unit-only outer factors preserve nonzero rows and
columns, so the path vanishes exactly when one bridge between consecutive punctuation edges has
zero scalar incidence.

This fractures the complete edge-rank census. With no punctuation every path is a unit. With at
least two punctuation edges the remaining unit graph has at most two edges, so its bridge
languages are finite unions of unary loops and are decidable by order-at-most-two recurrences.
One rank-one cross-edge gives equality of two positive cyclic `PGL₂(ℚ)` orbits; an audited
effective algorithm handles the parabolic cases elementarily and the semisimple cases by
effective `S`-unit enumeration.

The unique hard stratum has one rank-one loop `qr` and three unit edges. Lean transports every
compatible square in this stratum exactly to the existing raw reverse compiler. The intrinsic
instance has controls `A` and `BU`, row `rU`, column `Bq`, and exceptional scalars

```text
α=rq,   β=1.
```

Thus the square is mortal exactly when `rq=0`, giving immediate loop nilpotence, or the one
intrinsic generic incidence instance has a zero word. Combining the checked reverse compiler
with the audited decidable strata yields

```text
Mort₃^(2,2) ≡ₘ GPI₂.
```

**Scope:** the one-loop transport, forced `β=1`, and complete path equivalence are formalized.
The forward reduction's cyclic-orbit branch imports effective unit equations and is audited,
with source [`EG13`](references/evertse-gyory-2013-effective-unit-equations.md). `R32-S35`
separately removes arbitrary nongeneric PI₂ as a decidability seam; neither result decides GPI₂.

**Artifact:** `RankTwoPunctuation.transport_eq_rawEdge` and
`RankTwoPunctuation.exists_pathProduct_eq_zero_iff_selfBridge_or_incidence` in
[`RankTwoPunctuation.lean`](MatrixMortality/RankTwoPunctuation.lean), with the full rank census
in [`m32-rank-two-punctuation-2026-08-08.md`](audits/m32-rank-two-punctuation-2026-08-08.md).

**Use:** replace every rank-(2,2) graph attack by generic PI₂. The graph supplies neither a
controller bit nor a distinct universality mechanism; the remaining seam is the projective
incidence problem itself.

### R32-O17: Angular emergent primes and endpoint compactness no-go

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

In endpoint-adapted bases, a terminal product is triangular with diagonal factors

```text
X=p^Ω∏h_i,   Y=(−1)^n∏k_i
```

and shear `β`. Changing complements alters `β` by `Xm₀−Ym_n`, so only its residue modulo
`gcd(X,Y)` is intrinsic. In the physical basis the complete terminal boundary is

```text
M_w=[[Y,−RY],[c,X−Rc]],
```

where terminality leaves `c` free. The full fixed `p^Ω` kernel fixes one p-adic residue but
does not bound the primitive pole `((Rc−X)/g,c/g)`, `g=gcd(X,c)`. Even all diagonal factors,
Smith labels, valuations, and finitely many congruence labels permit unbounded abstract shear
unless the actual off-diagonal recurrence is retained.

The obstruction occurs in a genuine first-hit word. For

```text
(p,s,A,D,L)=(3,2,467,−35,124),   w=[3,1],
```

Lean checks the exact terminal product and primitive pole `(494,−41)`. The new pole primes
`19` and `41` divide neither the coefficient/reset data nor either cyclotomic branch factor
`3³−1`, `3¹−1`. Hence determinant allocation does not control angular support.

Separately, the depth-two wait gauge is conjugate to `diag(1,p^(2(b−a)))`, whose projective
adelic height is `p^(2|b−a|)`, not one. The product formula cancels common scalar size, not
directional eigenvalue ratio.

**Scope:** the exact emergent-prime certificate is formalized. The complement calculus,
boundary-freedom theorem, and adelic gauge-height calculation are independently audited. They
exclude arguments that discard the actual off-diagonal guard recurrence, not a bound exploiting
that recurrence.

**Artifact:** `ReturnGuard.Examples.decreasingMortal_emergentAngularPrimes` in
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean), with reconstruction in
[`m32-angular-emergent-primes-2026-08-08.md`](audits/m32-angular-emergent-primes-2026-08-08.md).
The surviving additive continuant is already owned by the cumulative endpoint recurrence; no
duplicate API was added.

**Use:** abandon fixed-support `S`-unit bounds and direction-free product-formula compactness.
Attack `gcd(X_n,c_n)` or the primitive additive continuant along actual legal terminal histories.

### R32-O18: Finite rational radial-atlas obstruction

**Kind:** obstruction
**Evidence:** audited
**Disposition:** graduated

Suppose finitely many modes express the ready tail as a reduced rational function

```text
t=T_v(p^a),
```

and every transition `e:v→w` changes the wait by one fixed integer `d_e`. Clearing the exact
tail-transition identity forces `P_w(p^(d_e)X)` to divide the source denominator. The quotient
divides `X−1`. Degree transport around a directed cycle then forces every quotient to be
constant and all chart numerator and denominator degrees to agree.

Comparing constant terms and the leading terms that must cancel yields

```text
C^ℓ=(∏_e p^(d_e))^(s+N).
```

Since `C` is a p-unit and `s+N>0`, every directed cycle has total shift `Σd_e=0`.
For an actual nonperiodic orbit, every recurrent edge is sampled at infinitely many distinct
prime powers and therefore satisfies the rational identity. Zero cycle weights make the
recurrent shifts a graph coboundary, bounding all waits. Finitely many chart states remain, so
determinism forces exact eventual periodicity and bounded reduced denominators.

**Scope:** this excludes finite rational charts with a finite transition alphabet of fixed
additive wait shifts. It does not exclude infinitely many charts or shifts, or angular state not
rationally determined by the current `p^a` and one finite mode.

**Artifact:** independent reconstruction in
[`m32-finite-radial-atlas-2026-08-08.md`](audits/m32-finite-radial-atlas-2026-08-08.md).
The checked one-chart rail and bounded-denominator orbit theorem remain the executable owners;
no duplicate rational-atlas API was retained.

**Use:** retire finite carry-mode counter machines even when no single global rail exists. A
counter-orbit must retain genuinely unbounded angular history or an unbounded wait-difference
alphabet.

### R32-S33: Terminal Casoratian and two-sided order allocation

**Kind:** structure theorem and decidable stratum
**Evidence:** formalized
**Disposition:** active

Let `P` be the endpoint product before the final branch, `c⁻=P₂₁`, and suppose the final
product sends reset to terminal with scalar `X` and lower-left coefficient `c`. The lower row of
the final transfer gives

```text
z c − X c⁻ = det P,
```

where `z` is the preceding cumulative denominator. Hence every common divisor of `X` and `c`
already divides the determinant support before the final branch. Since the fixed mod-`p` flag
makes `c` a p-unit,

```text
gcd(X,c) ∣ (DL)^(n−1) ∏_(i<n−1)(p^aᵢ−1).
```

No factor born at the terminal boundary can enter primitive pole normalization.

For a terminal schedule define prefix and suffix wait gcds `eᵢ` and `dᵢ`. After deleting
the fixed support of `DLR`, the full primitive cyclotomic part of exact order `dᵢ` divides
forward content `hᵢ`, while that of exact order `eᵢ` divides reverse content `kᵢ`. Thus only
mass whose order is broken on both chronological sides remains freely allocable. Primitive-part
growth makes the gcd of all waits effectively finite and yields an explicit decider for the
stratum `a₀∣a₁∣⋯∣aₙ₋₁`.

**Scope:** the Casoratian is Lean-checked. The global content induction, effective threshold,
and divisibility-chain algorithm are independently audited from checked local theorems. An
arbitrary sequence of order-breaking bridges can replenish earlier determinant support; no
global amortization or counter-orbit follows.

**Artifact:** `ReturnGuard.endpointProduct_append`,
`ReturnGuard.endpointTransfer_casoratian`, and
`ReturnGuard.terminalCommonDivisor_dvd_previousDet` in
[`ReturnGuardCumulative.lean`](MatrixMortality/ReturnGuardCumulative.lean), with the global proof in
[`m32-casoratian-order-allocation-2026-08-09.md`](audits/m32-casoratian-order-allocation-2026-08-09.md).

**Use:** replace the undifferentiated `gcd(Xₙ,cₙ)` obstruction by the doubly order-broken
core. A decision proof must amortize bridges which destroy exact order on both sides; an
undecidability construction must realize such recycled support along one exact reset orbit.

**Next:** prove global amortization of doubly order-broken bridges or exhibit a synchronized
support-recycling counter-orbit.

### R32-S34: Exact moving-prime ledger

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For a primitive endpoint reduction with source numerator `r`, forward content `h`, wait `a`,
and any divisor `d` coprime to `pDL`, Lean proves

```text
d∣h ⇔ d∣r ∧ d∣(pᵃ−1).
```

This is prime-power exact and applies to composite divisors. Equivalently, for every prime
`ℓ∤pDL`, forward content receives exactly the minimum of the multiplicities in `r` and
`pᵃ−1`; the excess remains reverse. There is no hidden auxiliary-prime register outside the
current endpoint numerator and branch boundary.

Combined with `R32-S33`, an angularly emergent prime is inert when created. It can participate
in later primitive cancellation only after a wait divisible by `ord_ℓ(p)` and simultaneous
reappearance in the endpoint numerator. An aperiodic counter-orbit therefore needs an explicit
infinite genealogy of synchronized births, not merely continual additive prime creation.

**Scope:** this is a local allocation theorem. It supplies neither a global lower bound on
content nor an infinite orbit. The reciprocal Euclidean coordinates and angular Wronskian are
culled as restatements of the cumulative endpoint recurrence and `R32-S33`. Rational Mahler
rails of degree at least two were already excluded by the stronger checked rail-degree theorem.

**Artifact:** `ReturnGuard.PrimitiveEndpointReduction.divisor_dvd_content_iff` in
[`ReturnGuardContinued.lean`](MatrixMortality/ReturnGuardContinued.lean), with synthesis in
[`m32-moving-prime-ledger-2026-08-09.md`](audits/m32-moving-prime-ledger-2026-08-09.md).

**Use:** on the constructive side, require every proposed auxiliary prime to satisfy both exact
ledger conditions at each activation. On the decision side, combine those synchronization
events with the two-sided order budget rather than bounding a fictitious hidden register.

**Next:** decide whether synchronized moving-prime activations admit an effective global bound
or an infinite exact genealogy.

### R32-S35: Positive projective-incidence genericization

**Kind:** reduction and normalization
**Evidence:** formalized
**Disposition:** active

For nonzero row and column and unit controls `G,H`, the two exceptional source rays of the
ordered reverse compiler are exactly

```text
H ker(r),
H G⁻¹ H ker(r).
```

Lean proves that `αβ≠0` is equivalent to the source avoiding these two rays. Intersecting this
set with the exceptional set after swapping `G,H` leaves at most two sources. If that common set
has two points, Lean proves that the relative projectivity permutes it, so the two labelled
successors are simultaneously internal or external. Positive first exit therefore reduces
unrestricted PI₂ nonadaptively to at most two GPI₂ queries, each reached by a positive prefix of
length at most two.

Every generic instance also admits independent nonzero generator scalings

```text
H' = αH,      G' = (α²/β)G
```

for which `α'=β'=1`. Lean proves both identities and preserves the zero coefficient of every
word, including the empty word.

**Scope:** the exact exceptional locus, common-set cardinality, two-point transition mechanism,
and unit normalization are formalized. The finite first-exit synthesis is independently audited.
This is a bounded truth-table reduction, not a many-one reduction to one generic instance, and
it does not decide GPI₂. The residual fixed-ray and order-three one-query forms are culled from
the master frontier because closing them would not decide any additional master stratum.

**Artifact:** `ProjectiveIncidence.generic_iff_sourcePoint_not_mem_badSources`,
`ProjectiveIncidence.commonBadSources_two_transition_iff`, and
`ProjectiveIncidence.exists_unitNormalized` in
[`ProjectiveIncidence.lean`](MatrixMortality/ProjectiveIncidence.lean), with reconstruction in
[`m32-three-query-genericization-2026-08-09.md`](audits/m32-three-query-genericization-2026-08-09.md)
and
[`m32-two-query-genericization-2026-08-09.md`](audits/m32-two-query-genericization-2026-08-09.md).

**Use:** identify PI₂ and GPI₂ at the level of decidability and normalize all further attacks to
`α=β=1`. The live rank-(2,2) enemy is GPI₂ itself; exceptional-scalar plumbing is retired.

**Next:** decide normalized GPI₂; do not reopen exceptional-scalar plumbing.

### R32-S36: Guarded affine projective incidence

**Kind:** compiler
**Evidence:** audited
**Disposition:** active

For a prime `p`, two branches

```text
Fᵢ(z)=(aᵢz+bᵢ)/p,       p∤aᵢ,
```

with distinct legal residues compile to two upper-triangular projective matrices. The first
illegal branch from a p-integral state creates valuation `−1`; every subsequent branch lowers
that valuation. Hence a word reaches a p-integral target if and only if every letter was legal.
At `p=2`, the residues exhaust parity and the resulting source dynamics is deterministic.

Two explicit predecessor nonincidences are exactly the genericity conditions. When they hold,
the existing scalar normalization makes `α=β=1` without changing any word zero.

**Scope:** this proves a compiler and a complete malformed-word converse, not universality or
decidability of binary guarded affine reachability.

**Artifact:** [`audits/m32-projective-arithmetic-guard-2026-08-10.md`](audits/m32-projective-arithmetic-guard-2026-08-10.md).

**Use:** search for intrinsic arithmetic universality inside normalized GPI₂ rather than a
separate finite word controller. Any decision theorem must consume the parity-selected family.

**Next:** decide reachability for two-branch parity-selected affine maps, or reduce a known
undecidable arithmetic system to that exact family while preserving the two genericity
nonincidences.

### R32-S37: Normalized shortcut-Collatz incidence

**Kind:** reduction and arithmetic benchmark
**Evidence:** formalized
**Disposition:** active

The fixed projective inverse branches

```text
A(z)=2z,       B(z)=(2z−1)/3
```

carry the pointwise shortcut-Collatz reaches-one set exactly. Starting at `1`, every binary word
either stays on integral legal predecessors or acquires negative 3-adic valuation at its first
illegal `B`; later letters cannot restore integrality. For every nonzero integer target `n`, the
row `(1,−n)`, column `(1,1)ᵀ`, and scalar representatives

```text
Hₙ=(1/2−n)A,       Gₙ=((1/2−n)²/(−3n))B
```

have `α=β=1` and the same complete word-zero language. Lean proves

```text
∃w, incidence(Gₙ,Hₙ,(1,−n),(1,1)ᵀ,w)=0
  ↔ n reaches 1 under shortcut Collatz.
```

**Scope:** this is a pointwise reduction, not a proof of the universal Collatz conjecture and
not an undecidability theorem. The normalized matrix representatives vary by central scalar,
but their two projective transformations are fixed.

**Artifact:** `ProjectiveCollatz.reachesOne_iff_shortcutCollatz`,
`ProjectiveCollatz.predecessorState_reaches_or_negative`,
`ProjectiveCollatz.normalizedScalars`, and
`ProjectiveCollatz.exists_normalizedIncidence_zero_iff` in
[`ProjectiveCollatz.lean`](MatrixMortality/ProjectiveCollatz.lean), with reconstruction in
[`m32-collatz-incidence-2026-08-10.md`](audits/m32-collatz-incidence-2026-08-10.md).

**Use:** every normalized GPI₂ decision proof must consume this intrinsic arithmetic family.
Do not replace it with an intended-language simulation or a finite malformed-word controller.

**Next:** decide the fixed-projectivity predecessor family by an exact symbolic arithmetic
invariant, or embed a known universal guarded-affine system through the same all-word p-adic gate.

### R32-S38: Jacobi schedule incidence

**Kind:** structure theorem and obstruction
**Evidence:** formalized core; audited strengthening
**Disposition:** active

For consecutive primitive endpoint reductions, the native edge quotient

```text
τᵢ=L tᵢ/(hᵢtᵢ₊₁)
```

obeys the exact generalized Jacobi transition

```text
qᵢ₊₁+qᵢ₊₁ˢ/τᵢ₊₁
  = A/L+(D/L)(qᵢˢ+(qᵢ−1)τᵢ).
```

Lean proves this directly from two primitive endpoint reductions. With
`βᵢ=(qᵢ−1)τᵢ`, the backward update is fractional-linear in `βᵢ₊₁`; Lean also proves its exact
difference factor. Iterating that factor shows that every prescribed positive wait schedule has
one compatible p-adic unit tail. It comes from the rational reset exactly when one explicit
p-adic continued fraction equals

```text
Lq₀ˢ(q₀−1)/(A+D−Lq₀).
```

Every adjacent handoff `αᵢ=βᵢ/(qᵢ₊₁−1)` approximates `A/D` to depth
`min(aᵢ₊₁,saᵢ)` and pays the corresponding Archimedean rational height. A finite handoff alphabet
therefore has bounded waits and is eventually periodic. If all states lie on one fixed rational
ready-tail chart, target readiness itself forces an affine monomial wait rail; the checked rail
theorem excludes it without assuming the successor schedule in advance.

**Scope:** no aperiodic rational schedule, fixed coefficient tuple, or undecidability reduction
is constructed. The p-adic completion, reset equivalence, handoff-height consequence, and
automatic one-chart reduction are audited; only the finite Jacobi identities are kernel checked.
The packet-allocation table is already owned by `R32-S34` and is not duplicated.

**Artifact:** `jacobiTail`, `jacobiBackward_sub`, and
`PrimitiveEndpointReduction.jacobiTail_transition` in
[`ReturnGuardContinued.lean`](MatrixMortality/ReturnGuardContinued.lean), with reconstruction in
[`m32-jacobi-schedule-incidence-2026-08-11.md`](audits/m32-jacobi-schedule-incidence-2026-08-11.md).

**Use:** reject schedule-first counterexamples. A genuine split counterorbit must solve the
rational reset incidence through an infinite unbounded-height handoff alphabet whose chart
depends on accumulated history.

**Next:** construct such a reset incidence, or prove that its moving Jacobi tail cannot coexist
with first-hit terminality and the global content budget.

### R32-S39: Reset companion and bilateral shadow

**Kind:** structure theorem and obstruction
**Evidence:** formalized core; audited strengthening
**Disposition:** active

Every reset-started first-hit terminal address canonically pulls the reset backward through the
same inverse branches. The resulting primitive companion follows the same waits and ends at
reset. If `Wᵢ` is the projective cross of the actual and companion states, their forward
contents are `hᵢ,ĥᵢ`, and the actual complementary content is `kᵢ`, then

```text
p^(saᵢ) ĥᵢ Wᵢ₊₁ = −kᵢ Wᵢ.
```

After removing the forced suffix power, the crosses are nonzero p-unit integers `δᵢ` with
terminal value `±R`. For the four content products this gives

```text
δ₀=(±1)RĤ/K=(±1)RH/K̂.
```

Thus actual reverse mass outside reset support reappears as companion forward mass. The endpoint
product compresses the uncancelled residue to one angular gcd deficit

```text
|δ₀|=|RH|/|K̂|.
```

Primewise differences of consecutive `δᵢ` are the exact bilateral packet ledger. Existing
boundary theorems force every moving layer surviving in `H/K̂` to be order-broken on both
chronological sides.

Monotone descent is nevertheless false. The checked positive family indexed by `n` has

```text
c=24n+1,  R=24n+2,
(R,1) --h=−cR--> (0,1),
((12n+1)(108n+5),−2) --ĥ=(12n+1)(108n+5)--> (R,1),
K̂=4c,
|H|/|K̂|=R/4=(12n+1)/2.
```

The expansion is unbounded, even though the actual step is nonmaximal. It is supported on the
fixed tuple through `2R`, so it refutes per-step or coefficient-uniform contraction but not a
coefficient-effective global amortization.

**Scope:** companion existence and the bilateral identities are audited compositions of the
checked inverse-address, integral-lift, exterior-product, and complementary-content theorems.
Lean checks the complete parametric counterfamily. No terminal bound or amortization constant is
claimed.

**Artifact:** `ReturnGuard.Examples.resetCompanion_counterfamily` in
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean), with reconstruction in
[`m32-reset-companion-2026-08-11.md`](audits/m32-reset-companion-2026-08-11.md).

**Use:** replace endpoint-only reverse charging by the canonical first-hit companion. Reject
monotone shadow descent and any proof multiplying local Smith savings without charging bilateral
packet overlap.

**Next:** prove coefficient-effective bilateral shadow amortization
`|Hₓ|/|K̂ₓ|≤Cρ^m(w)` for first-hit terminal words, or construct a rational reset-incidence
orbit whose doubly broken packet intervals repay every Smith loss aperiodically.

### R32-S40: Binary affine Syracuse collapse

**Kind:** structure theorem and obstruction
**Evidence:** audited
**Disposition:** active

At denominator two, the guarded-affine GPI₂ compiler is exactly an integer least-significant-bit
map

```text
T(2m)=a₀m+c₀,       T(2m+1)=a₁m+c₁,
```

with odd slopes. A common odd denominator merely conjugates the rational 2-integral orbit to
the numerator orbit and supplies no extra register. If both slope magnitudes are one, every
orbit enters an explicit invariant interval. If both are at least three, absolute value escapes
monotonically outside an explicit interval. Both strata are decidable by exact finite-box
simulation.

Only the mixed stratum survives. Affine conjugacy and acceleration through the unit branch put
it in one of the two forms

```text
S₊(n)=(an+B)/2^v₂(an+B),
S₋(n)=(−1)^(v₂(an+B)−1)(an+B)/2^v₂(an+B),
```

for fixed odd `a,B`. Every length-`N` macro has linear multiplier with odd numerator
`a₀^N₀a₁^N₁` and denominator `2ⁿ`. This excludes direct radix-tag append, direct
FRACTRAN valuation decrement, and finite affine-chart microcoding: the last chart factors
always telescope on controller cycles. It does not exclude computation by carries. Writing
`η=−B/a∈ℤ₂`, the positive map deletes the maximal common binary prefix of `n` and the
fixed eventually periodic word `η`, then multiplies the odd tail by `a`. That nonhomomorphic
carry transducer is the sole surviving universality seam inside this compiler.

The genericity exceptions are bounded preprocessing, not a second obstruction. Follow the
deterministic orbit through the at-most-two common bad source rays until target, repetition, or
first exit; after exit one ordering is generic, and the checked scalar normalization and
two-plane pushout complete the reduction.

**Scope:** no invariant universal configuration code, halting converse, undecidability theorem,
or decision theorem for the mixed Syracuse family is obtained. The literature-exhaustion claims
are not promoted. The arithmetic conjugacies, finite-box arguments, and scoped multiplier
obstructions are independently audited; no narrow duplicate Lean orbit API was added.

**Artifact:**
[`m32-binary-affine-syracuse-2026-08-11.md`](audits/m32-binary-affine-syracuse-2026-08-11.md).

**Use:** restrict further guarded-affine universality attacks to the mixed signed Syracuse
family. Do not spend the all-word compiler on direct radix, tag, FRACTRAN, denominator-register,
or finite affine-controller encodings.

**Next:** exhibit an invariant configuration-code family driven by multiplication carries in
the fixed `ax+B` map, prove that family's reachability decidable, or leave the guarded-affine
lane for a genuinely projective mechanism.

### R32-S41: Parabolic rational-subset normal form

**Kind:** reduction and obstruction
**Evidence:** audited
**Disposition:** active

For arbitrary `G,H∈GL₂(ℚ)` and nonzero incidence row and column, choose rational bases `C,D`
whose first columns are the source and a target-kernel vector. After localizing at the finite set
of coefficient and determinant primes,

```text
∃p∈{G,H}*, rpc=0
⇔ I ∈ {G,H}*^⁻¹ D Bₛ C⁻¹,
```

where `Bₛ` is the explicitly finitely generated upper-triangular subgroup of
`GL₂(ℤ[S⁻¹])`. Thus arbitrary PI₂, and hence normalized GPI₂, is one effective
identity-membership question for a rational subset of an `S`-arithmetic matrix group. Uniform
decidability of that problem, here named SARSM₂, would decide the rank-(2,2) profile; no such
theorem is imported or claimed.

The fixed shortcut-Collatz projectivities already generate

```text
Γ₆=ℤ[1/6]⋊ℤ².
```

Let `P` be their positive monoid, `K` the stabilizer of one, `R=PK`, and
`τₙ(z)=z+N−1`. Then

```text
τₙ∈R ⇔ ∃p∈P, p(1)=N
     ⇔ N reaches 1 under shortcut Collatz.
```

The final equivalence is the checked all-word predecessor theorem. Hence only the queried
translation varies: one fixed rational subset of one fixed metabelian group already contains
the arithmetic benchmark.

The positive monoid is free by an explicit affine normal form, so relations are not the
obstruction. Nor does the Tits alternative close the decision lane. Every finite-index subgroup
of `Γ₆` retains rank-two multiplier image and cannot reduce to a one-dilation affine group;
adjoining non-elementary generators does not stop an automaton from remaining inside this
exponentially distorted cusp. Fixed-arity `S`-unit equations do not control its unbounded ordered
translation sums.

**Scope:** the parabolic reduction, cusp computation, fixed-subset equivalence, and freeness
argument are independently audited. Claims about the current literature remain reported, not
theorem evidence. Neither SARSM₂, Collatz decidability, nor an undecidability reduction is supplied.
No broad rational-subset infrastructure was added to Lean; the existing formal predecessor and
GPI₂ compilers are the kernel-checked consumers.

**Artifact:**
[`m32-parabolic-rational-subset-2026-08-11.md`](audits/m32-parabolic-rational-subset-2026-08-11.md).

**Use:** abandon a Tits-alternative split that treats the solvable branch as routine. Any GPI₂
decision theorem must control automaton membership in the rank-two affine cusp; any
undecidability theorem must cross the fixed two-branch Collatz boundary without assuming it.

**Next:** decide rational-subset membership for `ℤ[1/6]⋊ℤ²` or the narrower fixed subset
`R`, find a sound reduction into that fixed pair, or identify additional normalization structure
that makes GPI₂ smaller than ambient SARSM₂.

### R32-S42: Non-pure cubic endpoints and false waits

**Kind:** structure theorem and obstruction
**Evidence:** formalized core; audited strengthening
**Disposition:** active

For the non-pure companion ambient with polynomial `X³+X²−1`, Lean checks

```text
A³+A²=I,       det A=1,       A³≠λI,
M_(n+3)=M_n−M_(n+2).
```

Its positive returns are units and wait zero is the unique singular return. The arbitrary
physical twist has enough freedom to align the actual singular image and kernel while retaining
a free selected binary semigroup. In one explicit rank-two physical family,

```text
M₀M₁M₀=0,
```

and exact interval ping-pong for selected waits one and five proves freeness. Endpoint placement
is therefore not the non-pure obstruction.

A second physical twist isolates the true failure. Its selected returns are upper triangular
with nonzero lower diagonal, and Lean proves that every word over waits `{1,5}` sends the actual
singular image `[79:90]` to a ray with nonzero lower coordinate. The selected endpoint orbit is
also injective by audited disjoint-interval ping-pong. Nevertheless every letter of

```text
[12,12,8,12,12,15,8]
```

is positive and strictly unselected, while Lean proves

```text
M₀ M₁₂ M₁₂ M₈ M₁₂ M₁₂ M₁₅ M₈ M₀=0.
```

Thus selected freeness, actual endpoint faithfulness, and selected immortality give no
arbitrary-word converse. After normalization, the complete remaining predicate is one endpoint
coefficient for an arbitrary common left factor `P` and the fixed relative recurrence

```text
H₁=I,       H₅∼diag(2/5,1),       H_(n+3)=H_n−H_(n+2).
```

**Scope:** Lean checks the ambient and return recurrence, unit ambient, non-pure relation,
rank-two cuts, terminal-aligned zero, strict unselected word, its exact false zero, and avoidance
of the kernel by every selected word. Irreducibility, the unique singular-index calculation,
and both ping-pong arguments are independently audited. No all-waits decision or sound universal
subalphabet is claimed.

**Artifact:** `CubicReturn.NonPure.terminal_zero`,
`CubicReturn.NonPure.falseWait_zero`, and
`CubicReturn.NonPure.selected_lower_ne_zero` in
[`CubicReturnNonPure.lean`](MatrixMortality/CubicReturnNonPure.lean), with reconstruction in
[`m32-cubic-endpoint-false-waits-2026-08-11.md`](audits/m32-cubic-endpoint-false-waits-2026-08-11.md).

**Use:** retire endpoint-alignment no-go arguments and selected ping-pong as a syntax guard. A
cubic universality proof must first exclude every false hit from the full positive-wait
recurrence; a decision proof may attack that exact recurrence directly.

**Next:** decide endpoint reachability for the fixed `H_n` recurrence, or find an arithmetic
normalization proving every first hit has a selected-word representative. Finite congruence
filters alone cannot isolate `{1,5}` because ambient powers are periodic modulo every modulus.

### R32-O19: Projective queue centralizer obstruction

**Kind:** obstruction
**Evidence:** audited
**Disposition:** graduated

Let `ρ:Σ*→PGL₂(ℚ)` be a homomorphic word store with an orbit containing at least three points.
Every projectivity implementing the tail-uniform update `(q,uv)↦(q′,vp)` has the necessary form

```text
S_q′ Z ρ(u)⁻¹ S_q⁻¹,
```

where `Z` centralizes every store letter and maps `x_q` to `ρ(p)x_q′`. If the store is injective
on a binary free monoid, its common centralizer is trivial: otherwise the generated group lies
in a virtually abelian Möbius centralizer, contradicting exponential positive-word growth.
Every finite-controller cycle therefore has empty appendants, so total storage growth is
bounded.

**Scope:** the theorem concerns injective homomorphic projective stores and tail-uniform fixed
prefix/suffix rules. It does not exclude nonhomomorphic arithmetic encodings such as
[`R32-S36`](#r32-s36-guarded-affine-projective-incidence).

**Artifact:** [`audits/m32-projective-arithmetic-guard-2026-08-10.md`](audits/m32-projective-arithmetic-guard-2026-08-10.md).

**Use:** do not reopen free Möbius, continued-fraction, radix, tag, or queue stores with a finite
projective controller. A rank-(2,2) universality proof must obtain its memory from intrinsic
arithmetic dynamics.

### R32-O20: Transverse reverse reservoir

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The lawful period-three guard `(p,s,A,D,L)=(3,2,−953,473,2240)` has primitive endpoint contents

```text
h=(−160,−1204,−80),    k=(−13244,−7040,−344344),
hᵢkᵢ=DL(3^aⁱ−1).
```

Its endpoint macro fixes the reset ray with eigenvalue `3¹²∏hᵢ`, while its second rational
eigenline has eigenvalue `(−1)³∏kᵢ`. The former is coprime to thirteen and the latter has exact
13-adic valuation one. Repeating the legal cycle `N` times fixes the rational reset orbit but
raises those eigenvalues to the `N`th powers. Arbitrary reverse 13-mass is therefore invisible
to the projective endpoints.

**Scope:** this is an immortal periodic orbit. It kills path-independent or endpoint-coercive
charging of every reverse packet, not a bound exploiting first-hit terminality, reset anchoring,
and aperiodicity.

**Artifact:** `ReturnGuard.Examples.cycle_endpointReductions` and
`cycle_transverseReservoir` in
[`ReturnGuardTransverseReservoir.lean`](MatrixMortality/ReturnGuardTransverseReservoir.lean),
with reconstruction in
[`m32-transverse-reverse-reservoir-2026-08-10.md`](audits/m32-transverse-reverse-reservoir-2026-08-10.md).

**Use:** exclude endpoint-only reverse-mass potentials from the split decision lane. Any
surviving certificate must use the reset-started first-hit orbit and distinguish aperiodic
escape from periodic transverse storage.

### R32-O21: Finite-image positivity collapse

**Kind:** obstruction
**Evidence:** formalized core; audited application
**Disposition:** graduated

Let a set `S` generate a group `Γ`, and let `P=S*` be its positive monoid. In every finite
homomorphic image `φ(Γ)`, the submonoid `φ(P)` is a subgroup: each element has a positive power
equal to one, so its inverse is another positive power. Since `φ(P)` contains the group
generators, it equals `φ(Γ)`.

For the fixed Collatz cusp

```text
Γ₆=ℤ[1/6]⋊ℤ²,   P={A,B}*,   K=Stab_Γ₆(1),   R=PK,
```

every finite ambient image therefore satisfies

```text
φ(R)=φ(Γ₆).
```

No translation `τ_N` can be separated from `R` by any finite monoid or group quotient of
`Γ₆`, regardless of whether `τ_N∈R`.

**Scope:** this concerns homomorphisms of the ambient group. It does not exclude an automaton
that retains positive spellings, or a nonhomomorphic abstraction carrying syntax or arithmetic
outside the group image. It does not weaken finite-quotient certificates for matrix families
outside this positive-coset form.

**Artifact:** `FinitePositiveImage.Submonoid.inv_mem_of_finite` and
`FinitePositiveImage.mclosure_eq_top_of_group_closure_eq_top` in
[`FinitePositiveImage.lean`](MatrixMortality/FinitePositiveImage.lean), with the `Γ₆`
application in
[`m32-gpi2-residue-blindness-2026-08-30.md`](audits/m32-gpi2-residue-blindness-2026-08-30.md).

**Use:** retire ambient congruence saturation on the fixed Collatz rational subset. Any finite
decision abstraction must preserve positive-word syntax rather than factor only through `Γ₆`.

### R32-O22: Congruence-blind free orbit

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let

```text
A=[[1,3],[0,1]],       B=[[1,0],[3,1]],
p=[1:1],               q=[10:13].
```

Ping-pong on the disjoint chambers `|t|>1` and `|t|<2/3` proves

```text
⟨A,B⟩≅F₂,       Stab(p)=1,       q∉⟨A,B⟩p.
```

Nevertheless, for every `N≥1` there is an explicit word `w_N` and a unit `u_N` modulo `N` with

```text
w_N p=u_Nq (mod N).
```

Writing `N=3^k m`, choose a CRT selector `x` equal to one modulo `m` and zero modulo `3^k`.
Choose `n` so that `13(1+3n)=10 modulo 3^k`. The five-factor bridge

```text
H(x,n)=L(x)U(3x)L(2x)U(−3xn)U(3n)
```

sends `p` exactly to `q` on the first component and to `[1+3n:1]=q` projectively on the second.
Because `x` is a multiple of three, this is a word in `A` and `B`.

**Scope:** the witnessing word depends on `N`. This places one target in the congruence closure
of one orbit; it does not make the whole orbit `p`-adically dense and does not decide generic
projective incidence. Lean checks the rational ping-pong no-instance, trivial stabilizer, free
representation, literal five-factor spelling, idempotent CRT interpolation, the modular
inverses, the CRT unit over composite rings, and one quantified `ZMod N` witness for every
positive `N`.

**Use:** reject eventual separation of every `GPI₂` no-instance by reductions modulo integers,
even under freeness and trivial source stabilizer. A surviving decision invariant must retain
Archimedean, height, syntax, or unbounded carry information.

**Formalization:**
[`MatrixMortality/CongruenceBlindOrbit.lean`](MatrixMortality/CongruenceBlindOrbit.lean), through
`bridgeMatrix_idempotent_projective_target`, `shearRepresentation_bridgeWord`,
`targetPoint_not_reachable`, `sourcePoint_stabilizer_trivial`, and
`shearRepresentation_injective`, together with `exists_bridgeWord_modular_hit` for the
end-to-end congruence closure.

**Artifact:**
[`audits/m32-congruence-blind-free-orbit-2026-08-30.md`](audits/m32-congruence-blind-free-orbit-2026-08-30.md).

### R32-D03: Bounded-denominator periodicity

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** graduated

For a reduced endpoint state `xᵢ=rᵢ/tᵢ`, readiness and complementary content give the exact
second-order recurrence

```text
p^(saᵢ₊₁) hᵢ₊₁ tᵢ₊₂
  = (A + Dp^(saᵢ) − Lp^aᵢ₊₁)tᵢ₊₁ + kᵢtᵢ,

hᵢkᵢ = DL(p^aᵢ−1).
```

If all positive reduced denominators `tᵢ` are bounded, Lean constructs an explicit ceiling for
both waits in every nondecreasing transition. A positive integer wait sequence cannot decrease
forever, so every wait is bounded by the larger of that ceiling and the initial wait. The
primitive numerators then lie in an explicit finite integral rectangle. Some state repeats,
and every functional stream is eventually periodic. Consequently every nonperiodic infinite
guard orbit has unbounded reduced denominators. The checked proof is uniform in every depth
`s≥2`, not only the campaign's critical depth two.

**Scope:** the proof is effective for a supplied denominator bound. It does not compute such a
bound for an arbitrary orbit and says nothing about the unbounded-denominator residue.

**Artifact:** `PrimitiveEndpointReduction.denominator_recurrence`,
`PrimitiveEndpointReduction.nonDecreasing_waits_le`,
`BoundedPrimitiveEndpointStream.state_mem_box`, and
`BoundedPrimitiveEndpointStream.eventually_periodic` in
[`ReturnGuardPeriodicity.lean`](MatrixMortality/ReturnGuardPeriodicity.lean) and
[`ReturnGuardFiniteOrbit.lean`](MatrixMortality/ReturnGuardFiniteOrbit.lean). Independent audit:
[`m32-bounded-denominator-periodicity-2026-08-02.md`](audits/m32-bounded-denominator-periodicity-2026-08-02.md).

**Use:** abandon integer-valued or bounded-denominator universality. The sole surviving
register in this split-spectrum guard is unbounded Archimedean denominator growth.

**Next:** force a denominator return from unbounded growth, or construct one coefficient-aligned
orbit with unbounded denominators and a genuinely nonperiodic wait word.

## Three-Generator Four-State Frontier

Formal promotion of this section is tracked in
[#5](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/5).

### M4-C01: Two-state pushout compiler

**Kind:** compiler
**Evidence:** formalized
**Disposition:** graduated

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

**Artifact:** the arbitrary finite-state routing and all-word laws
`controllerMatrix_mulVec_controllerVector` and
`controllerProduct_mulVec_controllerVector` in
[`MatrixMortality/ControllerPushout.lean`](MatrixMortality/ControllerPushout.lean), specialized
by `twoStateProduct_mulVec_phaseVector`,
`twoStateDataMatrix_rank_eq_four_of_ne`, `twoStateDataMatrix_rank_eq_three_of_eq`, and
`twoStateMortalityFamily_int_mortal_iff_nonempty_zero` in
[`MatrixMortality/TwoStatePushout.lean`](MatrixMortality/TwoStatePushout.lean). The independent
algebraic reconstruction is
[`audits/m43-two-state-pushout-2026-07-24.md`](audits/m43-two-state-pushout-2026-07-24.md).

### M4-O01: Exact toggle fusion leaves an immortal core

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For the paired controls, let

```text
H = im G_b = im G_c = span{e₁,e₃,e₄},
E = span{e₁,e₃}.
```

If a proposed fused generator satisfies

```text
SG_b = TG_b,       SG_c = TG_c,
```

then applying this identity to the common first column already gives `Se₁=e₁`. Both data
matrices also fix `e₁`, so every word over `{G_b,G_c,S}` fixes a nonzero column and cannot be
zero. One exact contextual identity is sufficient; the original invertible-two-plane argument
is stronger than necessary.

Separately, `S^r=T` with `r>0` makes `S` invertible, so no other pure power of `S` can be
rank one or zero.

**Scope:** exact contextual toggle identities and pure power codes only. A mixed macro may
break the shared plane internally and reconstruct it at its boundary.

**Use:** reject `T+P`, `TP`, `PT`, and power-coded toggle/punctuation proposals whenever they
claim exact local toggle semantics.

**Artifact:** `exactLeftToggleFusion_fixes_anchor` and `exactLeftToggleFusion_immortal` in
[`MatrixMortality/TwoStateObstructions.lean`](MatrixMortality/TwoStateObstructions.lean).

### M4-O02: Two-private-state phase signature

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Suppose an exact phase compiler shares a two-dimensional upper plane and stores every private
lower channel in a quotient `Q` of dimension at most two. Let `q₀` be the distinguished rule
phase and `q₁,q₂` two consecutive deletion phases. If two data controls agree on `q₁,q₂`, a
cyclic control carries `q₁` to `q₂` and eventually carries `q₂` back to `q₀`, all up to nonzero
scales, then the controls also agree on `q₀`.

The proof is a sharp dimension dichotomy. If `q₁,q₂` are independent, they span `Q`, so
agreement on them is global. If they are dependent, the cyclic control preserves their line
and carries that line back to `q₀`; agreement again reaches `q₀`.

In the supplied Neary source all deletion lower words coincide, whereas the two rule lower
scales differ whenever the body is nonempty. The checked generic theorem therefore makes the
putative rule scales equal, while `nearyLowerScale_rule_ne` makes them unequal.

**Scope:** exact phasewise `4=2+2` shared-channel realizations, including phase rescaling,
projective normalization, upper-plane shears, and basis changes. Nonletterwise macros and
same-zero representations remain outside the theorem.

**Use:** closes the direct extension of paired-role compression from two phases to the full
Neary deletion clock.

**Artifact:** `twoPrivateState_ruleScale_eq` proves the generic phase theorem and
`neary_twoPrivateState_phaseCompiler_impossible` instantiates the Neary scale signature in
[`MatrixMortality/PhaseSignature.lean`](MatrixMortality/PhaseSignature.lean).

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
**Evidence:** formalized
**Disposition:** graduated

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
The exact initial-queue criterion is
`closedSubstitutionHalts_iff_noReachableCycle` in
[`MatrixMortality/ClosedSubstitution.lean`](MatrixMortality/ClosedSubstitution.lean).

**Next:** use the checked criterion as a guardrail for every future source serializer.

### M4-O04: Exact internal/final code defect

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Suppose a binary source morphism `h` gives one semantic macro two distinct codewords `p≠q`
but preserves its upper word exactly:

```text
h(p)=h(q).
```

Then `h` is noninjective. By the two-word defect theorem, the images of the two binary letters
commute; the submonoid they generate is therefore commutative. The macro upper words

```text
û_b = u_bu_b,       û_c = 1u_b,       u_b=10^β1
```

do not commute: `û_bû_c` begins `10`, while `û_cû_b` begins `11`.

**Scope:** exact binary word-pair compilers with a state-independent upper morphism. A
state-dependent matrix gauge, an open residue, or solvability-only preservation is outside the
argument.

**Use:** distinct exact codewords cannot make one deletion macro mean “internal” in one place
and “final” in another.

**Artifact:** `binarySpell_not_injective_commute` proves the two-word defect theorem by
prefix cancellation and Euclidean descent. `neary_exact_internal_final_code_impossible`
derives the concrete macro contradiction in
[`MatrixMortality/BinaryDefect.lean`](MatrixMortality/BinaryDefect.lean).

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

**Scope:** [`M4-M02`](#m4-m02-universal-monomial-cube-root-blade) now supplies a rational
rank-one word uniformly, but no parameter satisfying both source boundary alignments is known.
Even such a solution would still require an arbitrary-product converse for every other mixed
fragment.

**Use:** independent matrix-level fallback if the two-state source route stalls.

**Next:** solve the two-sided boundary problem on the monomial blade, with the annihilator
guard [`M4-O06`](#m4-o06-punctuation-image-annihilator) imposed before any all-word claim.

## Three-Letter Source Frontier

### M4-M02: Universal monomial cube-root blade

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** parked

For one paired data matrix, write

```text
G = [[1,l,u,e], [0,0,0,0], [0,0,a,0], [0,m,0,n]],
B⁻¹GB = JF,
F = [[1,u,e+l,l-e], [0,a,0,0], [0,0,(m+n)/2,(m-n)/2]].
```

When `a u (l+e) (m-n) (m+n) (em-ln)≠0`, put

```text
p = 2(em-ln)/(m+n),
r = u(m-n)/(2a(l+e)),
q = 1/(pr),
A = [[0,0,p], [q,0,0], [0,r,0]].
```

Then `A³=I₃`. With `S=B diag(A,-1)B⁻¹`, direct calculation gives

```text
S³=T,                  rank(GSGSG)=1.
```

Indeed, for `Q=F diag(A,-1)J`, one has `det Q=e₂(Q)=0`, `rank Q=2`, and
`B⁻¹(GSGSG)B=JQ²F` with `rank Q²=1`. Rank-one existence is therefore uniform in the role
parameters; it is not an exceptional rational point on an incidence curve.

**Scope:** the blade's row and column are generally wrong. On the audited `β=3`, body-`bb`,
desynchronized diagnostic, the column is nonannihilating and the row has the safe length sign,
but neither boundary aligns. Exact bounded context and digit-resultant searches found no repair;
they are not impossibility theorems. No arbitrary-fragment converse is known.

**Use:** start future cube-root attacks from this closed rank-one formula. Do not spend another
search on bare rank-one incidence.

**Artifact:** [`audits/m43-cube-root-incidence-2026-08-05.md`](audits/m43-cube-root-incidence-2026-08-05.md).

**Next:** revisit only if an incomplete finite-order-root context escapes
[`M4-O07`](#m4-o07-closed-residue-monomial-obstruction). The parabolic construction
[`M4-M03`](#m4-m03-parabolic-blade-and-bridge-grammar) now owns the live cube-root attack.

### M4-O06: Punctuation-image annihilator

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

If a proposed nonzero punctuation has rank-one form `P=CL`, then any legal context with
`UC=0` or `LV=0` gives the unconditional zero word `UP=0` or `PV=0`. The usual self-incidence
test `L C≠0`, equivalently `P²≠0`, does not exclude either defect.

This kills the rational cubic component found for the repeated `Q_{b,2}²` incidence. Its
punctuation image is the intended terminal line, but `Q_{b,2}C=0`; prepending the legal fragment
`G_bS²` therefore annihilates the punctuation independently of the source computation.

**Scope:** this is a necessary local guard, not an all-fragment converse. The parabolic atom
family now passes every one-step guard, but longer annihilating contexts remain possible.

**Use:** before promoting a cube-root candidate, test `Q_{x,r}C≠0` and the row-dual condition
for both data letters and every residue modulo six. Then classify longer rank drops.

**Artifact:** the source-independent laws are `unit_mulVec_ne_zero` and
`vecMul_unit_ne_zero` in [`MatrixMortality/RankOne.lean`](MatrixMortality/RankOne.lean). The
parabolic family is discharged by `ParabolicBlade.atom_mulVec_column_ne_zero` and
`ParabolicBlade.row_vecMul_atom_ne_zero` in
[`MatrixMortality/ParabolicBlade.lean`](MatrixMortality/ParabolicBlade.lean).

### M4-O07: Closed-residue monomial obstruction

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

For the finite-order monomial blade, its reduced column `c` obeys

```text
Y(c) - (u/a)X(c) = 2(l+e)/(m+n).
```

Every forward or reverse closed ternary positional context sends the Neary terminal column to
projective coordinates in `ℤ[1/3]`, and `u/a∈ℤ[1/3]`. For every nonempty lawful paired macro,
the right side retains a denominator prime outside `3`: the terminal `b` case retains `5`, and
the terminal `c` case is excluded by the final false digit modulo `3`. Closed contexts therefore
cannot align the blade column.

**Scope:** closed standard-ternary positional macros and their inverses. An incomplete root
fragment adjacent to punctuation, a different same-zero series, or a nonmonomial root lies
outside the theorem. The exact arithmetic has been reconstructed, but the report's complete
“lawful macro” grammar is not yet a repository definition, so this record remains audited rather
than Lean-checked.

**Use:** do not spend further effort on closed-context repair of the finite-order monomial blade.

**Artifact:** [`audits/m43-parabolic-blade-2026-08-05.md`](audits/m43-parabolic-blade-2026-08-05.md).

### M4-M03: Parabolic blade and bridge grammar

**Kind:** partial mechanism

**Evidence:** formalized

**Disposition:** active

In the common-image basis, the rational open root

```text
S = [[0,-1,0,0], [1,-1,0,0], [0,0,1,0], [x,y,2/3,1]],
x=(114ρ-11)/96,             y=-(38ρ-11)/32,
ρ=3^β
```

satisfies `S³J=TJ`. For `R=F_bSJ`, Lean proves

```text
rank R = 2,
R² = (1/32) c v,
det(FₓSʳJ)=0  ↔  x=b and r=1.
```

Thus `G_bSG_bSG_b` is a nonzero rank-one physical word, every other gap atom is invertible,
every one-step row and column guard holds, and two exceptional atoms separated by any regular
atom word cannot vanish.

Writing `R=AB` with `A` left-invertible and `B` right-invertible, define `K(M)=BMA`. The stronger
formalizer reduction is

```text
R M₁ R ⋯ Mₖ R = 0  ↔  K(M₁)⋯K(Mₖ)=0,
```

for arbitrary `3 × 3` middle matrices. The complete malformed-word problem is therefore a
`2 × 2` bridge-language problem.

**Scope:** this constructs and classifies the matrix mechanism. The residue-two wall
[`M4-O08`](#m4-o08-residue-two-necessary-wall) proves that every word whose gaps are congruent
to zero or one modulo three is nonzero. The safe-bridge cone
[`M4-S02`](#m4-s02-residue-zero-safe-bridge-cone) further excludes singular regular bridges
made solely from residue-zero atoms. These results do not supply open contexts whose boundary
rays realize the paired Neary zero series. The arbitrary grammar
[`M4-S06`](#m4-s06-arbitrary-defect-bridge-grammar) now proves that every bridge zero descends
to one projective incidence between consecutive singular bridges; it excludes every good
residue skeleton and every nonempty pure-defect endpoint. The surviving incidence is not yet
identified semantically. The scalar exterior compression is
retired by [`M4-O09`](#m4-o09-one-coordinate-exterior-fracture): residue-one `c` return needs a
second projective coordinate. The finite cone replacement is itself retired by
[`M4-O10`](#m4-o10-irrational-rotation-cone-fracture): powers of the legal atom `Q(b,4)`
accumulate projectively on the singular wall while remaining arithmetically nonzero. No `M₄(3)`
theorem follows yet.

**Use:** all further cube-root work starts from the consecutive-wall incidence normal form in
`M4-S06`. Do not redo finite-gap searches, rank-one factorization, defect-count casework, raw
residue-{0,1} products, pure-defect endpoints, or collective-wall cancellation.

**Next:** solve the one-sided exterior collision-avoidance problem isolated by
[`M4-S07`](#m4-s07-one-sided-wall-orbit-normal-form), or replace the affine semantic middle by a
syntax-sensitive incidence.

**Artifact:** [`MatrixMortality/ParabolicBlade.lean`](MatrixMortality/ParabolicBlade.lean),
[`MatrixMortality/ParabolicResidueWall.lean`](MatrixMortality/ParabolicResidueWall.lean),
[`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean),
[`audits/m43-parabolic-blade-2026-08-05.md`](audits/m43-parabolic-blade-2026-08-05.md), and
[`audits/m43-arbitrary-defect-2026-08-08.md`](audits/m43-arbitrary-defect-2026-08-08.md).

### M4-M04: Retuned semantic boundary

**Kind:** partial mechanism

**Evidence:** formalized

**Disposition:** parked

The retuned rational root

```text
S = [[0,-1,0,0], [1,-1,0,0], [0,0,1,0], [-19/24,1/8,2/3,1]]
```

satisfies `S³J=TJ` and moves the unique singular reduced atom to the gap-two `b` atom. With
`true ↦ 0` and `false ↦ 1`, every complete gap evaluates to a sparse side-normal matrix. The
affine fraction `(19·code(z)+1)/3^|z|` is injective on the terminal suffix language, so the
exceptional `2 × 2` bridge has determinant zero exactly on the four-tile Neary terminal equation.

The bridge is internal to a literal word over the root and two data generators:

```text
P(z) = G_b S² G_z G_b S² G_b.
```

Lean proves that one fixed minor of `P(z)` is `-2052·3^β` times the bridge determinant and that
fixed retractions recover the bridge from `P(z)`. Thus `P(z)` is never zero. On a terminal match
it is a nonzero outer product with fixed right row

```text
(-1, (15·3^β+3)/2, 28, 24).
```

Right annihilation of `P(z)` is exactly annihilation of this row. Any continuation made only of
complete gaps preserves its first coordinate and cannot work.

**Scope:** positive deletion width and nonempty body for uniqueness of the singular atom;
arbitrary complete Neary words for the semantic determinant; literal rational three-generator
contexts. Uniform scaling by `24` clears denominators. The fixed-row closure is obstructed by
[`M4-O13`](#m4-o13-retuned-pseudo-terminal-obstruction); no full semigroup decision is claimed.

**Use:** preserves the exact semantic boundary as stock. A standalone annihilator is useless:
`M4-O13` proves that it also closes a malformed context on an admissible no-instance. The
original parabolic incidence route `M4-M03` remains live and incomparable.

**Next:** none under the fixed-row closure. Reopen only with an exact theorem making annihilator
reachability itself equivalent to legal source halting, including the `M4-O13` poison instance,
or with a different endpoint row.

**Artifact:** [`MatrixMortality/ParabolicRetuned.lean`](MatrixMortality/ParabolicRetuned.lean),
[`MatrixMortality/ParabolicRetunedBoundary.lean`](MatrixMortality/ParabolicRetunedBoundary.lean),
and
[`audits/m43-retuned-semantic-boundary-2026-08-08.md`](audits/m43-retuned-semantic-boundary-2026-08-08.md).

### M4-M05: Boundary-guarded homogeneous punctuation

**Kind:** partial mechanism

**Evidence:** audited

**Disposition:** active

Let `ρ:F(s,t)→SL₂(ℤ)` be the explicit Schottky embedding generated by

```text
[[10,3],[3,1]],   [[10,-3],[-3,1]],
```

and let `Λ(A,B)=B⁻ᵀ⊗A` act on the four-dimensional lattice `M₂(ℤ)`. There are fixed integral
row and column vectors `λ,c₀` such that, on the entire Schottky product,

```text
λ Λ(A,B)c₀=0 ↔ A=B.
```

For binary homomorphisms `α,β`, put `D_i=Λ(ρ(α(i)),ρ(β(i)))`. Given fixed binary boundaries
`L,R` with `α(LR)≠β(LR)`, one rank-one matrix

```text
Π=(D_R c₀)(λD_L)
```

satisfies the exact arbitrary-word equivalence

```text
{D₀,D₁,Π} is mortal ↔ ∃w∈{0,1}*: α(LwR)=β(LwR).
```

Lean formalizes the left--right action, its coefficient and multiplication laws, unimodularity,
and the source-independent boundary-bearing separator theorem. The Schottky ping-pong and
rational-eigenline converse are independently audited.

**Scope:** binary positive interiors with fixed boundaries and a mismatch at the empty interior.
The theorem does not compile a four-letter transducer equation into such an instance. Without
the mismatch, the separator squares to zero unconditionally.

**Use:** once a positive binary fixed-boundary compiler is supplied, this mechanism finishes the
reduction to three integer `4 × 4` matrices without another malformed-word proof.

**Next:** construct the exact compiler from the marker-tail equation in `G3-M01`, or classify
that restricted binary GPCP seam as decidable and retire this route.

**Artifact:** [`MatrixMortality/SchottkyPunctuation.lean`](MatrixMortality/SchottkyPunctuation.lean),
[`MatrixMortality/TerminalTile.lean`](MatrixMortality/TerminalTile.lean), and
[`audits/m43-free-group-punctuation-2026-08-11.md`](audits/m43-free-group-punctuation-2026-08-11.md).

### M4-O13: Retuned pseudo-terminal obstruction

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

At deletion width three with body `bbcc`, the legal restricted tag orbit is

```text
ccb → bbccb → cbb → bbccb → ⋯,
```

so the checked Neary source has no genuine terminal word. A single malformed gap-thirty `b`
atom nevertheless acts as the extra production `b↦ccb`. Lean evaluates an explicit literal
length-100 word containing this atom and proves that its product is a nonzero outer product with
the lawful terminal row `(-1,204,28,24)`. For every literal continuation `z`,

```text
product(poison ++ z)=0 ↔ (-1,204,28,24) · product(z)=0.
```

**Scope:** one exact admissible no-instance suffices to refute a uniform or body-independent
fixed-row closure. The theorem does not decide whether a row annihilator exists for every body,
or classify all retuned zeros. Uniform denominator clearing preserves the obstruction.

**Use:** jointly deletes the retuned right-annihilator and independent-converse nodes. If the row
has no annihilator, forward closure fails; if it has one on the poison instance, soundness fails.
The only reopening is a new theorem making annihilator reachability itself source-equivalent, or
a different endpoint geometry.

**Artifact:**
[`MatrixMortality/ParabolicRetunedObstruction.lean`](MatrixMortality/ParabolicRetunedObstruction.lean)
and
[`audits/m43-retuned-pseudo-terminal-obstruction-2026-08-10.md`](audits/m43-retuned-pseudo-terminal-obstruction-2026-08-10.md).

### M4-C04: Original mixed-gap endpoint compiler

**Kind:** conditional compiler

**Evidence:** formalized

**Disposition:** parked

For `ρ=3^β`, let

```text
u* = (0,−2,1)ᵀ,                      k = (4,4,−1)ᵀ,
p  = (18,11)ᵀ,
c* = ((5ρ−1)/2,3ρ,−1/2)ᵀ.
```

The vector `k` spans the kernel of the exceptional input factor and `p` is the column of the
empty rank-one bridge. The complete semantic middle `N(upper,lower)` sends `c*` to the ray `u*`
exactly at a Neary terminal match.

Lean packages the remaining forward construction. For three-dimensional contexts `C,D`, a left
inverse of `C`, and nonzero scalars `λ,μ`, assume

```text
C u* = λk,
D A p = μc*.
```

Then

```text
Kρ(C N(upper,lower) D) Kρ(I) = 0
  ↔ upper ++ nearyMarker β = lower.
```

The existing exceptional-chain contraction turns this into the reduced literal word
`R(CND)RR`. Uniform denominator clearing is already available.

**Scope:** the theorem is conditional on exact endpoint contexts. It proves both directions for
the semantic middle once those contexts are supplied; it neither certifies lawful source history
nor proves the global converse for every other consecutive-wall incidence.

**Use:** retain the identity as semantic stock, not as a uniform reduction. The pseudo-terminal
obstruction [`M4-O15`](#m4-o15-original-pseudo-terminal-endpoint-obstruction) proves that
endpoint failure destroys completeness while endpoint success creates a false zero on an
admissible no-instance. Reuse it only behind a strictly narrower computable source image that
excludes that poison by a checked syntax invariant.

**Artifact:**
[`MatrixMortality/ParabolicSemanticObstruction.lean`](MatrixMortality/ParabolicSemanticObstruction.lean)
and
[`audits/m43-original-semantic-obstruction-2026-08-10.md`](audits/m43-original-semantic-obstruction-2026-08-10.md).

### M4-O14: Original semantic endpoint obstruction

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Put one complete side-normal correspondence block between the original parabolic exceptional
factors. In the reduced blade basis it is

```text
M(X,Y,σ,τ) = [[1,X,2Y], [0,σ,0], [0,0,τ]],
```

and Lean proves this is a fixed conjugate of `sidePcpMatrix`. Each original rule gap of length
three and erasure gap of length zero evaluates to this middle, and the identity composes over
arbitrary complete tile words. Its bridge determinant is

```text
det Kρ(M) = (9ρ/2)[τ(22X+31)-σ(22τ+11Y+9)].
```

It is strictly negative when both concrete ternary words are nonempty. Thus a nonempty complete
Neary block cannot itself be a wall.

For arbitrary fixed endpoint rays, the scalar incidence

```text
F(X,Y,σ,τ)=c₀+cX·X+cY·Y+cσ·σ+cτ·τ
```

obeys `22c₀-31cX-18cY=0`. With the repository's left-to-right ternary code, the actual terminal
plane is

```text
Y=tX+m,       τ=tσ,
m=(5·3^β−1)/2,       t=3^(β+1).
```

If `F` vanishes on this formal plane, its coefficients satisfy

```text
(31t−22m−18)cY=(38·3^β−7)cY=0.
```

Lean therefore proves that `F` vanishes on the entire length plane `τ=tσ`. This rules out exact
formal-plane recognition. It does not exclude a same-zero coincidence confined to the discrete
encoded language.

The two endpoint rays required by the conditional compiler [`M4-C04`](#m4-c04-original-mixed-gap-endpoint-compiler)
cannot be supplied by complete semantic contexts. The left equation would force a ratio of powers
of three to equal two; the right equation conflicts with a strict sign pattern. Both contexts
must contain incomplete gaps.

**Scope:** fixed left and right rays on the full formal terminal plane, and complete semantic
contexts at the two explicit compiler endpoints. The theorem does not exclude a discrete
same-zero coincidence, history-dependent or malformed mixed-gap contexts, or arbitrary
nonsingular transport. The former depth-`n+β+1` cylinder used the wrong terminal convention and
is rejected.

**Use:** delete nonempty complete blocks as endpoint walls, the direct fixed-ray formal-plane
identity, and complete-gap endpoint contexts. The mixed-gap ray equations are no longer a
master-path target because [`M4-O15`](#m4-o15-original-pseudo-terminal-endpoint-obstruction)
defeats every successful instantiation. Do not build another terminal coefficient abstraction.

**Artifact:**
[`MatrixMortality/ParabolicSemanticObstruction.lean`](MatrixMortality/ParabolicSemanticObstruction.lean)
and
[`audits/m43-original-semantic-obstruction-2026-08-10.md`](audits/m43-original-semantic-obstruction-2026-08-10.md).

### M4-O15: Original pseudo-terminal endpoint obstruction

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

At deletion width three with body `bbcc`, the lawful restricted tag orbit

```text
ccb → bbccb → cbb → bbccb → ⋯
```

never halts. In the original parabolic family, however, the regular atom

```text
Q(b,30)=N(203,241,243,243)
```

is exactly the malformed side-normal pair `10001/11110`. Insert it into the retained 33-tile
poison word. Its upper and lower spellings satisfy `V=U ++ 1000`, with lengths `113` and
`117`, so its four parameters obey the corrected terminal equations

```text
Y=81X+67,       τ=81σ.
```

Lean proves a uniform losing fork. For every pair of endpoint contexts and nonzero scales
satisfying the hypotheses of [`M4-C04`](#m4-c04-original-mixed-gap-endpoint-compiler), there is
a reduced word containing `(b,30)`, containing no singular `(b,1)`, whose two-wall exceptional
chain is zero. The same theorem proves that no lawful Neary terminal word exists for this source.

**Scope:** this refutes the four-parameter conditional endpoint architecture as a uniform
reduction. It does not decide reachability of its endpoint rays, classify every original-family
zero, or exclude an incidence carrying a checked certificate of lawful history.

**Use:** park `M4-C04`. If its endpoint contexts are unavailable, completeness fails; if they
are available, this pseudo-terminal breaks soundness. Continue only through the all-word
consecutive-incidence classification, or through a syntax-sensitive geometry or narrower
computable source image that cannot realize the poison.

**Artifact:**
[`MatrixMortality/ParabolicRetunedObstruction.lean`](MatrixMortality/ParabolicRetunedObstruction.lean)
and
[`audits/m43-original-semantic-obstruction-2026-08-10.md`](audits/m43-original-semantic-obstruction-2026-08-10.md).

### M4-O16: One-complement spectral-checksum obstruction

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

Retain the paired data matrices and let the unused one-dimensional complement of the cube root
carry a rational eigenvalue `q`. The compulsory identity `Ŝ³J=TJ` has exactly two branches:

```text
q=1:   z=2/3, x and y free;
q≠1:   x=y=0, z=(1+q³)/(q²+q+1).
```

In the nonresonant branch, every reduced `b`- and `c`-gap atom is invertible for every natural
gap. A full arbitrary-word factorization then gives rank three to every word containing a data
letter; pure root words are also nonzero. The three-generator family is immortal.

In the resonant branch, complete gaps lie on the affine erase--rule line. At
`j_k=(9^k-1)/8`, gap `3j_k` realizes the exact pseudo-production with lower word `1^(2k)0`.
The intended gaps `0` and `3` are followed by the gap-thirty poison already formalized in
[`M4-O15`](#m4-o15-original-pseudo-terminal-endpoint-obstruction).

**Scope:** rational roots retaining the paired order-three block and placing all new syntax in
its one-dimensional complement. This does not cover nontriangular roots, nonlinear projective
legality invariants, or another three-generator family. Multilinear interpolation is not used as
a generic no-go: forward completeness need not accept every Boolean assignment to one skeleton.

**Use:** do not revisit exponential gap checksums in the spare eigenvalue. `q≠1` destroys every
wall; `q=1` restores the affine pseudo-terminals.

**Artifact:**
[`audits/m43-spectral-checksum-obstruction-2026-08-11.md`](audits/m43-spectral-checksum-obstruction-2026-08-11.md).

### M4-O17: Positive Nielsen-basis obstruction

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

For the repository's fixed universal source, Carvalho's numbered transducer has period
`m=216b+2`, where `b≥1` is the cardinality of the fixed binary interpreter state type. Its
closed-path subgroup has index `m` in `F(0,1,H,p)` and rank

```text
3m+1=648b+7≥655.
```

It admits an explicit all-positive Nielsen basis. Nevertheless, every nonempty positive word on
that basis has binary-exponent character a positive multiple of `m`, while every element of the
Carvalho equalizer has character zero. The intersection of the positive basis monoid with the
equalizer is therefore only the identity, on both halting and nonhalting instances.

**Scope:** the natural positive Nielsen basis of the exact fixed-program closed-path subgroup.
This does not forbid a nonlinear positive compiler, boundary encoding, overlapping code, or a
different free-cancellation source.

**Use:** never supply the closed-path basis itself as semigroup generators. Positivity removes
every nontrivial halting witness even before generator-count compression.

**Artifact:**
[`audits/m43-free-group-punctuation-2026-08-11.md`](audits/m43-free-group-punctuation-2026-08-11.md)
and [`references/carvalho-2026-free-group-pcp.md`](references/carvalho-2026-free-group-pcp.md).

### M4-O08: Residue-two necessary wall

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Multiply every atom `Q(x,3j)` and `Q(x,3j+1)` by 64, then reduce the resulting integral matrix
modulo three. Independently of `x` and `j`, the two residues become

```text
Q₀ = [[1,2,2], [0,0,0], [0,0,0]],
Q₁ = [[0,0,0], [0,0,0], [2,0,2]].
```

Both preserve the two rays generated by `e₀,e₂` with nonzero weights: `Q₀` resets either ray to
`e₀`, and `Q₁` resets either to `e₂`. Every residue-{0,1} word therefore acts nontrivially on
`e₀`. Scalar extension proves that its rational atom product is nonzero.

**Scope:** every natural `β`, every body, every `j≥0`, both letters, arbitrary residue-zero and
residue-one mixtures, arbitrary exceptional count, and the empty word. The theorem excludes no
word containing `Q(x,3j+2)`.

**Use:** every parabolic zero contains a residue-two atom. A different regular residue-one atom
cannot repair the closed semantic boundary, even amid arbitrarily many other residue-zero and
residue-one atoms.

**Next:** use [`M4-S03`](#m4-s03-one-defect-phase-cut) and
[`M4-O09`](#m4-o09-one-coordinate-exterior-fracture) to classify the surviving alternating
phases in the complete exterior state, then extend or fracture that classification at successive
residue-two atoms.

**Artifact:** `ParabolicBlade.residueTwoWall_wordProduct_ne_zero` in
[`MatrixMortality/ParabolicResidueWall.lean`](MatrixMortality/ParabolicResidueWall.lean) and
[`audits/m43-residue-two-wall-2026-08-05.md`](audits/m43-residue-two-wall-2026-08-05.md).

### M4-S02: Residue-zero safe-bridge cone

**Kind:** structure theorem

**Evidence:** audited

**Disposition:** active

In triangle coordinates, bridge singularity is `u=0` and the empty bridge starts at
`(u,v,w)=(0,22,9)`. The cone

```text
u≤0,       v>w>0
```

is sent strictly into `u<0, v>w>0` by every residue-zero `b`- or `c`-atom. The proof uses the
exact transition rows and the uniform Neary inequalities `2M-L-5>0` and `3L-2M>0`. Induction
therefore gives

```text
W nonempty and every gap of W is 0 mod 3  →  det K(W)<0.
```

**Scope:** arbitrary letters, waits, word length, `β`, and encoded body, but only regular bridge
blocks containing residue-zero atoms. Residue-one atoms are not controlled. A companion
two-letter family approaches the singular wall to arbitrary `3`-adic precision, so finite local
digits cannot replace the Archimedean cone.

**Use:** any singular nonempty safe bridge contains a regular residue-one atom. Compress maximal
residue-zero runs and attack the resulting residue-one skeleton; do not revisit closed-only
bridge return or finite local valuation separation.

**Next:** use the residue-zero cone only as a local compression. The complete return proof must
carry exact arithmetic through arbitrary residue-one alternation; finite wall-separated cone
families are excluded by [`M4-O10`](#m4-o10-irrational-rotation-cone-fracture).

**Artifact:** [`audits/m43-safe-return-2026-08-06.md`](audits/m43-safe-return-2026-08-06.md).

### M4-S03: One-defect phase cut

**Kind:** structure theorem

**Evidence:** formalized

**Disposition:** graduated

After multiplying by 64 and reducing modulo three, every residue-two atom acts on
`span(e₀,e₂)` as

```text
A₂ = [[1,1], [2,1]].
```

The safe residue matrices have rank-one factorizations `Aᵢ=pᵢqᵢᵀ`. Their only local
one-defect scalar is

```text
phaseTable(i,k) = qᵢᵀ A₂ pₖ = [[2,0], [0,1]].
```

Hence a word with one residue-two atom and nonempty safe contexts is nonzero whenever the two
adjacent safe atoms have the same residue. If either context is empty, safe-word nonvanishing and
residue-two invertibility give the same conclusion. Only `0|2|1` and `1|2|0` survive.

**Scope:** arbitrary `β`, body, letters, waits, safe-context lengths, and exceptional-atom count,
but exactly one residue-two atom. The two alternating phases vanish modulo three; this proves
only divisibility there, not an exact zero.

**Use:** every exact one-defect zero has nonempty safe contexts whose adjacent residues are
opposite. The five-atom word `R²Q(b,3j+2)R²` is the `1|2|1` instance and needs no separate
theorem.

**Promotion:** subsumed by the complete arbitrary-run table
[`M4-S06`](#m4-s06-arbitrary-defect-bridge-grammar).

**Artifact:** `ParabolicBlade.oneDefect_wordProduct_ne_zero_of_same_residue` in
[`MatrixMortality/ParabolicResidueWall.lean`](MatrixMortality/ParabolicResidueWall.lean) and
[`audits/m43-one-defect-phase-2026-08-07.md`](audits/m43-one-defect-phase-2026-08-07.md).

### M4-O09: One-coordinate exterior fracture

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

In triangle coordinates, safe-bridge singularity is `u=0`. On the chart `v≠0`, the scalar

```text
s=(u+w)/v
```

closes on every residue-zero atom:

```text
b0: s ↦ s/(9ρ)−(ρ−1)/(6ρ),
c0: s ↦ s/3.
```

It also makes every regular residue-one `b` return wall wait-independent:

```text
u'=0  ↔  s=−2/(12ρ−1).
```

For a residue-one `c` atom, however, set `t=w/v`. Its candidate return wait has the form

```text
j = (a s+b+Δt)/(αs+M−3),
Δ = (11L−38Mρ+11M+114ρ−92)/16.
```

The Neary bounds `ρ≥1`, `M≥27`, and `L≤M−2` give

```text
16Δ ≤ (−38M+114)(ρ−1)−16M < 0.
```

Thus the `c1` return equation depends essentially on the second projective coordinate `t`; the
displayed scalar is not a closed state on the ambient chart. The same defect remains when the
denominator vanishes.

**Scope:** this rejects only the proposed scalar compression. It does not exclude an exact
invariant relation `t=φ(s)` on the reachable locus, another one-dimensional coordinate, a
two-dimensional projective invariant, or a finite multicone.

**Use:** do not extend the `s` recurrence or its inverse-phase reformulation without first proving
a reachable-locus closure theorem. Decide the `c1` quotient with both projective coordinates and
exact arithmetic; [`M4-O10`](#m4-o10-irrational-rotation-cone-fracture) excludes the former finite
wall-separated cone fallback.

**Next:** seek a reachable exact invariant or counterexample on the full projective state whose
arithmetic content distinguishes wall accumulation from wall incidence.

**Artifact:**
[`audits/m43-alternating-defect-literature-2026-08-07.md`](audits/m43-alternating-defect-literature-2026-08-07.md).

### M4-O10: Irrational-rotation cone fracture

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

Fix `β≥1`, put `ρ=3^β`, and let `G=Q(b,4)`, the legal regular safe label `(b,1,true)`. In triangle
coordinates its exterior action and empty state are

```text
Aρ = [[12−144ρ, −24, 12−144ρ],
      [315ρ,       0,      216ρ],
      [(297/2)ρ,   0,      108ρ]],
x₀ = (0,22,9)ᵀ.
```

For `Aρⁿx₀=(uₙ,vₙ,wₙ)ᵀ`, exact Cayley–Hamilton arithmetic gives

```text
uₙ=3ⁿaₙ,       aₙ∈ℤ,       aₙ≡1 (mod 3).
```

Thus every cyclic bridge `Gⁿ` is invertible. Over `ℝ`, however, `Aρ` has one positive eigenvalue
`α∈(0,8)` and a strictly dominant complex-conjugate pair `λ,λ̄`; `λ/λ̄` is not a root of unity.
The projective orbit is dense in the dominant invariant projective line, accumulates on `u=0`,
and has each sign of `u` infinitely often.

**Scope:** for every `β≥1`, this excludes any finite componentwise system of proper closed convex
cones invariant up to sign under `G`. It also excludes any finite strict Markov or closed
projective certificate for the complete safe system whose recurrent regions remain separated
from `u=0`. It does not exclude infinite cone families, non-strict regions whose closure meets the
wall, arithmetic partitions, hybrid real/`3`-adic invariants, safe returns outside this cyclic
language, or malformed zeros.

**Use:** the complete safe-return problem cannot be solved by a finite Archimedean separation
margin. Every replacement must distinguish irrational near returns from equality by exact
arithmetic, admit infinitely many geometric states, touch the wall non-strictly, or expose an
exact counterexample.

**Artifact:**
[`audits/m43-irrational-rotation-cone-fracture-2026-08-07.md`](audits/m43-irrational-rotation-cone-fracture-2026-08-07.md).

### M4-C02: Positive overlap-queue compiler

**Kind:** compiler

**Evidence:** formalized

**Disposition:** graduated

Fix a binary queue alphabet and two controller states. A trace consumes the current head `x`
and appends `produce(q,x)` at the open tail. For a nonempty initial queue `s`, use the two
positive frames

```text
z_rule = 0 :: s,       z_erase = []
```

and require the four local word identities

```text
z_q ++ produce(q,x) = cancel(q,x) ++ z_δ(q,x).
```

Lean proves that these identities telescope along every word. More importantly, positive-word
causality proves the arbitrary-word converse: if a nominal consumed word agrees with the queue
history, either it is a genuine trace or a genuine prefix has already emptied the queue. Under
the two semantic promises that every reachable empty queue is in `erase` and the initial
configuration never returns to its longer framed queue, reversal converts queue acceptance into
the exact suffix-controlled coefficient zero of [`M4-C01`](#m4-c01-two-state-pushout-compiler).
Consequently

```text
queue accepts  ↔  mortality of three integer 4 × 4 matrices.
```

**Scope:** the theorem fixes two states, two queue letters, three matrices, a nonempty mortality
witness, and all arbitrary physical words. The semantic promises are hypotheses on a source
family; the compiler neither decides them nor constructs an undecidable family satisfying them.

**Use:** this is now the shortest source-side route to `M₄(3)`. It supersedes vague requests for
an “open tail”: prove undecidability of the promised overlap-queue problem and instantiate the
checked theorem.

**Next:** construct a computable undecidable family satisfying the cocycle and both semantic
promises, necessarily with the deletion mechanism in [`M4-O11`](#m4-o11-pure-deletion-necessity),
or prove that the promised two-state binary model is decidable.

**Artifact:** `OverlapQueue.mortality_iff_accepts` in
[`MatrixMortality/OverlapQueue.lean`](MatrixMortality/OverlapQueue.lean) and
[`audits/m43-overlap-queue-2026-08-08.md`](audits/m43-overlap-queue-2026-08-08.md).

### M4-O11: Pure-deletion necessity

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Charge an ordinary queue by its length and an `erase`-state queue by one additional unit. Under
the positive frame cocycle, this potential cannot decrease if every state-preserving role emits
a nonempty production word. An accepted initial queue of length greater than one would then have
potential at least two but terminal potential one, a contradiction. Hence every such accepted
instance contains a role `(q,x)` with

```text
δ(q,x)=q,       produce(q,x)=[],       cancel(q,x)=[].
```

The last equality is forced by the frame cocycle, not assumed separately.

**Scope:** this is a necessity theorem for an accepted instance with nonempty initial queue of
length greater than one. It does not say that the pure-deletion role is reachable, classify
short instances, or prove decidability once such a role exists.

**Use:** reject every proposed positive overlap source that merely transfers complete state
frames and keeps all self-loops length-nondecreasing. A viable construction must spend one of
its four state-letter roles on genuine open-front deletion while the other roles reconstruct
enough computation to retain universality.

**Next:** classify the remaining four-role machines around the forced deleting self-loop. Either
embed an undecidable queue/tag system into that normal form or derive an effective finite or
semilinear reachability description.

**Artifact:** `OverlapQueue.pure_deletion_of_accepts_large` in
[`MatrixMortality/OverlapQueue.lean`](MatrixMortality/OverlapQueue.lean) and
[`audits/m43-overlap-queue-2026-08-08.md`](audits/m43-overlap-queue-2026-08-08.md).

### M4-S04: Arbitrary-switching three-adic exterior flag

**Kind:** structure theorem

**Evidence:** formalized

**Disposition:** active

The complete contragredient exterior state of a safe suffix is a vector `(u,v,w)`. Lean checks
an invertible triangle-coordinate change for which bridge singularity is exactly `u=0`, the
empty suffix is `(0,22,9)`, and physical left multiplication acts linearly even for singular
atoms. Define two sectors by

```text
C₀: ν₃(v) > min(ν₃(u),ν₃(w)),
C₁: ν₃(w) > min(ν₃(u),ν₃(v)),
C = C₀ ∪ C₁,
```

with zero treated as valuation infinity. For the actual nonempty Neary body, every regular safe
residue-zero atom sends `C` into `C₀`, and every regular safe residue-one atom sends `C` into
`C₁`. The proof recomputes the exact common power of three after every multiplication and
therefore survives arbitrary switching and arbitrarily deep cancellation. Induction gives the
flag for every regular safe word. For a nonempty word lying on `u=0`, its leftmost residue also
forces a strict orientation between `v` and `w`.

The first exposed wall equation is exact. A regular residue-one `b` atom with wait `j>0` hits
the wall precisely when

```text
(12·3^β−1)(u+w)+2v=0.
```

**Scope:** arbitrary regular safe words, all natural `β`, every nonempty encoded body, and all
legal waits. The exceptional residue-one `b` label with wait zero is excluded because it is the
singular atom, not a regular safe gap. The flag sectors themselves meet `u=0`; this theorem is
not safe return and does not control residue-two defects. Its state action is
`exteriorChange · adjugate(C)ᵀ · exteriorChangeInv`, not the primal action `C`. Exterior
invariants cannot be applied to primal endpoint equations without a separate intertwiner.

**Use:** arbitrary switching is no longer the unknown. Any safe wall hit must occur in one of
two oriented `3`-adic boundary sectors, and each leftmost atom supplies an explicit exact wound
functional. Continue with reachable-locus arithmetic, not a finite Archimedean cone or another
coarse valuation partition. In particular, the quadratic-conic claim for `C u*∼k` is invalid:
the regular primal atom `atom 3 bbcc b 0` sends `(0,0,1)ᵀ` from conic value zero to value
`24`.

**Next:** derive and compare the wall functionals for all four atom families under the oriented
flag, then prove their reachable avoidance or exhibit an exact safe returning word. In parallel,
feed the oriented contexts directly into the alternating one-defect and multiple-defect grammar.

**Artifact:** [`MatrixMortality/ParabolicExterior.lean`](MatrixMortality/ParabolicExterior.lean),
[`MatrixMortality/ParabolicFlag.lean`](MatrixMortality/ParabolicFlag.lean),
[`MatrixMortality/ParabolicSafeFlag.lean`](MatrixMortality/ParabolicSafeFlag.lean), and
[`audits/m43-parabolic-flag-2026-08-08.md`](audits/m43-parabolic-flag-2026-08-08.md).

### M4-S05: Deletion-scanner normal form

**Kind:** structure theorem

**Evidence:** audited

**Disposition:** graduated

Fix the pure-deletion self-loop forced by [`M4-O11`](#m4-o11-pure-deletion-necessity) and split
the other three controller roles. Absorbing rows reduce to a two-letter dependency graph;
unreachable accepting states and the `|s|=1` two-singleton orbit are decidable directly. Four
apparent scanners remain. A last-return argument using the compulsory suffix `A=0::s` and the
forbidden configuration `(rule,A)` eliminates the forward all-return scanner and forces unary
zero frames in the forward one-loop and backward all-entry scanners.

The promised source is therefore the union of three exact kernels:

```text
Lₙ: zero-framed binary context-2 Lag,
Bₙ: zero-framed reset scanning,
C:  a conjugate scanner with nonempty periodic rule production.
```

In `C` the rule self-loop equation `A ++ P = K ++ A` has exactly the conjugate form
`K=u++v`, `P=v++u`, `A=(u++v)^r++u`. The split is exhaustive over the two-by-two transition
table. [`M4-D01`](#m4-d01-zero-framed-binary-two-lag-decision) subsequently decides `Lₙ`,
[`M4-D02`](#m4-d02-zero-framed-reset-scanner-decision) decides `Bₙ`, and
[`M4-D03`](#m4-d03-periodic-conjugate-scanner-decision) decides `C`. The exhaustive source
class is closed.

**Scope:** promised binary two-state positive overlap queues. The transition classification and
the elementary decisions outside the three kernels have been independently audited but are not
one Lean declaration. `M4-D01` owns the formal decision of `Lₙ`; `M4-D02` and `M4-D03` own the
audited decisions of `Bₙ` and `C`.

**Use:** records why no universal source can inhabit the promised overlap-queue class compiled
by `M4-C02`. Any new source route must leave this exhaustive normal form rather than revive one
of its scanners.

**Next:** none inside this source class. Do not revisit `Lₙ`, `Bₙ`, `C`, or complete-frame
machines outside this normal form.

**Artifact:**
[`audits/m43-deletion-scanner-2026-08-08.md`](audits/m43-deletion-scanner-2026-08-08.md).

### M4-S06: Arbitrary defect bridge grammar

**Kind:** structure theorem

**Evidence:** formalized

**Disposition:** active

After the canonical integral clearing, every safe atom restricts to one of two rank-one matrices
and every residue-two atom restricts to

```text
A₂ = [[1,1],[2,1]],    A₂⁴ = 2I
```

on the protected plane. A maximal run of `m` defects between safe phases `i,k` has zero local
incidence exactly when

```text
m ≡ 1 (mod 4) and i ≠ k,
m ≡ 3 (mod 4) and i = k.
```

Lean factors every arbitrary skeleton into the product of these local incidences and proves the
same theorem for the full cleared `3 × 3` residues. It then consumes the reduction at the
physical level: a concrete rational safe/defect skeleton avoiding all bad runs is nonzero. This
subsumes the one-defect phase cut `M4-S03`.

A separate integral exterior lift proves that every nonempty pure-defect block induces an
invertible `2 × 2` bridge. For arbitrary regular blocks, bridge singularity is exactly the
exterior wall, every wall bridge is a nonzero outer product, and an arbitrary varying wall chain
vanishes exactly at one incidence between consecutive walls. Its explicit nonzero cokernel is
`(v,-4w)` for wall state `(0,v,w)`.

**Scope:** all natural `β`, every body, both letters, arbitrary waits, arbitrary safe/defect run
lengths, and arbitrarily many singular bridges. A bad residue skeleton is only a necessary
first-layer condition; it is not asserted to be a rational zero. The theorem does not identify
the surviving projective incidence with a semantic computation.

**Use:** every minimal parabolic zero now has exactly two singular endpoint bridges, only
invertible transport between them, and one zero projective incidence. Neither endpoint can be a
nonempty pure-defect block. Delete all extra walls and all defect-count casework before attacking
the remaining incidence.

**Next:** construct paired-Neary endpoint contexts and identify the resulting incidence in both
directions, or produce a malformed exact incidence. In parallel, decide whether nonsingular
mixed bridges can transport the oriented cokernel into the annihilating sector.

**Artifact:** [`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean) and
[`audits/m43-arbitrary-defect-2026-08-08.md`](audits/m43-arbitrary-defect-2026-08-08.md).

### M4-S07: One-sided wall-orbit normal form

**Kind:** structure theorem

**Evidence:** audited

**Disposition:** active

For a regular wall middle `M`, define the canonical right bridge kernel

```text
κρ(M)=coreLeftInverse(ρ) adj(M) (4,4,-1)ᵀ.
```

Lean proves that `κρ(M)` is nonzero and `Kρ(M)κρ(M)=0`. Together with the checked left
cokernel `λ(M)=(v(M),-4w(M))`, every pair of wall endpoints and invertible bridge transport
satisfies

```text
Kρ(U) T Kρ(V)=0  ↔  λ(V) adj(T) κρ(U)=0.
```

More sharply, if `U` is a wall and `adj(T)κρ(U)=(a,b)≠0`, then for every regular `V`

```text
Kρ(U) T Kρ(V)=0  ↔  exteriorState(V) ∼ (0,4b,a).
```

The target ray itself forces `V` to be a wall. Combined with `M4-S06`, this is an exact
arbitrary-literal-word criterion for mortality of the pinned parabolic family.

**Scope:** the original parabolic root, every positive source width, nonempty body, arbitrary
regular endpoint words, and transports generated by invertible regular bridges. This is a normal
form, not an avoidance theorem: no claim is made that the target ray is unreachable.

**Use:** replace the former pair-of-wall-languages problem by exterior collision avoidance.
Enumerating right walls or choosing outer-product gauges is no longer frontier work.

**Next:** prove uniform avoidance using the oriented `3`-adic flag and defect grammar, or produce
one exact orbit hit and expand it to a physical zero word.

**Artifact:**
[`MatrixMortality/ParabolicIncidence.lean`](MatrixMortality/ParabolicIncidence.lean) and
[`audits/m43-one-sided-wall-orbit-2026-08-11.md`](audits/m43-one-sided-wall-orbit-2026-08-11.md).

### M4-S08: Safe-wall transport chamber

**Kind:** structure theorem

**Evidence:** formalized

**Disposition:** active

Let a nonempty regular safe right wall have exterior state `(0,v,w)`, let the nonzero
transported left kernel be `ξ=(a,b)`, and suppose their consecutive incidence vanishes. Since
the wall cokernel is `(v,-4w)`, the incidence is

```text
v a = 4 w b.
```

The safe flag now constrains the transported kernel, not merely the wall. If the wall's
leftmost gap has residue zero, then `ν₃(w)<ν₃(v)` and the equation forces
`ν₃(a)<ν₃(b)`. If it has residue one, then `ν₃(v)<ν₃(w)` and the equation forces
`ν₃(b)<ν₃(a)`. The theorem includes the cases where the higher-valuation coordinate is zero.
Consequently a transported kernel whose two coordinates are nonzero and have equal valuation
cannot close against any nonempty safe wall.

**Scope:** every natural `β`, every nonempty body, every nonempty regular safe right-wall word,
and every nonzero rational transport vector. The theorem does not assert that safe walls exist,
constrain right walls containing residue-two defects, or classify which bridge transports
produce the required strict chamber.

**Use:** replace an unstructured scalar incidence against a safe right wall by a strict,
phase-indexed transport obligation. Balanced transport is excluded immediately. The surviving
parabolic search should classify transported kernels only across the bad defect skeletons from
`M4-S06` and test whether they can enter the chamber selected here.

**Next:** derive the adjugate transport action on the two bad run classes
`m≡1 (mod 4), i≠k` and `m≡3 (mod 4), i=k`; prove chamber avoidance or extract an exact orbit
hit.

**Artifact:**
[`MatrixMortality/ParabolicIncidence.lean`](MatrixMortality/ParabolicIncidence.lean) and
[`audits/m43-safe-wall-transport-2026-08-30.md`](audits/m43-safe-wall-transport-2026-08-30.md).

### M4-S09: Minimal all-b bad-run exclusion

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

The shortest bad skeleton left by `M4-S06` is one residue-two atom between opposite safe phases.
For all-`b` atoms its two orientations are

```text
b(3z) b(3x+2) b(3y+1),    b(3z+1) b(3x+2) b(3y).
```

Lean computes their bridge determinants exactly. The first is

```text
(81/2) ρ y P₀(ρ,x,z),
```

where `P₀` is strictly positive for `ρ≥1` and nonnegative waits. The second is

```text
−243 ρ z P₁(ρ,x,y),
```

where `P₁` is strictly positive for `ρ≥9`. Regularity forces `y>0` in the first orientation and
`z>0` in the second, because the excluded zero wait would be the exceptional singular atom.
Thus neither orientation can be a wall at the universal-source scale `ρ=3^β`, `β≥2`, in
particular at `β=3`.

**Scope:** exactly three atoms, one residue-two atom, both safe phases, and letter `b` at both
endpoints and at the defect. `M4-S14` now strictly subsumes this scope, including the same exact
regularity boundary, for every finite residue-two run at deletion width three.

**Use:** the smallest bad skeleton is no longer merely a modulo-three survivor. Any minimal
one-defect wall must use the body-dependent `c` atom or a nontrivial safe context. The positive
factorization also supplies the characteristic-zero sign template for the longer-run attack.

**Next:** none within the all-`b` run. The live alphabet extensions use a `c` defect or endpoint.

**Artifact:**
[`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean) and
[`audits/m43-minimal-all-b-bad-run-2026-08-30.md`](audits/m43-minimal-all-b-bad-run-2026-08-30.md).

### M4-S10: Phase-zero c-defect exclusion

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** active

Replace the middle atom in the shortest `0|2|1` bad run by the body-dependent `c` atom while
retaining `b` endpoints:

```text
b(3z) c(3x+2) b(3y+1).
```

At deletion width three, Lean computes the exact bridge determinant as `729y/16` times a
polynomial in `x,z` with monomials `xz,x,z,1`. Every coefficient is strictly positive for every
nonempty body. The proof uses only the native code bounds

```text
27 < L_c^{scale},    0 ≤ L_c < L_c^{scale},
```

then checks the four exact coefficients. Regularity forces `y>0`, so the determinant is positive
for every pair of nonnegative waits `x,z`.

**Scope:** deletion width `β=3`, arbitrary nonempty body, exactly three atoms, `b` safe endpoints,
a `c` defect, and orientation `0|2|1`. The coefficientwise argument does not transpose to the
mixed-sign `1|2|0` determinant; `M4-S11` excludes that orientation by a separate cylinder proof.

That opposite determinant is nevertheless formalized at its compressed endpoint. With
`L=nearySideLowerC 3 body`, `M=nearySideLowerCScale 3 body`, it is `−4374z` times

```text
1699776(M−3)(8y+1)x − B_y y − B₀,
```

where

```text
B_y = 1316002776L−442700696M−28695312,
B₀  = 164500347L−55585393M−2843496,
B_y−8B₀ = 1982448(M−3).
```

Thus the surviving phase is one exact two-endpoint interval problem, not an uncontrolled mixed
polynomial.

**Use:** together with `M4-S11`, no shortest bad run with `b` endpoints survives when the defect
is `c`.

**Next:** allow a `c` endpoint or lift the defect run from length one to its four-periodic longer
classes.

**Artifact:**
[`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean) and
[`audits/m43-phase-zero-c-defect-2026-08-30.md`](audits/m43-phase-zero-c-defect-2026-08-30.md).

### M4-S11: Opposite c-defect cylinder exclusion

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** active

The opposite shortest bad run with `b` endpoints is

```text
b(3z+1) c(3x+2) b(3y).
```

Put `L=nearySideLowerC 3 body`, `M=nearySideLowerCScale 3 body`,

```text
A  = 1699776(M−3),
B₀ = 164500347L−55585393M−2843496,
B₁ = B₀+247806(M−3).
```

After removing the regular factor `−4374z`, the determinant is

```text
A(8y+1)x − 8B₁y − B₀.
```

A zero would make `x` the weighted average of `B₀/A` and `B₁/A`. Their separation is the
body-independent width `1059/7264<1`. Every nonempty body is either all `c` or has the form
`c^k b tail`. Exact ternary-code bounds place both roots between consecutive integers for
`k=1`, `k=2`, `k≥4`, and the all-`c` case. For `k=0` and `k=3`, only `x=59` and `x=64`
respectively remain; the same cleared inequalities force `y<1`, and `y=0` contradicts the
strict lower root bound. Hence the determinant never vanishes.

**Scope:** deletion width `β=3`, arbitrary nonempty body, exactly three atoms, `b` safe
endpoints, a `c` defect, and orientation `1|2|0`. The theorem does not cover a `c` endpoint,
longer defect runs, or nontrivial safe endpoint contexts. Regularity requires `z>0`; `z=0` is the
exceptional singular `b(1)` endpoint.

**Use:** `M4-S10` and `M4-S11` eliminate both shortest bad-run orientations with a `c` defect and
`b` endpoints. A surviving shortest run must therefore put body dependence at an endpoint or in
more than one atom.

**Next:** finish the sole one-`c`-endpoint survivor with a `b` defect, then treat multiple `c`
atoms and lift run length one through the residue-two four-cycle.

**Artifact:**
[`MatrixMortality/ParabolicDefectCylinder.lean`](MatrixMortality/ParabolicDefectCylinder.lean)
and
[`audits/m43-opposite-c-defect-cylinder-2026-08-30.md`](audits/m43-opposite-c-defect-cylinder-2026-08-30.md).

### M4-S12: Residue-zero c-endpoint exclusion

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** active

At deletion width three, replace the residue-zero safe endpoint of either shortest all-`b` bad
run by the body-dependent `c` atom:

```text
c(3z) b(3x+2) b(3y+1),
b(3z+1) b(3x+2) c(3y).
```

Both exact bridge determinants factor as the regular residue-one `b` wait, times a polynomial
whose four wait-monomial coefficients are strictly positive. The native nonempty-code inequality

```text
0 < 11L−9M−32 < 16(M−3)
```

proves every body-dependent coefficient positive without a body split. Hence neither orientation
can close for any nonempty body and nonnegative remaining waits.

**Scope:** deletion width `β=3`, exactly three atoms, a `b` defect, exactly one `c` endpoint, and
that endpoint in residue-zero phase. The residue-one `c` endpoint, a `c` defect together with a
`c` endpoint, longer defect runs, and nontrivial safe endpoint contexts remain open. Regularity
requires `y>0` in the first orientation and `z>0` in the second; the excluded zero wait is the
exceptional singular `b(1)` endpoint.

**Use:** body dependence at a residue-zero endpoint does not create a new shortest-run wall. For
a `b` defect and exactly one `c` endpoint, only the two placements of `c` in residue-one phase
remain.

**Next:** settle the two residue-one `c` endpoint determinants, then allow a `c` defect at the
same time as a `c` endpoint. Lift run length one to `1+4k` only after the three-atom endpoint
alphabet is closed.

**Artifact:**
[`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean) and
[`audits/m43-residue-zero-c-endpoints-2026-08-30.md`](audits/m43-residue-zero-c-endpoints-2026-08-30.md).

### M4-S13: Residue-one left c-endpoint exclusion

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** active

At deletion width three, the shortest `1|2|0` bad run with a `c` left endpoint and `b` defect is

```text
c(3z+1) b(3x+2) b(3y).
```

Its exact bridge determinant is a polynomial in the eight monomials
`xyz,xy,xz,x,yz,y,z,1`. Every coefficient is strictly positive for an arbitrary nonempty body;
the proof needs only `27<M` and `0≤L<M`. Hence the determinant is positive for all nonnegative
waits, without an exceptional endpoint case.

**Scope:** deletion width `β=3`, exactly three atoms, a `b` defect, a residue-one `c` left
endpoint, and a residue-zero `b` right endpoint. It does not cover the transposed
`b(3z)b(3x+2)c(3y+1)` placement, a `c` defect together with a `c` endpoint, a longer defect run,
or a nontrivial safe context.

**Use:** together with `M4-S12`, three of the four placements with a `b` defect and exactly one
`c` endpoint are excluded. Only the residue-one right endpoint in the `0|2|1` orientation
survives.

**Next:** compress the remaining `b(3z)b(3x+2)c(3y+1)` mixed-sign determinant before introducing
a second body-dependent atom.

**Artifact:**
[`MatrixMortality/ParabolicDefect.lean`](MatrixMortality/ParabolicDefect.lean) and
[`audits/m43-residue-one-left-c-endpoint-2026-08-30.md`](audits/m43-residue-one-left-c-endpoint-2026-08-30.md).

### M4-S14: Uniform all-b defect-run exclusion

**Kind:** structure theorem and obstruction

**Evidence:** formalized

**Disposition:** active

At deletion width three, let `Bε(j)` be the residue-zero (`ε=false`) or residue-one
(`ε=true`) safe `b` atom, and let `D(j)=b(3j+2)`. For arbitrary endpoint phases and every finite
wait list `w`, Lean proves

```text
det bridge(27, Bε(z) · D(w₀) ··· D(wₙ₋₁) · Bδ(y)) ≠ 0
```

whenever both endpoints are regular. The only excluded endpoint is `b(1)`, represented by the
residue-one phase with zero wait. No parity or nonemptiness hypothesis is required.

The proof conjugates the adjugate-transpose defect action by `S=diag(1,−1,−1)`. After removing
one global minus sign per defect, every wait acts through an explicit matrix preserving the cone

```text
0 < x,    x ≤ 2y,    7y ≤ 6x,    x ≤ z.
```

Both regular right safe endpoints enter this cone. The signed left bridge covector is strictly
negative in residue-zero phase and strictly positive in residue-one phase. A run of length `n`
therefore changes only the global factor `(−1)^n`; it cannot create a zero.

**Scope:** arbitrary finite runs consisting entirely of residue-two `b` atoms between single
regular safe `b` endpoints, exactly at `β=3`. This includes every all-`b` bad run of lengths
`1+4k` and `3+4k`, as well as even and empty runs. It does not allow a body-dependent `c` atom
inside the defect run or either endpoint, or a multi-atom safe endpoint context.

**Use:** all-`b` defect-run length has disappeared from the `M₄(3)` frontier. The former exact
one-defect result `M4-S09` and the explicit three-defect coefficient expansion are subsumed; the
latter has been deleted. Every surviving bad bridge family must contain a `c` atom or a
nontrivial safe context.

**Next:** classify the shortest bad bridges containing `c`, then seek a cone or cylinder
transport that tolerates `c` inside longer runs.

**Artifact:**
[`MatrixMortality/ParabolicLongDefect.lean`](MatrixMortality/ParabolicLongDefect.lean) and
[`audits/m43-uniform-all-b-defect-run-2026-08-30.md`](audits/m43-uniform-all-b-defect-run-2026-08-30.md).

### M4-S15: Opposite double-c endpoint exclusion

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** active

The shortest `1|2|0` bad bridge with a `b` defect and body-dependent `c` atoms at both safe
endpoints is

```text
c(3z+1) b(3x+2) c(3y).
```

Put `D=M−3` and `q=11L−9M−32`. Lean collects its determinant as `729/704` times a polynomial
in `xyz,xy,xz,x,yz,y,z,1`. Seven coefficients are immediately positive from

```text
24 < D,    0 < q < 16D.
```

The `xyz` and `xz` coefficients share the positive throat
`84797D−2991q−143568`. The sole quadratic competition occurs in the `yz` coefficient; multiplying
`q<16D` by `q>0` absorbs its negative `2871240q²` term, and `D>24` absorbs the remaining negative
linear and constant terms. Hence the determinant is strictly positive for every nonempty body
and all nonnegative waits.

**Scope:** deletion width `β=3`, exactly three atoms, a residue-one `c` left endpoint, one `b`
defect, and a residue-zero `c` right endpoint. It does not cover the transposed double-`c`
endpoint orientation, a `c` defect, longer defect runs, or multi-atom safe contexts.

**Use:** the `1|2|0` shortest family with a `b` defect is closed whenever its two endpoints are
both body-dependent. Every surviving shortest `1|2|0` bridge now has a `c` defect and at least
one `c` endpoint.

**Next:** kill the transposed `c(3z)b(3x+2)c(3y+1)` bridge, then the six families combining a
`c` defect with one or two `c` endpoints.

**Artifact:**
[`MatrixMortality/ParabolicMixedEndpoint.lean`](MatrixMortality/ParabolicMixedEndpoint.lean) and
[`audits/m43-opposite-double-c-endpoint-2026-08-30.md`](audits/m43-opposite-double-c-endpoint-2026-08-30.md).

### M4-C03: Zero-framed binary two-Lag compiler

**Kind:** compiler

**Evidence:** formalized

**Disposition:** graduated

For `n>0` and arbitrary binary appendants `U,V,W`, prefix the queue phase as a bit. The scanner

```text
λ(00)=V,  λ(01)=W0ⁿ⁺¹,  λ(10)=U,  λ(11)=ε
```

then performs the literal context-two Lag step `qxZ ↦ xZλ(qx)`. Lean proves both directions of
the chronological trace equivalence. It also proves that empty-state isolation is exactly
isolation of the reachable singleton `0` and that the framed-return promise forbids `10ⁿ⁺¹`
from the initial word `10ⁿ`. Under these promises,

```text
singleton 0 is reachable  ↔  mortality of three integer 4 × 4 matrices.
```

**Scope:** arbitrary positive words and malformed Lag histories are included through the parent
queue compiler. Universality of this constrained four-rule Lag class is not asserted.

**Use:** an undecidability proof for this exact binary Lag problem now instantiates `M₄(3)`
without further matrix engineering.

**Artifact:** `OverlapLag.mortality_iff_accepts` in
[`MatrixMortality/OverlapLag.lean`](MatrixMortality/OverlapLag.lean) and
[`audits/m43-deletion-scanner-2026-08-08.md`](audits/m43-deletion-scanner-2026-08-08.md).

### M4-D01: Zero-framed binary two-Lag decision

**Kind:** decidable stratum

**Evidence:** formalized

**Disposition:** graduated

For `n>0`, the unrestricted scanner in `M4-C03` accepts exactly when

```text
(n=1 and U=ε) or (V=ε and U∈0*).
```

Every accepting trace has last predecessor `10` or `00`. The full backward cone of `10` is
`1ᵏ0`, while a `1` in `U` is forward invariant and excludes `00`. The two displayed conditions
give explicit all-zero traces. Neither compiler promise enters the classification.

**Scope:** all binary `U,V,W`, every positive `n`, every malformed intermediate word, and the
chronological tail-appending convention of `M4-C03`. The theorem classifies source acceptance;
its matrix corollary retains the compiler's singleton-isolation and framed-return hypotheses.

**Use:** deletes `Lₙ` from the source frontier. No universality attack on this Lag subclass
survives.

**Artifact:** `OverlapLag.accepts_iff`, `OverlapLag.acceptsDecidable`, and
`OverlapLag.mortality_iff_syntax` in
[`MatrixMortality/OverlapLagDecision.lean`](MatrixMortality/OverlapLagDecision.lean), with audit
[`audits/m43-overlap-lag-decision-2026-08-10.md`](audits/m43-overlap-lag-decision-2026-08-10.md).

### M4-D02: Zero-framed reset scanner decision

**Kind:** decidable stratum

**Evidence:** audited

**Disposition:** graduated

Let `U₀=0ʳ1V` when `U₀` is not all-zero, and let `zr` contract every nonempty zero-run to
one zero. The unrestricted reset scanner accepts exactly when

```text
U₀∈0*
or
(U₁∈0* and
  if W contains 1 then zr(VW0)=10
  else zr(VW0)∈(101|11)*10).
```

After the first return, every rule boundary ends in zero. The quotient code `a↦01`, `b↦1`
turns its complete boundary dynamics into

```text
ε ↦ S,     aX ↦ XaS,     bcX ↦ XQ,     b ↦ accept.
```

If `W` contains `1`, both appendants begin in `a`, so only the initial token `S=b` accepts. If
`W∈0*`, then `Q=ε`; the token monoid partitions into `(bΣ)*b`, `(bΣ)*`, and words with an
`a` in an odd position. The first class reaches `b`, the second cycles through `ε`, and the
third is invariant. Translating `(bΣ)*b` back gives `(101|11)*10`.

**Scope:** every positive frame length and arbitrary binary `U₀,U₁,W`; neither compiler
promise is used. The result is independently reconstructed but not Lean-formalized. It does not
classify reset scanners outside `M4-S05`.

**Use:** deletes `Bₙ` from the source frontier. `M4-D03` subsequently closes the remaining
periodic-conjugate scanner `C`.

**Artifact:**
[`audits/m43-reset-scanner-decision-2026-08-10.md`](audits/m43-reset-scanner-decision-2026-08-10.md).

### M4-D03: Periodic-conjugate scanner decision

**Kind:** decidable stratum

**Evidence:** audited

**Disposition:** graduated

Let `A=0s`, with `s` nonempty, and let nonempty `P` obey `AP=KA`. The periodic-conjugate
scanner is decidable on every instance promised to avoid `(R,A)`. Its initial rule phase is
computed directly. If that phase returns, promised acceptance forces

```text
a=c=0,    A∈0⁺,    U∈0*,    W∈0*.
```

Put `p=#₁(K)`. The scanner rejects when `p=0` or `p` is even. For odd `p`, let `γᵣ` be the
zero-gap preceding the `r`th `1` of `K²`, set `t₁=γ₁−1` and `tᵢ=γ_(2i−1)` for `2≤i≤p`, and
put `Tᵢ=t₁+⋯+tᵢ`. It accepts exactly when `pTᵢ=2i−1` for some `i≤p`.

The proof normalizes every conjugacy as `K=qᵈ`, `q=xy`, `P=(yx)ᵈ`, `A=qʳx`. A prefix telescope
handles self-consumed production without block assumptions. Its counter
`Δᵢ=pTᵢ−(2i−1)` counts the ones left on entry to erase state. The first `p` odd gaps exhaust
the cyclic phases of `K`; thereafter every full phase block adds at least `#₀(K)−2≥0`, plus
nonnegative unary spacers, so a later first acceptance is impossible.

**Scope:** all finite binary parameters satisfying the conjugacy equation and the exact
`M4-S05` promises. Avoidance of `(R,A)` is essential; unlike `M4-D01` and `M4-D02`, this is not
an unconditional scanner theorem. The result is independently reconstructed but not
Lean-formalized.

**Use:** deletes `C`, the final kernel of `M4-S05`. The positive overlap-queue source trunk is
closed; `M₄(3)` now lives on the parabolic matrix trunk.

**Artifact:**
[`audits/m43-periodic-conjugate-decision-2026-08-10.md`](audits/m43-periodic-conjugate-decision-2026-08-10.md).

### M4-O12: Terminal-frame morphism obstruction

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

If a source initial word is `Jb`, no fixed monoid morphism `h` can map the shared terminal `b`
to the compulsory return frame `0h(Jb)`. Lengths would give
`|h(b)|=1+|h(J)|+|h(b)|`. The Lean theorem is alphabet-generic.

**Scope:** fixed letterwise morphisms identifying the same terminal with the entire return
frame. Overlapping, stateful, history-dependent, or nonliteral simulations remain possible.

**Use:** kills the direct Neary-to-scanner morphism. Any surviving reduction must exploit the
queue overlap itself or change source.

**Artifact:** `OverlapLag.terminal_image_ne_frame` in
[`MatrixMortality/OverlapLag.lean`](MatrixMortality/OverlapLag.lean).

### G3-O01: Four-role macro irreducibility

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

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
source. [`G3-O08`](#g3-o08-erasing-and-stationary-closed-block-obstruction) subsequently removes
erasure and one precise closed-overlap class.

**Use:** reject every proposal to merge or macro-expand the present four roles unless it
explicitly invokes one of the escape mechanisms outside the scope.

**Artifact:** `MatrixMortality.ExactNearyMacroFactorization.four_le_card` in
[`MacroIrreducibility.lean`](MatrixMortality/MacroIrreducibility.lean). The structure
`ExactNearyMacroFactorization` quantifies over arbitrary macro words and does not assume an
injective role code, prefix code, or equal macro lengths.

### G3-O08: Erasing and stationary closed-block obstruction

**Kind:** obstruction

**Evidence:** audited; formalized core

**Disposition:** graduated

For each Neary role pair, record the four additive channels

```text
(upper ones, upper zeros, lower ones, lower zeros).
```

In the order `R_c,R_b,D_b,D_c`, their matrix is

```text
[[1,0,2+2μ+ν,1+βμ],
 [2,β,2,1],
 [2,β,0,1],
 [1,0,0,1]],
```

where `μ=|q|_b` and `ν=|q|_c`. Its determinant is `2β²μ`. Lean proves the stronger operational
fact directly: the associated rational linear map is injective whenever `β>0` and `μ>0`.
Every exact factorization through fixed physical macros factors this map through one dimension
per physical letter. Consequently at least four letters are necessary even when both target
morphisms erase, codewords are empty or coincident, and parsing is nonunique.

The complete paper argument permits more overlap. Fix spellings `ρ_b,ρ_c,δ_b,δ_c`, arbitrary
possibly erasing target morphisms, and arbitrary upper and lower residual words. Require only
that every block comprising one rule and `β−1` deletions return to the same two residuals while
emitting the correct complete binary pair. For `β≥4` and a body containing both `b` and `c`, no
three-letter system satisfies these identities. After taking Parikh vectors, nonnegativity leaves
two cases for the common lower deletion image and two cases for the upper residual shift. Lean
checks those discrete reductions; the ensuing one-dimensional-kernel contradictions and the
nonempty-deletion word argument are independently audited.

The checked universal Neary family has `β=10p≥10` and mixed bodies, so the closed-block theorem
applies throughout that family.

**Scope:** fixed physical spellings which concatenate by semantic role and return to one common
residual after each complete deletion-width block. The theorem does not cover state-dependent
spellings, an open residual which persists between blocks, genuinely nonfactorial adjacent-role
codes, or a target recoding that preserves only global solvability.

**Use:** reject every further attempt to save a local four-to-three role code by permitting
erasure, unequal or empty macro words, fixed boundary fragments, or a finite overlap which closes
at each Neary block. Demand an explicit state transition or an unclosed residue.

**Artifact:** [`TernaryClosedBlockNoGo.lean`](MatrixMortality/TernaryClosedBlockNoGo.lean) and
[`m34-ternary-closed-block-no-go-2026-08-08.md`](audits/m34-ternary-closed-block-no-go-2026-08-08.md).

The former next step is discharged by `G3-O13`: every rational exact state-dependent spelling
with recurrent block powers synchronizes to a forbidden stationary return.

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

### G3-O02: Rational phase fracture

**Kind:** obstruction

**Evidence:** audited

**Disposition:** stock

Fix an admissible paired instance with a nonempty zero language. Let the checked four-state
suffix column lie in one of the two embedded phase planes, and write its local projective point
as `[v_y]∈P²(ℚ)`. There is no three-state same-zero realization whose compressed suffix point is

```text
[H_yγ] = Φ_P([v_y])
```

for rational maps `Φ_rule,Φ_erase : P² ⇢ P²` defined at every reachable point. The target
generators may be singular, and either phase image may be a point, a line, or a nonlinear curve.

The erase orbit is Zariski dense. Equivariance therefore holds as a rational identity. A
non-line image makes the data generators invertible on the image; comparing the rule/erase
discrepancies yields invariance under one nontrivial private scaling, while erase-`c` mixes that
private direction back into the surviving coordinate. This forces a constant image. On a line,
two exact commutators act as one constant and one radial translation in the accumulator; rational
two-translation rigidity forces the line map to forget that accumulator. In every branch,

```text
Φ_erase ∘ E_c = Φ_erase.
```

If the original series has a zero, a toggle first normalizes its suffix phase to erase without
changing the coefficient. Prefixing `c` then emits erase-`c`; its upper and lower binary words
begin with different symbols, so the prefixed coefficient is nonzero. Projective invariance
would preserve target vanishing, contradicting the same-zero hypothesis.

**Scope:** the compressed suffix point must be rationally determined by the checked phase and
local suffix point. The theorem excludes linear projective gluings, rational gauges, Cremona
identifications, and rational collapses to curves or lines. It does not exclude a representation
that assigns different compressed points to words with the same checked suffix point. Such a
survivor has a genuinely multivalued phase graph closure or positive-dimensional generic fibers.

**Use:** cull every phase-plane identification that is merely a rational function of the present
paired state. [`G3-O03`](#g3-o03-history-sensitive-minimal-body-fracture) realizes the excluded
history-sensitive escape and moves the live boundary to uniform computability.

**Formalized core:** [`PhaseFracture.lean`](MatrixMortality/PhaseFracture.lean) checks phase
normalization, erase-`c` nonvanishing, and the dimension-free final contradiction.
[`PhaseRigidity.lean`](MatrixMortality/PhaseRigidity.lean) checks every displayed role matrix,
scale, discrepancy, commutator, mixing coefficient, and the invariant-pencil rigidity step in the
linear-fractional line branch. The density and arbitrary-rational function-field steps remain
audited rather than kernel-checked.

**Artifact:**
[`audits/m34-rational-phase-fracture-2026-08-06.md`](audits/m34-rational-phase-fracture-2026-08-06.md).

### G3-O03: History-sensitive minimal-body fracture

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

The report claiming uniqueness of the terminal role word for every admissible mortal paired
instance is false. At deletion width three and body `bcbb`, the distinct words

```text
R_c E_b E_c R_b E_b E_b
R_c E_b E_c R_b E_b E_b R_b E_b E_b R_c E_b E_b
```

both satisfy the complete terminal equation. The second appends a nonexecuted two-stroke null
history after the lawful computation has already reached a short queue. Determinism of `TagStep`
does not imply uniqueness of global history certificates.

On the infinite minimum-body subclass

```text
2 < β,    body.length = β−1,
```

the null-history defect is impossible. Every terminal match is exactly

```text
ω(body) = R_c :: body.map E.
```

Assign the four roles digits `1,2,3,4` in base five. Three integral control matrices maintain

```text
(κ(decodePairedWord y), phaseSign(y), 1)ᵀ
```

for every arbitrary paired-control word. The row `(1,0,−κ(ω))` therefore vanishes exactly on the
paired zero language. Adjoining its outer-product separator gives four `3 × 3` integral matrices;
the unconditional rank-one separator theorem proves the arbitrary-product mortality converse
directly, without rescaling the singular data controls. For `β=3`, body `bb`, the target code is
`92` and `ctbbt` is an explicit zero witness.

The associated phase graph closures are independently audited as

```text
P² × ℓ_rule,    P² × ℓ_erase.
```

Their generic fibers are lines. Thus no theorem can force every history-sensitive three-state
phase graph to be generically single-valued.

**Scope:** exact same-zero representation and mortality are formalized only for minimum-length
bodies. The full-product graph calculation is audited, not Lean-checked. Arbitrary admissible
bodies can have several terminal words, and no source-computable parameter selecting all of them
is supplied. This is not an undecidability reduction and does not settle `M₃(4)`.

**Use:** close instancewise phase-graph exclusion and generic-single-valuedness as routes to the
master problem. The rank-two data maps also show that singularity can erase the entering phase
without colliding decoded positive histories; rank drop alone cannot force inverse saturation.
The paired route now requires a uniform computable three-state recognizer for all terminal
histories, or a no-go for a precisely delimited uniform compiler class.

**Artifact:** [`HistoryFracture.lean`](MatrixMortality/HistoryFracture.lean), including
`NullHistoryCounterexample.terminal_word_not_unique`, `minimalBody_terminal_word_unique`,
`minimalBody_history_zero_iff_paired_zero`, and
`historyMortalityFamily_int_mortal_iff_zero`; bounded audit in
[`m34-history-fracture-2026-08-06.md`](audits/m34-history-fracture-2026-08-06.md), with the
unconditional separator strengthening in
[`m34-unconditional-separator-2026-08-07.md`](audits/m34-unconditional-separator-2026-08-07.md).

### G3-O04: Expanding affine-history no-go

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

Let a history machine carry one integral coordinate `X` and finitely many modes. Each transition
either preserves `X` or has the form

```text
(q,X) ↦ (q′,rX+D),    |r|≥2.
```

For a bound `N` containing every translation and target coordinate, a reverse data step obeys

```text
2|X| ≤ |r||X| = |Y−D| ≤ |Y|+|D| ≤ 2N.
```

Every predecessor of the target therefore lies in the finite box `Q×{−N,…,N}`. Lean constructs
an exact caged DFA: a transition leaving the box enters a dead state, while every accepted run
stays in the box because each intermediate state can still reach the target. The bounded-target
language is regular even when collisions and cycles produce infinitely many terminal histories.

This contains every effectively normalized reset-affine three-state compiler with
source-dependent signed integer radices, rational phase digits after denominator clearing,
arbitrary finite phase charts, and finitely many affine target fibers. The `u=0` row degeneracy is
a two-phase test. On a nonempty same-zero source, a zero and its leading toggle force the phase
coefficient to vanish without implying history uniqueness.

The fixed universal family satisfies

```text
∃y, pairedCoefficient ℚ source.width (source.body e) y = 0
  ↔ CodeHalts(e).
```

Hence no computable predicate, and therefore no total compiler with the finite reverse-search
normalization above, has exactly these sourcewise zero answers.

**Scope:** the finite-mode theorem requires one shared affine coordinate with stationary or
expanding integral transitions. It does not cover arbitrary rational reparameterizations between
curves, a genuinely two-dimensional projective orbit, infinite target sections, nonexpanding
translations, denominator-generating dynamics, or singular ideals without such a normalization.
The report's broader “finitely many rational curves” wording is rejected outside this explicit
law.

**Use:** cull every proposed replacement of the missing accumulator by a source-dependent radix,
one phase bit or finitely many charts, and finitely many target codes. The next paired-route attack
must exploit one of the stated escape mechanisms rather than alter digits, radix, collisions, or
conjugacy.

**Formalized core:** [`ExpandingHistoryNoGo.lean`](MatrixMortality/ExpandingHistoryNoGo.lean)
checks the all-word orbit formula, toggle rigidity, phase-only degeneracy, reverse bound, finite
reverse orbit, exact caged DFA, regularity, universal paired-zero equivalence, and the
computability contradiction. Whole target charts have their own checked finite-mode automaton.
Extracting mathlib `ComputablePred` code from an encoded rational
normalization certificate remains audited. The bounded reconstruction is
[`m34-expanding-history-no-go-2026-08-06.md`](audits/m34-expanding-history-no-go-2026-08-06.md).

### G3-O05: Cancellative projective state tax

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

For a paired control prefix `p`, suffix `s`, and the phase `q` entering from `s`, the terminal
equation is exactly

```text
A(p,q)=B(s),
A(p,q)=U(D_q(p))⁻¹L(D_q(p)),
B(s)=U(D(s))mL(D(s))⁻¹
```

in the binary free group. Assign every phase-tagged residual an injective rational code `θ`, put

```text
v(t)=(1,t,t²)ᵀ,       ℓ(a,b)=(ab,−(a+b),1),
```

and use `ℓ(a,b)v(t)=(t−a)(t−b)`. This gives one global three-coordinate factorization with exactly
the complete paired prefix-suffix zero support. Consequently every finite support submatrix has
rational rank at most three. A zero-language dimension lower bound must use common shift maps;
support/minrank alone cannot work.

The positive role pairs also contain

```text
(zx^β,1),       (z(zx^β)z⁻¹,1),
(1,z²),         (1,xz²x⁻¹).
```

The first two and last two freely generate `L_β` and `R`; their folded-core fiber product is a
tree, so `L_β∩R={1}`. Hence they yield a freely acting `F₂×F₂` discrepancy orbit.

If a projective recurrence extends every role to this two-sided group action and its target row
remains exact on every formal inverse state, role matrices become invertible on the reachable
span. The free discrepancy orbit then gives a faithful `F₂×F₂` action in `PGL_d(ℚ)`. No such
action exists for `d≤3`: opposite-factor lifts commute linearly because a projective commutator
scalar satisfies `μ³=1`, and the commutant of a faithful nonabelian subgroup of `GL₃` cannot
contain another faithful nonabelian free group.

**Scope:** the saturation hypothesis is essential. The theorem does not cover a positive-only
orbit whose inverse continuations are absent, whose target law fails there, or whose singular
maps destroy the group orbit. It does not prove general paired zero-language dimension four.

**Use:** cull projective cross-multiplication of independently cancellative upper and lower word
sides. Search must preserve genuinely one-way semigroup behavior. `G3-O11` proves that positive
common-shift equations alone do not supply inverse saturation, and
[`G3-O17`](#g3-o17-paired-inverse-chamber) proves that the paired grammar itself has no cofinal
positive inverse orbit. Only a representation-specific faithful Ore completion could now invoke
this tax.

**Formalized core:** [`CancellativeProjectiveNoGo.lean`](MatrixMortality/CancellativeProjectiveNoGo.lean)
checks the phase-aware decoder split, positive free-group embedding, terminal residual equation,
global conic factorization, every finite support-rank bound, role-fraction identities, and the
rational scalar-commutator law. The folded-graph, projective descent, and commutant classification
remain audited in
[`m34-cancellative-projective-no-go-2026-08-06.md`](audits/m34-cancellative-projective-no-go-2026-08-06.md).

### G3-O11: Positive shifts do not force saturation

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

There are explicit integral rank-two matrices `H_b,H_c,H_t∈M₃(ℤ)`, a column `γ`, and a row
`λ` such that

```text
λH_wγ=0 ↔ w=t
```

on the complete free monoid. Three selected reachable columns form the identity, and three
selected observable rows have determinant `−1`. No matrix word is zero. Nevertheless

```text
H_bγ=H_bH_tγ,        γ≠H_tγ.
```

Thus the positive `b`-shift collapses two distinct zero residuals and fails backward
cancellativity despite full reachability, observability, and arbitrary-word correctness.

The positive source can moreover be embedded in
`(⊕_{i∈ℤ}F(p_i,q_i))⋊ℤ`, which contains `F₂×F₂`: blocks between successive `t` letters occupy
distinct free factors. This audited strengthening shows that neither a cancellative semantic
monoid nor the forbidden subgroup in its group completion repairs the singular positive action.

**Scope:** Lean checks the orbit recurrence, exact zero language, rank-two generators, full finite
contexts, nonzero products, collision, and failed backward-cancellation law. The semidirect-product
normal form, infinite Fibonacci orbit, and absence of nilpotent products are audited deductions.
The singleton language is not the paired Neary language.

**Use:** never infer the saturation hypothesis of `G3-O05` from positive shift equivariance,
global minimality, or group-completion structure alone. The former program of proving its two
missing hypotheses on the paired residual system is closed by
[`G3-O17`](#g3-o17-paired-inverse-chamber): inverse-orbit cofinality is false uniformly.

**Artifact:** [`PositiveShiftCountermodel.lean`](MatrixMortality/PositiveShiftCountermodel.lean)
and
[`m34-positive-shift-countermodel-2026-08-08.md`](audits/m34-positive-shift-countermodel-2026-08-08.md).

### G3-O12: Positive reset dimension tax

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Let `v_w` be a projective code of the current reverse queue, let `H_b,H_c` prepend data letters,
and let `T` enter rule phase. Suppose the legal transitions satisfy

```text
H_bv_w∼v_bw,          H_cv_w∼v_cw,
H_bTv_wb∼v_bw,        H_cTv_wqb∼v_cw,
```

and each complete prepend cylinder spans the ambient finite-dimensional rational vector space.
Cylinder fullness makes both data maps invertible. At the legal queue `qb`, cancelling `H_b`
identifies `Tv_qb` with `v_q`, while cancelling `H_c` identifies it with `v_ε`. Hence

```text
v_q∼v_ε.
```

The standard homogeneous radix code has cylinder determinant
`B²(B−1)(d_b−d_c)`, so every nondegenerate two-coordinate radix or denominator recurrence lies
inside the theorem.

**Scope:** the proof is strictly positive and occurs on legal transitions; it uses no formal
inverse orbit, expansion bound, finite target, or illegal-state trap. It assumes residual locality,
both cylinder-fullness conditions, and persistent separation of `q` from `ε`. History-sensitive
states, collapsed legal cylinders, and a transient coordinate policing an intentional persistent
collision remain outside it.

**Use:** cull faithful projectively full queue/deque engines, including variants which only send
illegal histories into a denominator or ideal trap. The constructive paired leaf must now combine
a singular legal cylinder with source-computable entrance history; the fixed `bcbc` recognizer is
the model mechanism, not a uniform solution.

**Artifact:** [`PositiveResetNoGo.lean`](MatrixMortality/PositiveResetNoGo.lean) and
[`m34-positive-reset-dimension-tax-2026-08-08.md`](audits/m34-positive-reset-dimension-tax-2026-08-08.md).

### G3-S02: Rank-two kernel bifurcation

**Kind:** structure theorem

**Evidence:** formalized

**Disposition:** active

Let the two data controls have rank two. Their projective fibres are lines through their kernel
points. If the kernels coincide, a route difference in that common kernel remains invisible to
both data maps. When toggles preserve the kernel, any number of toggles retains the difference
and the first later data action annihilates it exactly.

For transverse coordinate kernels, use quotient charts

```text
π_b[x:y:z]=[y:z],       π_c[x:y:z]=[x:z].
```

If their target rays are `[u:v]` and `[r:s]`, with `s≠0`, Lean proves that every common fibre
point lies on the bilinear ray

```text
[rv : us : vs].
```

This is the precise survivor left by collapsed legal cylinders: two separately routed quotient
coordinates can coexist only through their common homogenizing product.

**Scope:** common-kernel erasure is conditional on the route difference already lying in the
kernel and on toggle invariance. The periodic `bcbb` compiler shows that toggle invariance is not
forced: its two data controls have exact common kernel `ℚ(1,1,0)`, the toggle sends its generator
to `(1,-1,0)`, and either next data control recovers `(2,0,0)`. Thus non-invariant kernel shuttling
is useful on an exact all-word paired language. The transverse formula is a fibre-intersection
law, not a source-computable invariant surface or an all-word same-zero construction.

**Use:** split every rank-two paired proposal by kernel geometry. A common-kernel constructor must
use a non-invariant shuttle or accept quotient factorization; a toggle-invariant persistent guard
is closed. In the transverse branch, solve the bilinear shift-equivariance equations rather than
returning to one-coordinate affine carries.

**Artifact:** [`PositiveResetNoGo.lean`](MatrixMortality/PositiveResetNoGo.lean),
[`PeriodicHistory.lean`](MatrixMortality/PeriodicHistory.lean),
[`m34-rank-two-kernel-bifurcation-2026-08-10.md`](audits/m34-rank-two-kernel-bifurcation-2026-08-10.md),
and [`m34-common-kernel-shuttle-2026-08-11.md`](audits/m34-common-kernel-shuttle-2026-08-11.md).

**Next:** construct a source-computable invariant surface in `P¹×P¹` closed under both prepend
maps and the bilinear reset, or prove that no linear terminal section can be exact on every
control word.

### G3-O18: Transverse minimum-body countermodel

**Kind:** fixed-subclass compiler

**Evidence:** formalized

**Disposition:** graduated

Assign the four paired roles the variable-radix recurrences

```text
R_b:w↦4κ(w)+1,    E_b:w↦4κ(w)+3,
R_c:w↦8κ(w)+2,    E_c:w↦8κ(w)+4.
```

Their residues modulo four distinguish the roles, so `κ` is injective. Three fixed integral
controls maintain the exact all-word state

```text
(8κ(w)−ε, 4κ(w)−ε, 1)ᵀ,
```

where `ε∈{±1}` is the retained paired phase. The two data controls have exact kernels `ℚe₁`
and `ℚe₂`; the phase toggle is an involution. The row `(1,−1,−4K)` vanishes exactly when the
decoded role word has code `K`.

Every minimum body has the unique terminal role word `R_c E(body)`. Choosing its computable code
therefore gives an exact three-state transverse-kernel recognizer on the complete paired-control
free monoid for every `β>2` and `|body|=β−1`.

**Scope:** this is an infinite, source-computable fixed subclass, but every instance in the
subclass has one known terminal word. It does not recognize unrestricted bodies, whose terminal
sets may be infinite. The result kills any lower bound derived from distinct rank-two kernels,
the bilinear fibre law, or exceptional projective fibres alone.

**Use:** a transverse constructor must now supply an infinite terminal section or genuinely
two-dimensional terminal dynamics. A lower bound must exploit unrestricted terminal arithmetic,
not transverse geometry by itself.

**Artifact:** [`TransverseHistory.lean`](MatrixMortality/TransverseHistory.lean) and
[`m34-transverse-history-2026-08-11.md`](audits/m34-transverse-history-2026-08-11.md).

**Next:** uniformize the terminal section beyond singleton target codes, or prove that every
source-computable transverse section with arbitrary-body soundness falls into a decidable class.

### G3-O13: Rational serializer pumping

**Kind:** obstruction

**Evidence:** audited; formalized core

**Disposition:** graduated

For even `β≥4` and a mixed body, no three-letter asynchronous finite-transducer relation can
exactly serialize arbitrarily large powers of four explicit Neary blocks. The serializer may use
state-dependent and nonunique spellings, erasure, physical letters crossing block boundaries,
fixed context on both target sides, and unbounded upper/lower lag.

Pumping one accepting path exposes a loop consuming a positive block power and emitting a
physical cycle. Exact transport for all pump counts makes both target images of that cycle powers
of cyclic rotations of the block images. Three `b`-head pulses force at least three physical
letters whose lower images lie in `b*`; hence every letter has that property. The mixed `c`-head
pulse instead requires a lower image containing `c`, a contradiction.

**Scope:** arbitrarily large powers of each test block must be encodable, and the two target sides
must be transported exactly up to fixed contexts. A solution-sensitive domain which truncates
most powers, final-equality-only transport, or a nonrational spelling relation remains outside the
theorem.

**Use:** close total finite-control stateful serialization and merge its genuine survivors into
the global word-residual leaf. Finite state can police syntax, but it cannot itself be the
computational store.

**Formalized core:** [`TernaryClosedBlockNoGo.lean`](MatrixMortality/TernaryClosedBlockNoGo.lean)
checks the bidirectional block-semantic equation on arbitrary stroke histories and the final
fractional-contribution contradiction. The transducer pumping and three-pulse word-factor audit
are recorded in
[`m34-rational-serializer-pumping-2026-08-08.md`](audits/m34-rational-serializer-pumping-2026-08-08.md).

### G3-D01: Bounded prefix residuals

**Kind:** decidable stratum

**Evidence:** audited

**Disposition:** stock

Given a GPCP instance and a certified bound `K` on every prefix discrepancy of every accepting
word, free-prefix reduction has a finite state set `0,+s,−s` with `|s|≤K`, plus dead and overflow
states. Final boundaries determine acceptance exactly; one bit enforces nonemptiness. Finite
decoder state and regular side conditions may be multiplied into the same graph.

**Scope:** the bound must be supplied effectively and need hold only on accepting paths. The
theorem does not decide instances whose accepting residual is unbounded or lacks a computable
uniform bound.

**Use:** reject every proposed universal ternary reduction which exports a computable accepting-
prefix residual ceiling. A surviving word residual must be unbounded and non-effectively bounded.

**Artifact:**
[`m34-rational-serializer-pumping-2026-08-08.md`](audits/m34-rational-serializer-pumping-2026-08-08.md).

### G3-D02: Virtually cyclic prefix discrepancy

**Kind:** decidable stratum

**Evidence:** audited; formalized core

**Disposition:** graduated

For any GPCP instance, restrict the search to words whose signed prefix discrepancy stays, in
each supplied finite mode, inside a finite set plus finitely many capped periodic rays

```text
±u p^n v.
```

Existence of a terminal word in this normal subclass is decidable. Every ray-to-ray update is a
two-power word equation; its exponent pairs are effectively finite plus at most one arithmetic
tail. Above a finite threshold, residual length is therefore one counter with fixed increments
and finite congruence control. Pushdown reachability decides acceptance.

**Scope:** caps, signs, periods, rotations, overlaps, erasing images, regular source modes, and an
indefinitely open residual are allowed. The ray templates and mode graph must be computably
supplied. Two independent exponents, unbounded word order at fixed length, and a halting-dependent
normal form remain outside the theorem.

**Use:** a global three-letter reduction cannot merely preserve one computably normal witness and
use its arbitrary-word converse for soundness; if that witness has a virtually cyclic residual
path, searching the normal subclass decides the source. Demand at least two counters or a genuine
word-valued residual.

**Formalized core:** [`WordDiscrepancy.lean`](MatrixMortality/WordDiscrepancy.lean) checks first-
mismatch permanence and all signed transition and terminal equations. The two-power lemma and
one-counter construction are audited in
[`m34-virtually-cyclic-discrepancy-2026-08-08.md`](audits/m34-virtually-cyclic-discrepancy-2026-08-08.md).

### G3-D03: One-sided corrected drift

**Kind:** decidable stratum

**Evidence:** audited; formalized core

**Disposition:** graduated

Give every transition of a finite-control paired certificate target words `(Uₑ,Vₑ)`, a positive
symbol weight `ω`, and a state potential `π`. If every trim transition has

```text
κ(e)=|Uₑ|ω−|Vₑ|ω+π(source(e))−π(target(e)) ≥ 0,
```

then terminal equality fixes the total corrected drift. Every accepting prefix spends at most
that budget. Prefix comparability identifies its weighted difference with the unmatched suffix,
giving an effective residual-length bound and a finite exact reachability graph. Reversing both
sides gives the nonpositive case. Existence of a suitable rational positive weight and potential
is an exact linear feasibility problem.

The same budget makes finite-control rewriting reachability decidable: every intermediate word
on a successful path has bounded positive weight. A one-state universal source must therefore
contain recurrent positive and negative drift under every positive symbol weighting.

**Scope:** finite control, state-dependent word images, arbitrary fixed boundaries, erasure, and
arbitrary word overlap are allowed. Mixed drift, an unbounded word-valued residual, and a normal
form unavailable to the reduction remain outside the theorem.

**Use:** reject bounded-delay, equal-height tableau, one-sided queue-growth, and acyclic-verifier
three-schema sources before attempting a GPCP compiler.

**Formalized core:** [`EndpointPrefixCompiler.lean`](MatrixMortality/EndpointPrefixCompiler.lean)
checks that a nonnegative corrected trace spends at most its complete endpoint budget. The finite
residual graph, potential criterion, and decision extraction are audited in
[`m34-endpoint-prefix-compiler-2026-08-08.md`](audits/m34-endpoint-prefix-compiler-2026-08-08.md).

### G3-D04: Priority-affine residual atlas

**Kind:** decidable stratum

**Evidence:** audited; formalized core

**Disposition:** graduated

Let a finite-mode normal-witness class parameterize every signed word residual by counters
`n∈N^d`. Require the parameterization to be effectively proper: a bound on residual length
effectively bounds every counter. Suppose every exact letter update is a finite union of affine
translations

```text
n ↦ n+v
```

guarded by fixed values of the first `j` counters, for one global counter priority. Initial and
terminal residual bounds then have finite counter preimages. Each guarded translation compiles
exactly to three counter operations: subtract the guarded constants, zero-test the first `j`
counters, and restore the constants while adding `v`. The resulting machine is a VASS with
nested zero tests, whose reachability is decidable.

Consequently, if an arbitrary-word converse is sound and every yes-instance has one witness in
such a computably emitted atlas, the old predicate is decidable. The atlas may have any fixed
finite dimension, cycles, reversals, sign modes, erasing images, and only one structured witness
per yes-instance.

**Scope:** guards must follow one fixed nested priority and updates here are additive
translations. Priority-aligned destructive transfer and reset are subsumed by
[`G3-D05`](#g3-d05-priority-triangular-transfer-atlas). Incomparable recurrent zero tests,
priority permutations, feedback, source-preserving copy, nonlinear counter interaction,
unbounded word order, and a noncomputable halting-dependent atlas remain outside. The generic
atlas assembly is audited; Lean checks the arithmetic macro but does not reimplement VASSnz
reachability.

**Use:** reject every literal finite-factor residual carrier whose exponents evolve affinely under
one nested guard hierarchy. A surviving global recoding must exhibit the precise non-priority,
non-additive, or genuinely word-valued operation it uses.

**Source:**
[`guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md`](references/guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md).

**Artifact:** [`PriorityAffineResidual.lean`](MatrixMortality/PriorityAffineResidual.lean) and
[`m34-priority-affine-residual-atlas-2026-08-10.md`](audits/m34-priority-affine-residual-atlas-2026-08-10.md).

**Next:** force either feedback, two incomparable recurrent tests, a changing priority, a
nonlinear counter operation, or an unbounded freely ordered residual in every proposed
three-pair recoding.

### G3-D05: Priority-triangular transfer atlas

**Kind:** decidable stratum

**Evidence:** audited; formalized core

**Disposition:** graduated

Fix one global counter order. A priority-triangular drain at pivot `i` repeatedly applies the
ordinary VASS shift

```text
−eᵢ+Aᵢ,
```

where the nonnegative fanout `Aᵢ` is supported strictly after `i`. The only stage exit tests that
the first `i+1` counters vanish. If the pivot enters with value `s`, natural-state semantics
permits at most `s` iterations and the exit test permits at least `s`; every successful stage
therefore executes exactly `s` loops. Its exact effect is

```text
nᵢ ↦ 0,
nₜ ↦ nₜ+s(Aᵢ)ₜ  for t>i.
```

Cascading these private stages after the existing debit guard and before a fixed final drift
compiles guarded reset, destructive transfer, fanout, and multiplication by arbitrary fixed
nonnegative constants into a VASS whose only tests are one nested hierarchy of initial
segments. Finite unions, modes, and compositions remain finite. Effective properness again
makes the initial and terminal residual fibres finite, so VASSnz reachability decides the
normal-witness search.

Lean proves the exact one-stage equivalence between the logical destructive transfer and an
existential number of ordinary loop iterations followed by the nested exit test. It separately
proves that the reset graph `n↦0` is not any finite union of fixed translations, so this record
strictly extends [`G3-D04`](#g3-d04-priority-affine-residual-atlas). The finite-mode atlas
assembly and imported VASSnz decision theorem remain audited.

**Scope:** fanout must be destructive and strictly forward in one fixed physical priority.
Backward transfer, source-preserving copy, cyclic reuse of priority levels, unbounded products
or data-dependent multipliers, incomparable or changing tests, and literal free-word order are
not covered.

**Use:** reject proposed escapes whose apparent nonlinearity is only a one-way drain, reset,
fanout, or fixed multiplier. The global recoding beam must now expose genuine feedback,
nonlinear interaction, changing tests, or irreducible word order.

**Source:**
[`guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md`](references/guttenberg-czerwinski-lasota-2025-vass-nested-zero-tests.md).

**Artifact:**
[`PriorityTriangularResidual.lean`](MatrixMortality/PriorityTriangularResidual.lean) and
[`m34-priority-triangular-transfer-2026-08-11.md`](audits/m34-priority-triangular-transfer-2026-08-11.md).

**Next:** force a backward edge, source-preserving feedback, a recurring transfer cycle, a
counter product, incomparable tests, changing priority, or an unbounded free-word residual.

### G3-D06: Functional phase-transfer guillotine

**Kind:** decidable stratum

**Evidence:** audited; formalized core

**Disposition:** graduated

Let three productions have positive net phase transfers

```text
Qdᵢ = −Aᵢeᵢ+Bᵢeτ(i),    Aᵢ,Bᵢ>0,    τ(i)≠i,
```

where `Q` is a nonnegative phase-by-symbol quotient with positive support in every symbol
column. The loopless functional graph `i↦τ(i)` is either one three-cycle or one two-cycle with a
feeder. In all eight labeled cases, positive rational phase weights can kill two edge drifts
exactly. The remaining edge chooses a common weak sign for all three. Lifting through `Q` gives
a strictly positive symbol weighting with that same one-sided drift.

For fixed source and target words, the induced word weight bounds every state in a successful
derivation by the heavier endpoint. The bounded word graph is finite and effectively searchable,
so every such functional private-head transporter has decidable reachability. Internal word
order and arbitrarily large charge-balanced payload do not evade the argument.

Lean checks the complete eight-shape classification, constructs the positive weights, proves the
quotient-lifting identity and strict symbol positivity, and proves both directions of the local
two- and three-cycle product inequalities. The finite reachability enumeration is audited rather
than implemented as a second normal-system decision procedure.

The boundary is sharp at the drift level. The head-separated fork

```text
ppX ⟶ Xq,    pX ⟶ Xqq,    qX ⟶ Xp
```

has a strict positive and a strict negative drift under every positive weighting. It represents
two competing `P→Q` edges and one `Q→P` return, whose two cycle products straddle one. Lean proves
this universal mixed-drift statement. It does not prove the fork undecidable.

**Scope:** every rule must consume positive projected charge from its own phase and deposit all
net positive charge into one definite different phase. Multiple forward edges from the same
phase, empty-consume pumps, splitting into several target phases, overlapping incomparable phase
channels, and displacements without such a positive quotient remain outside.

**Use:** reject cyclic private-head queues, two-cycles with a functional feeder, and any
balanced-payload refinement admitting the quotient above. A native head-separated source must
now use a forked two-cycle with products on opposite sides of one, an empty pump, or genuinely
nonfunctional phase splitting.

**Artifact:** [`FunctionalPhaseNoGo.lean`](MatrixMortality/FunctionalPhaseNoGo.lean) and
[`m34-functional-phase-transfer-2026-08-11.md`](audits/m34-functional-phase-transfer-2026-08-11.md).

**Next:** make the forked two-cycle preserve an unbounded mixed or neutral word across every
return. Competing pure-phase forward edges alone are closed by `G3-D07`.

### G3-D07: Pure-phase fork closure

**Kind:** decidable stratum

**Evidence:** audited; formalized arithmetic core

**Disposition:** graduated

Let `P,Q` be disjoint finite alphabets, permit any finite family of forward productions and one
return,

```text
αᵢX⟶Xβᵢ,    αᵢ∈P⁺, βᵢ∈Q⁺,
cX⟶Xd,       c∈Q⁺, d∈P⁺.
```

Reachability between arbitrary `P`-only endpoints is decidable. At every complete boundary,
forward steps first exhaust a `P` prefix and build a `Q` suffix; returns then exhaust that suffix
and build one power of `d`. Thus `dⁿ⟶*dᵐ` is the transitive closure of

```text
R(n,m) ↔ ∃u, α(u)=dⁿ and β(u)=cᵐ.
```

The valid trace language `α⁻¹(d*)∩β⁻¹(c*)` is effectively regular. Its effective Parikh image
and the two length equations make `R⊆ℕ²` effectively semilinear. Trace concatenation makes `R`
additive.

Every effective semilinear additive relation has decidable closure reachability. With one drift
sign, paths lie in a finite endpoint interval. With both signs, additivity produces a positive
diagonal `(h,h)∈R`. Quotienting by residues modulo `h` gives finitely many effective semilinear,
diagonally upward-closed edge relations. Each linear component compiles exactly to a nested
decrement-then-increment grammar macro; finite residue-path nonterminals compose the macros.
The result is literally a one-dimensional GVAS, whose reachability is decidable by Bizière and
Czerwiński's STOC 2025 Theorem 1.

Lean proves the reusable arithmetic throat: opposite drifts in an additive relation force a
positive diagonal. It also proves the exact two-variable linear equations, factor-two bounds,
modulo-three law, additivity, symmetry, and descent steps for the canonical
`pp→q, p→qq, q→p` fork. The general semilinear, grammar, and normal-system decision reductions
remain audited.

**Scope:** consumes and outputs are nonempty and phase-pure, and the sole return collapses every
complete boundary to one power `dⁿ`. The theorem allows arbitrary finite forward branching and
multi-letter words inside either phase. It does not cover a neutral word surviving a return,
mixed-phase boundary words, empty consumes, or genuinely split recurrent output.

**Use:** remove the canonical fork and every complete pure two-chamber refinement from the native
three-schema race. A surviving head-separated source must preserve an unbounded mixed or neutral
word across cycles, use an empty consume, or split recurrent transport.

**Source:**
[`biziere-czerwinski-2025-one-dimensional-pvas.md`](references/biziere-czerwinski-2025-one-dimensional-pvas.md).

**Artifact:** [`FunctionalPhaseNoGo.lean`](MatrixMortality/FunctionalPhaseNoGo.lean) and
[`m34-pure-phase-fork-closure-2026-08-30.md`](audits/m34-pure-phase-fork-closure-2026-08-30.md).

### G3-C03: Endpoint-prefix compiler

**Kind:** compiler

**Evidence:** formalized

**Disposition:** active

For a prefix normal system with three productions `αₓX⟶Xβₓ`, every lawful trace `w` from `s` to
`t` satisfies

```text
s β(w) = α(w) t.
```

If that endpoint equality itself forces every cumulative `α` prefix to be available at the
corresponding intermediate queue, Lean reconstructs every step and proves the converse. Taking
`g(x)=βₓ`, `h(x)=αₓ`, and boundaries `(s,ε,ε,t)` is then an exact three-pair GPCP compiler. The
empty witness corresponds exactly to `s=t`.

**Scope:** endpoint prefix forcing is a substantive source property. Lean's explicit underflow
system satisfies the aggregate equation for trace `a` although its first production is not
applicable. Arbitrary-substring semi-Thue traces also omit redex contexts, so the known
three-rule accessibility theorem does not instantiate the compiler.

**Use:** search directly for an undecidable family of endpoint-prefix-forcing three-production
normal systems. The source must also evade [`G3-D03`](#g3-d03-one-sided-corrected-drift).

**Artifact:** [`EndpointPrefixCompiler.lean`](MatrixMortality/EndpointPrefixCompiler.lean) and
[`m34-endpoint-prefix-compiler-2026-08-08.md`](audits/m34-endpoint-prefix-compiler-2026-08-08.md).

**Next:** make a three-rule queue architecture terminal-self-certifying without a recurrent copy
schema; demand a complete arbitrary-trace converse, not merely forward telescoping.

### G3-C04: Head-separated endpoint debt

**Kind:** compiler criterion

**Evidence:** formalized

**Disposition:** active

For every production `αₓX⟶Xβₓ`, suppose `βₓ` begins with a symbol which occurs nowhere in `αₓ`.
Compare the source and `αₓ` at the first rule of an arbitrary endpoint witness. If `αₓ` is not
already a prefix of the source, prefix comparability forces

```text
αₓ = source · d,       βₓ β(rest) = d α(rest) target
```

for a nonempty debt `d`. The left equation's second line begins with the fresh output symbol;
the right side begins with a symbol of `αₓ`, a contradiction. Repeating this argument after each
lawful step reconstructs the whole trace. Lean proves both the direct reconstruction and the
stronger consequence that endpoint prefix forcing holds for every source and target.

**Scope:** the condition is sufficient, not necessary. It neither constructs a universal
three-production source nor defeats the one-sided corrected-drift decision boundary. A cyclic
marker scheme which closes into finitely many token types remains decidable.

**Use:** make fresh output heads a default invariant in the native-source lane. The remaining
construction problem is wholly global: retain an unbounded open word residue and mixed drift
while using only three such productions.

**Artifact:** [`EndpointPrefixCompiler.lean`](MatrixMortality/EndpointPrefixCompiler.lean) and
[`m34-head-separated-endpoint-debt-2026-08-10.md`](audits/m34-head-separated-endpoint-debt-2026-08-10.md).

**Next:** construct or exclude an undecidable three-production head-separated prefix-normal
family with mixed drift in every positive Parikh direction.

### G3-O06: Periodic-ray completion and branching fracture

**Kind:** compiler and obstruction

**Evidence:** formalized

**Disposition:** graduated

At width three with body `bcbb`, every null history is exactly

```text
(bbb,cbb)^k.
```

The complete terminal role language is therefore `P₀Q*`, where

```text
P₀ = R_c E_b E_c R_b E_b E_b,
Q  = R_b E_b E_b R_c E_b E_b.
```

For most-significant-digit-first base-five code `V`, take

```text
κ=5443/15624,       α=5417371/9765000.
```

Lean proves `κ+V(w)=α5^|w|` exactly on `P₀Q*`. The converse uses
`gcd(5443,5⁶−1)=1` to force length modulo six, rejects the empty word, and then applies
injectivity of the role code. Three singular controls maintain the affine code, suffix-phase
sign, and positional scale on every arbitrary control word. Clearing the rank-one separator
gives four explicit integral `3 × 3` matrices whose mortality is equivalent to the `bcbb` paired
zero language. Their data maps have exact common kernel `ℚ(1,1,0)`, while the toggle moves its
generator outside that kernel and the next data action recovers it nontrivially. Thus `bcbb`
cannot support a same-zero dimension-four lower bound, and common-kernel shift laws do not imply
toggle invariance.

The adjacent body `bcbc` branches. The equal-length null blocks

```text
BBB,CBC,BBB,CBC
BBB,BCB,CBB,CBC
```

can be concatenated according to an arbitrary bit word. Prepending the fixed terminal history
gives an injective family of terminal role words, all of length `6+12n` for `n` input bits. Hence
one fixed length contains at least `2^n` terminal words. A single affine positional row fixes one
injective code at each length, so it cannot recognize the complete `bcbc` language.

**Scope:** the `bcbb` grammar, all-control affine converse, integral lift, `bcbc` binary terminal
fork, failure of a single affine positional section, and complete `bcbc` grammar
`FD(X(DZ)*F)*` are Lean-checked. The residual proof explicitly establishes the missing
right-residual rigidity invariant. The separate fixed-instance recognizer is [`G3-C02`](#g3-c02-fixed-bcbc-singular-recognizer).

**Use:** delete `bcbb`, periodic rays, positional digit refinements, and branching cardinality by
itself from the lower-bound frontier. The exact grammar is now reusable as a finite laboratory,
but `bcbc` is no longer a viable four-state lower-bound target after [`G3-C02`](#g3-c02-fixed-bcbc-singular-recognizer).

**Artifact:** [`PeriodicHistory.lean`](MatrixMortality/PeriodicHistory.lean),
[`BranchingHistory.lean`](MatrixMortality/BranchingHistory.lean), and
[`m34-periodic-ray-branching-fracture-2026-08-07.md`](audits/m34-periodic-ray-branching-fracture-2026-08-07.md),
with the shuttle classification audited in
[`m34-common-kernel-shuttle-2026-08-11.md`](audits/m34-common-kernel-shuttle-2026-08-11.md).

### G3-O07: Near-fork carry collision

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

For the body `bcbc`, the canonical controls

```text
p = c t b c b t c b t,
q = b t c b c t c b t
```

decode respectively to the terminal prefix `R_c E_b E_c R_b E_c E_b` and the nonterminal
near-fork `R_b E_c E_b R_c E_c E_b`. Lean proves that their paired coefficients are respectively
zero and nonzero.

Let `B,C,T` be arbitrary common controls, set

```text
D=B T C B,       Z=C T B B,
F=C T B C,       X=B T B B,
```

and let `γ,v` be columns. Lean proves the dimension-independent implication

```text
B B v = C B T γ  ∧  D Z v = F X v  ⇒  H_q γ = H_p γ.
```

Thus no rational same-zero representation in any dimension can satisfy both local identities.
This uses no global cancellation or invertibility; it isolates the exact internal comparison that
the complete binary-fork zeros do not yet force.

The proposed phase-line carry is closed parametrically. For `ρ≠−1`, put

```text
a=2/(ρ+1),       σ=ρ(ρ+1)²/4,

B=[[1,0,0],[0,a,σ],[0,0,0]],
C=[[1,ρ+1,−σ],[0,a,σ],[0,0,0]],
T=[[1,0,0],[0,0,1],[0,1,0]].
```

Lean normalizes its three stroke products and proves `DG=FD`, so the full physical products for
`p` and `q` are equal matrices. No row or column can repair the resulting false zero. This covers
every intended `ρ≥3` and strengthens the reported projective-coordinate collision.

**Scope:** the terminal/nonterminal pair, local collision law, parametric matrix identity, and
same-zero impossibility for the displayed family are Lean-checked. The result does not prove that
an arbitrary three-state recognizer satisfies the local recovery or fork identity. Singular
partial factors may separate the internal paths and merge them only after a complete block.

**Use:** delete two-phase, one-projective-coordinate stroke carries, including rational
contractions outside `G3-O04`. A surviving construction must use genuinely two-dimensional
projective history or prevent the near-fork suffix from entering the two-step erase image. A
lower bound must derive an internal collision from all terminal contexts without assuming
invertibility.

**Artifact:** [`BranchingHistory.lean`](MatrixMortality/BranchingHistory.lean) and
[`m34-near-fork-carry-collision-2026-08-07.md`](audits/m34-near-fork-carry-collision-2026-08-07.md).

### G3-C02: Fixed `bcbc` singular recognizer

**Kind:** fixed-instance compiler

**Evidence:** audited, with formalized core

**Disposition:** graduated

Write `X=BBB`, `D=BCB`, `Z=CBB`, and `F=CBC`. Canonical residual paths give the exact languages

```text
null histories      = (X(DZ)*F)*,
terminal histories  = FD(X(DZ)*F)*.
```

The checked residual invariant says every reachable nonempty right residual is exactly `b`.
Lean classifies the only entrances to the three live residuals and proves both grammars on
arbitrary role words.

There is a rational three-state candidate with row `λ=(1,0,0)`, column `γ=(1,2983,1)ᵀ`,
singular data matrices

```text
B=[[0,1,1/2],                  C=[[0,1/6125,-29503/6125],
   [0,5,385],                     [0,7,534],
   [0,0,1]],                      [0,0,1]],
```

and affine involution

```text
T=[[1,0,0],[0,-1,2983],[0,0,1]].
```

Lean proves its complete raw-control recurrence from `δ=(1,0,1)ᵀ`:

```text
H_wδ=(X(w),Y(w),1)ᵀ,
Y(bv)=5Y(v)+385,       X(bv)=Y(v)+1/2,
Y(cv)=7Y(v)+534,       X(cv)=(Y(v)-29503)/6125,
Y(tv)=2983-Y(v),       X(tv)=X(v).
```

Canonical terminal controls decode to the checked terminal grammar and vanish under both the
matrix coefficient and paired coefficient. Both data determinants are zero and `det T=-1`.

The audited reverse certificate removes `tt`, strips controls from targets `0` and `29503`, and
closes on finite graphs of 22 and 44 states. Its accepted paths are exactly the reduced canonical
language. Independent enumeration through length twelve checked 797,161 controls, sixteen zeros
on each side, and no mismatch. Thus the audited conclusion is

```text
zdim_ℚ(L₃,bcbc) ≤ 3.
```

**Scope:** the grammars, recurrence, determinants, canonical decoder, and intended zeros are
Lean-checked. The arbitrary-control reverse converse is audited but not yet kernel-checked, so the
zero-language dimension inequality is not a formal theorem. The constants are fitted to one
fixed regular language. A source-uniform finite-target affine construction would remain inside
the decidable class of `G3-O04`.

**Use:** retire `bcbc` as a lower-bound instance and reject branching width as evidence for four
states. Preserve the mechanism as a design clue: singular dynamics may use one persistent carry
and one transient guard to separate a malformed fork, then merge only at a complete block. The
master target is now uniformity across the source family, not this fixed grammar.

**Artifact:** [`BranchingRecognizer.lean`](MatrixMortality/BranchingRecognizer.lean) and
[`m34-bcbc-singular-recognizer-2026-08-08.md`](audits/m34-bcbc-singular-recognizer-2026-08-08.md).

### G3-C05: Equal-length mixed branching recognizer

**Kind:** fixed-instance compiler

**Evidence:** formalized

**Disposition:** graduated

At width three, the body `bcbcbb` has the complete terminal-history language

```text
P₀(A₀|B₀)*,
P₀=(CBC,BCB,BBB),
A₀=(BBB,BCB,CBB),
B₀=(BBB,CBC,BBB).
```

The two null blocks have the same length. Hence level `n` contains `2ⁿ` terminal histories,
without the nested-depth variation used by `bcbc`. Lean derives this grammar from a four-state
word-residual path and proves the terminal prefix by three exact cancellation steps.

Three explicit integral controls recognize the entire raw paired zero language:

```text
B=[[0,2,1],              C=[[0,2,-432372898],       T=[[1,0,0],
   [0,5,3703455],           [0,7,5236172],             [0,-1,21436039],
   [0,0,1]],                [0,0,1]],                   [0,0,1]].
```

With `λ=(1,0,0)` and `γ=(1,21436039,1)ᵀ`, Lean proves on every raw control word `w`

```text
λH_wγ=0  ↔  pairedCoefficient(ℚ,3,bcbcbb,w)=0.
```

The converse is not an enumeration. Adjacent toggles are scoured exactly, every normal control
word is decomposed into four affine carry macros, and a complete integer inverse-congruence
graph proves that the only target paths are one eight-macro entrance followed by arbitrary
nine-macro `A` or `B` returns. Both reported competing branches are formally shown to have no
integer predecessor, and the unmatched terminal toggle is excluded by carrying both possible
base states through the recursive classification.

Both data controls have determinant zero and exact common kernel `ℤ(1,0,0)ᵀ`; `T²=I` and
`det T=-1`. Every suffix state has last coordinate one, and no generator product is zero.

**Scope:** this is an exact all-word theorem for one fixed body. It refutes equal-length binary
branching, exponentially many same-level witnesses, finite return flowers, and common-kernel
guard refresh as lower-bound invariants. It neither constructs a source-uniform recognizer nor
proves that every body has a regular terminal section.

**Use:** delete fixed mixed-branching diagrams from the positive-projective lower-bound beam.
Any surviving obstruction must force incompatible transitions uniformly across an unbounded
terminal section, rather than count branches or exhibit finitely many return cycles.

**Artifact:** [`MixedBranchingHistory.lean`](MatrixMortality/MixedBranchingHistory.lean),
[`MixedBranchingRecognizer.lean`](MatrixMortality/MixedBranchingRecognizer.lean), and
[`m34-mixed-branching-recognizer-2026-08-11.md`](audits/m34-mixed-branching-recognizer-2026-08-11.md).

### G3-M02: Square-root punctuation fracture

**Kind:** partial mechanism

**Evidence:** formalized

**Disposition:** closed

Let `S` be one distinguished matrix among three ordinary controls and suppose

```text
S²=uvᵀ.
```

For a physical word `w`, put `c(w)=vᵀH_wu`. Whenever `w=l SS r`, rank-one multiplication gives

```text
c(w)=c(l)c(r).
```

Strong induction therefore extracts an `SS`-free scalar-zero residual from every zero product.
Conversely, `c(z)=0` gives the explicit zero word `SS z SS`. Lean proves, over an arbitrary
field and without rank or normalization assumptions,

```text
Mort({X₁,X₂,X₃,S}) ↔ ∃ z avoiding SS, vᵀH_zu=0.
```

For the side-normal Neary boundary `λ=(1,0,0)` and `γ=(μ,−1,T)ᵀ`, the source-uniform rational
matrix

```text
S=[[1,       0, 0],
   [−1/μ,    0, 0],
   [T/μ+1,   μ, 0]]
```

has `S²=(γ/μ)λ`, rank exactly two, and determinant zero. Assigning isolated `S` to `R_b` is
compatible with every lawful width-at-least-three history. The sole constructive obligation is
now a three-state same-zero representation of the original role series on the complete
`R_bR_b`-free subshift.

A `3×3` inserted Hankel certificate on prefixes and suffixes `ε,D_c,D_b` proves that any
three-state representation preserving the old coefficient exactly on that subshift makes its
`R_b` matrix invertible. The conclusion survives arbitrary nonzero per-letter multiplicative
weights. A successful completion must therefore change nonzero values in a genuinely
word-dependent way.

The adjacent additive family

```text
αA+cA^ε(γλ)A^δ,     ε,δ∈{0,1}, α≠0,
```

is separately audited immortal: the inverse active semigroup never reaches the terminal
incidence, and the unique singular update preserves rank two through every interstitial word.

**Scope:** the square identity, rank, complete arbitrary-word fracture, exact-series rigidity,
and weighted rigidity are Lean-checked. The reverse-marker and additive-fusion obstructions are
audited paper proofs. No same-zero matrices on the `SS`-free subshift are known.

**Use:** retain the fracture theorem as reusable punctuation, but do not pursue the direct Neary
role identification. `G3-O10` proves that every admissible square root preserves coefficient
vanishing when placed at either boundary, contradicting the source's initial-role rigidity.

**Artifact:** [`SquareRootPunctuation.lean`](MatrixMortality/SquareRootPunctuation.lean) and
[`m34-square-root-punctuation-2026-08-08.md`](audits/m34-square-root-punctuation-2026-08-08.md).

### G3-O10: Square-root boundary saturation

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Over any field, let `P²=uvᵀ` with `vᵀu≠0`. Commutation with its square forces one nonzero scalar
`σ` such that

```text
Pu=σu,        vᵀP=σvᵀ,        σ²=vᵀu.
```

Consequently the boundary insertions `Pw` and `wP` preserve the zero set of every scalar series
`vᵀH_wu`, independently of dimension, rank, and the ordinary generators.

The checked arbitrary-word Neary converse supplies the incompatible source fact. Every terminal
match begins with `R_c`, so prefixing any role word by `R_b` can never produce a native zero. A
terminal word and its physical `P`-prefix are both `PP`-free at deletion width at least three.
Thus no same-zero representation on the complete `PP`-free fracture domain can identify `P` with
`R_b`. This closes the square-root attack opened by `G3-M02`; choosing another root cannot evade
the obstruction.

**Scope:** Lean proves the dimension-free eigenvector theorem, both boundary zero equivalences,
arbitrary-terminal-match initial-role rigidity, and the exact logical contradiction from a
square-free witness pair. The routine composition producing that pair from a complete Neary
history is audited at list-syntax level. Semantic macros, degenerate separators `vᵀu=0`, and
fracture languages excluding boundary punctuation remain outside the theorem.

**Use:** reject every nondegenerate rank-one square-root compiler using scalar readout on the full
square-free domain and a direct Neary rule-role decoder. Any future punctuation route must alter
one of those structural hypotheses, not merely the displayed root.

**Artifact:** [`SquareRootPunctuation.lean`](MatrixMortality/SquareRootPunctuation.lean),
[`NearyEncoding.lean`](MatrixMortality/NearyEncoding.lean), and
[`m34-square-root-boundary-saturation-2026-08-08.md`](audits/m34-square-root-boundary-saturation-2026-08-08.md).

### G3-M01: Free-group discrepancy engine

**Kind:** partial mechanism

**Evidence:** audited

**Disposition:** active

For the fixed cyclic-tag program, Carvalho's inverse transducer carries the queue in the freely
reduced discrepancy

```text
Δ(w) = w⁻¹T(w).
```

On a legal transition, cancellation deletes the queue head while the transducer output appends
the production. An `H` marker counts simulated steps, a unique `p` marker excludes trivial false
paths, and first-letter cancellation supplies an all-positive-word converse. Rotating the
terminal marker word gives the exact marker-tail equation

```text
e halts ↔ ∃τ∈{0,1,H,p}*, n≥0: τ p H^n=d_e Ψ(τ).
```

The full closed-path subgroup for `m` appendants has rank `3m+1`, but the accepting fixed
subgroup is trivial on a nonhalting instance and infinite cyclic on a halting instance:

```text
Fix(T̃_C)={1}       if C does not halt,
Fix(T̃_C)=⟨g_C⟩    if C halts.
```

The generator is a conjugate of the first marker-only cycle and is not a proper power. It cannot
be selected from a computable finite menu. Carvalho's `p`-exponent character gives the sharper
existential slice: for the equalizer maps `g,h:F_Y→F_A`, put `κ=χ∘h`; then

```text
C halts ↔ ∃u∈F_Y, g(u)=h(u) and κ(u)=1.
```

Moreover `χ∘g=χ∘h` on all of `F_Y`, not only on the equalizer. The character excludes the
identity and selects the primitive orientation without choosing one positive spelling.

**Scope:** the marker-tail form uses one fixed four-letter sequential transducer, a
source-dependent positive prefix, and a unary tail. The equalizer form lives in a free group,
not a positive free monoid. Neither the cyclic accepting subgroup nor the exponent-one slice
alone supplies a three-control compiler. Positive Nielsen-basis compression is impossible by
[`M4-O17`](#m4-o17-positive-nielsen-basis-obstruction), and coarse shared-character promises are
insufficient by [`G3-O19`](#g3-o19-correlated-affine-slice-density).

**Use:** preserve the all-word marker-tail converse when applying the boundary punctuation
mechanism [`M4-M05`](#m4-m05-boundary-guarded-homogeneous-punctuation). In the group route,
compile the exponent-one equalizer slice rather than the complete Stallings basis or a selected
irreducible spelling.

**Source:** [`carvalho-2026-free-group-pcp.md`](references/carvalho-2026-free-group-pcp.md).

**Artifacts:**
[`m34-free-group-discrepancy-2026-08-08.md`](audits/m34-free-group-discrepancy-2026-08-08.md)
and [`m43-free-group-punctuation-2026-08-11.md`](audits/m43-free-group-punctuation-2026-08-11.md).

**Next:** compile the marker-tail equation to positive binary fixed-boundary free-group equality,
or realize `g(u)=h(u), κ(u)=1` through three positive controls with a spelling-sensitive or
nonalgebraic carrier. A decision procedure for the restricted marker-tail problem would close
that route.

### G3-M03: Three-positive affine exponent cover

**Kind:** partial mechanism

**Evidence:** formalized

**Disposition:** active

Let three positive letters evaluate in `F(a,b)` by

```text
x ↦ a,       y ↦ b,       z ↦ b⁻¹a⁻¹.
```

Give them signed weights `1,0,−1`. The induced word weight is exactly the exponent of `a` after
free reduction. Lean proves the stronger slice statement: for every integer `d`, evaluation maps
the positive words of weight `d` surjectively onto all free-group elements whose `a`-exponent is
`d`. Thus the positive alphabet loses no element of an affine exponent slice, and the converse is
automatic for every arbitrary positive spelling.

The identity word `xyz` has weight zero. Appending it changes neither evaluation nor weight, so
positive identity padding is harmless for exponent-one acceptance.

For a rank-`r` source group with primitive `κ`, the audited Nielsen-Schreier step embeds it into
the index-`r−1` subgroup of `F(a,b)` so that the `a`-exponent becomes `(r−1)κ`. Consequently
Carvalho's predicate becomes a three-positive equalizer with one exact signed-weight constraint.

**Scope:** the transported morphisms are defined on the finite-index subgroup, not on all of
`F(a,b)`. Signed weight is an affine side condition, not yet an ordinary GPCP boundary equation or
one scalar zero. The Nielsen basis and subgroup embedding remain audited paper algebra; Lean
checks the complete ambient positive-cover seam.

**Use:** abandon positive normal-form filters. Extend the correlated equalizer from the
finite-index subgroup to three ambient positive controls while retaining the exact weight slice,
or represent the group discrepancy and cocycle inseparably in three projective coordinates.

**Artifact:** [`PositiveFreeCancellation.lean`](MatrixMortality/PositiveFreeCancellation.lean) and
[`m34-three-positive-affine-cover-2026-08-10.md`](audits/m34-three-positive-affine-cover-2026-08-10.md).

**Next:** compile the subgroup-domain equalizer and weight equation jointly into ordinary
three-pair GPCP or a three-state scalar-zero series.

### G3-O19: Correlated affine-slice density

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

The coarse Carvalho promises do not force an algebraic dimension drop. Let `F=F(a,b)`,

```text
h=id,    g(a)=a,    g(b)=b²,    κ=expₐ.
```

Then `h` is injective, `κ∘g=κ∘h`, and `Eq(g,h)=⟨a⟩`; every slice
`Eq(g,h)∩κ⁻¹(t)` is the singleton `{aᵗ}`. Under Carvalho's explicit faithful embedding
`ρ:F₂→SL₂(ℤ)`, the correlated graph of `ker κ` has Zariski-dense projections. Algebraic Goursat
leaves either the full product or the graph of an automorphism of `PSL₂`. The graph case would
send `ρ(b)` to `ρ(b²)`, impossible because projective trace-squared is respectively `16` and
`196`. Thus every fixed-`κ` slice of the correlated graph is Zariski dense in `PSL₂×PSL₂`.

Any rational multiplicative carrier extending algebraically from this graph and depending
nontrivially on both factors has dimension at least four: irreducible product representations
have dimension `(m+1)(n+1)≥4`, and separate nontrivial constituents cost `2+2`. Projective and
two-dimensional affine-cocycle versions have the same bound after lifting or homogenizing.

The canonical mixed carrier has an explicit rank-four Hankel certificate. For rows
`ε,x,y,xy` and columns `ε,z,xz,zy`, its scalar section is

```text
[[ 0, −2,   1, 465],
 [ 0,  1,  22,  51],
 [ 2,  0, 429,  23],
 [−1,  0, 843,   2]],
```

with determinant `1,197,990`. Exact arithmetic independently reproduces the certificate.

**Scope:** this is a synthetic correlated graph satisfying injectivity, a globally shared
primitive character, cyclic equalizer, and singleton exponent-one slice. It is not proved to be
the graph emitted by Carvalho's cyclic-tag reduction. The example's accepted language is
visibly `π(w)=a` and itself has a two-state same-zero detector, so the result is not a general
same-zero or language-rank lower bound.

**Use:** reject every proposed dimension-three theorem derived only from the coarse source
promises or from conditioning on the shared affine character. `G3-O21` subsequently uses the
explicit numbered-state transitions to prove the actual graph dense as well; only
spelling-sensitive, nonalgebraic, or infinite-dimensional scalarization remains.

**Source:** [`carvalho-2026-free-group-pcp.md`](references/carvalho-2026-free-group-pcp.md).

**Artifact:**
[`m34-correlated-affine-slice-density-2026-08-11.md`](audits/m34-correlated-affine-slice-density-2026-08-11.md).

### G3-O21: Actual Carvalho slice density

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

Let `R_C` be Carvalho's complete numbered-state transducer for a cyclic tag system of positive
period `m`. Write `S` for its loop subgroup at state zero, `ψ:S→F(0,1,H,p)` for its output
homomorphism, `d₀=w₀p`, `θ(x)=d₀ψ(x)d₀⁻¹`, and `χ=exp_p`. For every faithful Schottky embedding
`ρ:F(0,1,H,p)→SL₂(ℂ)` and every `t∈ℤ`,

```text
{([ρ(θ(x))],[ρ(x)]) : x∈S, χ(x)=t}
```

is Zariski dense in `PSL₂×PSL₂`.

For `K=S∩ker χ`, the second projection contains the noncommuting words `H,pHp⁻¹`; the first,
before conjugation by `d₀`, contains `H,pHᵐp⁻¹`, since `ψ(p0ᵐp⁻¹)=pHᵐp⁻¹`. Both projections
are therefore dense. Algebraic Goursat leaves the full product or an automorphism graph. On
`⟨H,pHp⁻¹⟩≤K`, `ψ` is the identity, so that automorphism must be conjugation by `ρ(d₀)`. But
`0ᵐ∈K` and `ψ(0ᵐ)=Hᵐ≠0ᵐ`, excluding the graph case. Finally, `pᵗ∈S` makes every `χ=t` slice a
translate of the dense kernel graph. The partial-transducer maps `g,h` differ from this graph
only by coordinatewise conjugation by the `#` boundary.

**Scope:** the theorem uses the explicit numbered-state transitions, positive period, and a
faithful Schottky embedding. It excludes algebraically extendable carriers which retain both
group coordinates in dimension three. It is not a same-zero language lower bound and does not
exclude spelling-sensitive, graph-only nonalgebraic, singular nonsemantic, or infinite-state
constructions.

**Use:** close the actual program-graph geometry leaf. Searching this graph for a proper
algebraic three-dimensional quotient is finished. `G3-O22` and `G3-O23` subsequently reduce the
remaining scalar-language route to invertible projective group orbits.

**Source:** [`carvalho-2026-free-group-pcp.md`](references/carvalho-2026-free-group-pcp.md),
Theorem 4.1 and the explicit transducers in Sections 3 and 5.

**Artifact:**
[`m34-actual-carvalho-slice-density-2026-08-30.md`](audits/m34-actual-carvalho-slice-density-2026-08-30.md).

### G3-O22: Invertible fibre-span rigidity

**Kind:** structural reduction

**Evidence:** formalized core

**Disposition:** graduated

Let a positive evaluation `π:S*→G` surject onto a group, let every control act invertibly on a
finite-dimensional vector space, and fix a seed `γ`. For

```text
C_q = span { M_w γ : π(w)=q },
```

Lean proves `M_u C_q=C_{π(u)q}` for every positive word `u`. The forward inclusion is literal
prefixing. A positive spelling of `π(u)⁻¹` gives the reverse dimension inequality, and
invertibility preserves dimension. Consequently all fibres have one common positive dimension
when `γ≠0`.

For a nonzero scalar boundary `λ` in dimension three, vanishing on every spelling of one fibre
is exactly `C_q≤ker λ`, so `dim C_q∈{1,2}`. Rank one is a projective point-to-hyperplane orbit
incidence. In rank two, `C_q=ker λ`; the dual point follows a group orbit. On the triangle cover,
the `x,y` transitions and their linear inverses implement the two-generator group action on the
family of fibre subspaces.

The identity fibre has an intrinsic finite algebra. Lean defines the unital subalgebra

```text
A = span { M_w : π(w)=1 } ≤ End(V)
```

and proves `C_1=Aγ`. For the triangle cover over an effective field, `A` is computable by finite
subspace saturation of an effective context-free grammar for `π⁻¹(1)`; the grammar algorithm is
audited rather than formalized.

**Scope:** all transitions must be linear equivalences, positive evaluation must be surjective,
and the rank dichotomy uses nonzero seed and boundary. The resulting orbit uses inverse linear
maps. It is a group/Grassmannian reduction, not a positive-semigroup reduction to `M₃(2)`, and it
does not cover singular spelling carriers.

**Use:** reduce the everywhere-invertible Carvalho branch to a computable rank-one or rank-two
group-orbit incidence problem. `G3-O23` subsequently collapses the singular saturated branch to
an invertible two-state carrier; do not treat arbitrary infinite fibres as unstructured state.

**Artifact:** [`PositiveFreeCancellation.lean`](MatrixMortality/PositiveFreeCancellation.lean)
and
[`m34-invertible-fibre-span-2026-08-30.md`](audits/m34-invertible-fibre-span-2026-08-30.md).

### G3-O23: Singular triangle-carrier collapse

**Kind:** structural reduction

**Evidence:** formalized core

**Disposition:** graduated

Let `π:S*→G` surject positively onto a group, and suppose a rational three-dimensional scalar
series recognizes a saturated language `L⊆G` and rejects at least one known group element. If a
positive semantic-identity word `r` acts singularly, then the same zero language has an exact
two-dimensional realization in which every control is invertible.

The formal proof uses positive spellings of inverse semantic letters. It is algorithmic when
those spellings are effectively supplied, automatically for the triangle cover. An identity
operator of rank at most one factors as `vφ`; inserting it between arbitrary left and right
spellings makes the zero language rectangular, hence universal or empty. A nontrivial singular
identity operator `P` therefore has rank two. On
`U=im P`, every sandwich `u↦PM_su` is invertible: a singular sandwich and a positive spelling of
the inverse semantic letter would create another rank-at-most-one identity loop. Interleaving
`r` before each letter and after the word proves exact recognition on `U`, including the empty
word. Over `ℚ`, Gaussian elimination chooses a rational basis of `U` and produces literal
invertible `2×2` transitions. The empty-language branch has a fixed invertible two-state model.

For the triangle cover, `xyz` is a semantic identity and is singular whenever any of `X,Y,Z` is
singular. Lean therefore proves the dichotomy: either all three original `3×3` transitions are
invertible, or an equivalent everywhere-invertible `2×2` three-control carrier exists.

For a singleton saturated language on the triangle semantic group `F₂`, `G3-O22` sharpens the
reduced carrier to a faithful `PGL₂(ℚ)` action with a free orbit and

```text
[T_z]=[T_y]⁻¹[T_x]⁻¹.
```

**Scope:** saturation through the positively surjective group evaluation and one rejected group
element are essential. Abstract surjectivity is non-effective unless positive inverse spellings
can be computed. The output has three positive controls. The displayed relation is in the two-
generator group action; it does not turn the inverse edges into positive words in `T_x,T_y` and
is not a positive `M₂(3)` or `M₃(2)` reduction.

**Use:** remove singular spelling memory as a separate Carvalho escape. Any singular saturated
three-state construction would simultaneously construct an effective invertible two-state
projective group-orbit instance. Treat this as a joint `M₃(4)`/dimension-two research seam.

**Artifact:** [`PositiveFreeCancellation.lean`](MatrixMortality/PositiveFreeCancellation.lean)
and
[`m34-singular-triangle-collapse-2026-08-30.md`](audits/m34-singular-triangle-collapse-2026-08-30.md).

### G3-O24: Directed-Dyck absorption collapse

**Kind:** obstruction

**Evidence:** formalized core

**Disposition:** graduated

Every finite-dimensional algebra over a field is directly finite: `PQ=1` implies `QP=1`.
Consequently, a finite-dimensional scalar carrier which identifies `PQ` with the identity in
every two-sided value context must also identify `QP` with the identity. The same conclusion
holds for zero contexts whenever the selected context family separates algebra elements up to a
nonzero scalar. More sharply, any zero-context family which distinguishes `QP` from the identity
forces `PQ` away from every nonzero scalar identity and fails global projective separation.

This applies to a tempting but invalid compression of the Matiyasevich–Sénizergues three-rule
system. Its last rule is the directed deletion `xx̄→ε`, not the congruence `xx̄=1`. The stable
cone is `K_st=Desc_D(Im τ₄)=B*y`, strictly inside the complete decoder domain
`(yD₁*)*y`. Proposition 3.5 shows that a deletion can shrink the directed descendant set and
move the greatest-lower-bound decoder down a nontrivial source path. Rule names omit both redex
contexts, and no canonical deletion schedule or postponement theorem is supplied.

**Scope:** this kills faithful quotient absorption, complete scalar-value saturation, and
projectively faithful zero saturation in every finite dimension. It does not kill a singular
carrier confined to the directed stable cone. Such a carrier may distinguish redex positions
through nonprojective zero-context blindness and couple the deletion inseparably to the other two
rules. It also does not turn the arbitrary-substring source into three prefix productions.

**Use:** reject every construction which replaces the directed deletion by an algebra identity.
A surviving S5 attack must realize its directed decoder order on the unbounded stable cone. Test
rank-two singular actions directly rather than appealing to the eight-element letter lattice
alone.

**Source:**
[`matiyasevich-senizergues-2005-few-rule-semi-thue.md`](references/matiyasevich-senizergues-2005-few-rule-semi-thue.md).

**Artifact:** [`DirectedCancellation.lean`](MatrixMortality/DirectedCancellation.lean) and
[`m34-directed-dyck-absorption-2026-08-30.md`](audits/m34-directed-dyck-absorption-2026-08-30.md).

### G3-O20: Consecutive-repeat tail closure

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

For arbitrary free-monoid words `A,B,C,D,E,F` and `N`, suppose

```text
A Bᴺ C = D Eᴺ F,       A Bᴺ⁺¹ C = D Eᴺ⁺¹ F.
```

Then `A Bᴺ⁺ᵏ C = D Eᴺ⁺ᵏ F` for every `k≥0`. After absorbing the first `N` copies into
`A,D`, prefix comparability leaves two cases. If `D=AG`, cancellation gives `C=GF` and
`BG=GE`; if `A=DG`, it gives `F=GC` and `GB=EG`. Either conjugacy equation iterates and proves
the entire tail.

**Scope:** the theorem requires one stationary pump block on each side and fixed boundaries. It
does not constrain two interacting pump directions, changing blocks, nonliteral matrix zero
languages, or histories whose terminal section changes with the exponent.

**Use:** delete the unary Cayley-Hamilton lower-bound shortcut for fixed-boundary word equality.
A three-state unary coefficient would be refuted by three consecutive zeros followed by a
nonzero escape, but literal equality already forces the tail from the first two zeros. Any live
positive-transition lower bound must use noncommuting or nonstationary shifts.

**Artifact:** [`WordMorphism.lean`](MatrixMortality/WordMorphism.lean) and
[`m34-consecutive-repeat-tail-2026-08-30.md`](audits/m34-consecutive-repeat-tail-2026-08-30.md).

### G3-O09: Quotient-blind positive boundary collapse

**Kind:** obstruction

**Evidence:** formalized core

**Disposition:** graduated

Three positive letters `x,y,z`, evaluated by

```text
x↦x,       y↦y,       z↦y⁻¹x⁻¹,
```

surject onto `F₂`; Lean proves this by free-group induction. The cyclic words `xyz,yzx,zxy` are
nonempty spellings of the identity. Thus positivity does not itself remove formal inverses.

Let a positive evaluation `π:S*→G` surject onto a group. Suppose fixed homomorphic boundaries
accept a group element `g` and its square:

```text
ℓ α(g) r = ℓ′ β(g) r′,
ℓ α(g²) r = ℓ′ β(g²) r′.
```

Group cancellation forces `ℓr=ℓ′r′`. Surjectivity gives a nonempty positive identity word, and
the boundary equality accepts it. Lean proves the boundary-square lemma and constructs the false
witness over arbitrary groups.

**Scope:** the application to Carvalho assumes completeness for every nontrivial accepting fixed
loop, hence for both `g_C` and `g_C²`, and assumes the final test factors only through the evaluated
group element. It does not cover existential-only witness transport, a test of the unreduced
positive spelling, partial action, or singular dynamics which destroy inverse continuations.

**Use:** reject Nielsen or Schreier compression followed by quotient-blind boundaries which accept
the complete nontrivial fixed subgroup. A survivor must restrict the accepted quotient elements,
not merely choose a positive normal form for all of them.

The exponent-one slice in [`G3-M01`](#g3-m01-free-group-discrepancy-engine) escapes this theorem:
it accepts the primitive orientation but not its square, since `κ(u^n)=n`.

**Artifact:** [`PositiveFreeCancellation.lean`](MatrixMortality/PositiveFreeCancellation.lean)
and [`m34-free-group-discrepancy-2026-08-08.md`](audits/m34-free-group-discrepancy-2026-08-08.md).

### G3-O14: Positive cancellation spelling dichotomy

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

An injective transition over a finite invariant semantic fibre is periodic on every fibre point.
Thus a positive semantic identity word `r` satisfies `T_(r^k)ξ=ξ` for some `k>0`, even when the
finite spelling state is twisted arbitrarily over the semantic discrepancy. Cancellative target
overlap is bijective in the free-group completion and therefore cannot make every wrong-time
identity insertion permanent with finite fibres.

Singularity does not repair a three-dimensional lift which retains a two-dimensional invertible
quotient. If `qP=ρq`, `ρ` is injective, `P` is singular, and `ker q` is one-dimensional, then
`ker P=ker q`. Every quotient identity `qR=q` consequently satisfies `PR=P`. After the first
singular prefix, later triangle-identity factors are equal as complete products and cannot be
separated by boundaries.

**Scope:** finite fibres are required in the invertible branch. The singular branch requires a
one-dimensional extension of an injective quotient action. Everywhere-invertible infinite fibres,
unbounded cocycles, and constructions whose persistent semantics are singular remain outside.

**Use:** delete the seven-state cancellative spelling lift and transient singular third-coordinate
guard. Attack the exponent-one slice from [`G3-M01`](#g3-m01-free-group-discrepancy-engine)
without selecting a normal spelling.

**Artifact:** [`PositiveFreeCancellation.lean`](MatrixMortality/PositiveFreeCancellation.lean) and
[`m34-positive-cancellation-obstructions-2026-08-08.md`](audits/m34-positive-cancellation-obstructions-2026-08-08.md).

### G3-O15: Triangle normal-form rank six

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Let `N` contain exactly the positive words avoiding `xyz`, `yzx`, and `zxy`. The coefficient table
on prefixes and suffixes `x,y,z,xy,yz,zx` has six private nonzero entries. Columns `x,y,z` isolate
rows `yz,zx,xy`; after those vanish, columns `yz,zx,xy` isolate rows `x,y,z`. Lean proves the rows
independent over every field and proves that every row-column factorization has at least six
states.

**Scope:** the scalar zero language must equal the complete standalone irreducible language `N`.
A legality predicate coupled inseparably to one program-specific halting equation can have a
different support table and is not excluded.

**Use:** reject every proposal to fuse a separate three-state triangle-normal-form detector with
Carvalho semantics. Legality must disappear from the target or be inseparable from the
exponent-one equalizer predicate.

**Artifact:** [`PositiveFreeCancellation.lean`](MatrixMortality/PositiveFreeCancellation.lean) and
[`m34-positive-cancellation-obstructions-2026-08-08.md`](audits/m34-positive-cancellation-obstructions-2026-08-08.md).

### G3-O16: Full augmented-pair dimension tax

**Kind:** obstruction

**Evidence:** audited

**Disposition:** graduated

Suppose a homomorphic linear detector represents the full independent carrier
`F×F×ℤ` and vanishes exactly when its first two entries agree and the integer entry is one.
Fixing that integer slice and comparing diagonal pairs forces the two factor actions to be
faithful; the product law makes their images commute.

In characteristic zero, two commuting faithful nonabelian free groups do not embed in `GL₃`.
An irreducible first factor has scalar commutant. A reducible representation has composition
factors `1+1+1`, giving solvable image, or `2+1`, whose unit commutant is solvable. Either case
contradicts faithfulness of the second free factor.

**Scope:** this excludes the full independent direct-product carrier. Carvalho supplies only the
correlated graph `u↦(g(u),h(u),κ(u))`; a three-dimensional representation of that graph need not
extend to independent factors. The centralizer classification is independently audited, not
kernel-checked here.

**Use:** reject constructions which first represent two arbitrary free-group values and an
independent counter, then compare them. Preserve program correlation throughout the recurrence.

**Artifact:**
[`m34-three-positive-affine-cover-2026-08-10.md`](audits/m34-three-positive-affine-cover-2026-08-10.md).

### G3-O17: Paired inverse chamber

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Let `P={x,z}*` be the positive submonoid of the binary free group. Every checked paired suffix
residual belongs to `PP⁻¹`; its reduced signed word has no negative-to-positive turn. Every
phase-aware prefix residual belongs to `P⁻¹P`; its reduced signed word has no
positive-to-negative turn.

The independent role discrepancies from [`G3-O05`](#g3-o05-cancellative-projective-state-tax)
produce the formal inverse states

```text
ξ_L = x⁻ᵝ z xᵝ z⁻¹,
ξ_R = x z⁻² x⁻¹ z².
```

For `β>0`, both words are freely reduced and contain both sign turns. Every Neary upper role word
ends in `z`, while every lower role word ends in `x`. Consequently a positive role continuation
`U ξ V⁻¹` cancels neither seed boundary; both internal turns survive. Lean proves, for every body,
role sequence, suffix, prefix context, and entering phase,

```text
U ξ_L V⁻¹, U ξ_R V⁻¹ ∉ PP⁻¹ ∪ P⁻¹P,
U ξ_L V⁻¹, U ξ_R V⁻¹ ≠ every actual suffix or prefix residual.
```

Thus entire positive forward cones of two indispensable formal inverse states are absent from the
paired residual grammar. No Ore-style common future or positive representative can supply the
inverse saturation required by `G3-O05`.

**Scope:** this kills grammar-forced inverse-orbit cofinality, not every representation-specific
projective extension. A particular matrix representation could impose extra projective points and
incidences, but their faithful equivariant continuation would be an additional hypothesis not
determined by the zero language. The theorem does not prove a four-state lower bound.

**Use:** delete paired residual saturation as a raceable lower-bound leaf. The next one-sided
lower-bound object is a finite positive projective transition diagram carrying actual generator
ranks, kernels, images, and base loci across every singular rank pattern.

**Artifact:** [`PairedInverseChamber.lean`](MatrixMortality/PairedInverseChamber.lean) and
[`m34-paired-inverse-chamber-2026-08-10.md`](audits/m34-paired-inverse-chamber-2026-08-10.md).

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

### D2-S02: Monotone affine path form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** stock

Suppose the two projective generators share a rational fixed point. After
sending it to infinity and removing the elementary cases, an affine conjugacy
puts them in the form

```text
F(z)=az,      G(z)=bz+1,      a,b∈ℚ×.
```

Every operational word is uniquely

```text
F^m₀ G F^m₁ G ⋯ G F^mₙ,      mᵢ≥0.
```

With `M=Σmᵢ` and `sⱼ=Σᵢ₌ⱼⁿmᵢ`, its action is

```text
w(x)=a^M b^n x + Σⱼ₌₁ⁿ a^sⱼ b^(n−j),
M≥s₁≥⋯≥sₙ≥0.
```

Conversely the monotone chain recovers every block length. The translation
terms therefore occupy one ordered exponent path with one contribution in
each `b`-layer; they are not independent `S`-units.

**Scope:** this is a normal form, not a decision procedure. Projective
source or target points at infinity are trivial because every affine map fixes
infinity. If the second translation vanishes, the pair preserves `{0,∞}`. If
both multipliers are one, reachability is a semilinear translation problem.

**Use:** preserve the path order in every affine attack. General `S`-unit
encodings that forget it may replace the problem by a strictly harder one.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#affine-normalization-and-path-form).

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

### D2-D05: Prescribed translation count

**Kind:** decidable stratum
**Evidence:** audited
**Disposition:** stock

For normalized maps

```text
F(z)=az,      G(z)=bz+1,
```

rational endpoints, a prescribed number `n` of occurrences of `G`, and an
optional regular control language, reachability is decidable.

For `a=p/q` with `|p|≠q`, zero evaluation of any integer digit polynomial at
`p/q` is recognized by a finite carry automaton. If

```text
P(X)=(qX−p)E(X),
```

its digits and carries obey

```text
dₖ=qeₖ₋₁−peₖ.
```

Scanning in the contracting coefficient direction bounds `|eₖ|` by the
maximum digit size divided by `||p|−|q||`. For prescribed `n`, the endpoint
equation has only `n+2` ordered coefficient markers; coincident markers add
and arbitrary gaps encode the unbounded `F`-runs. A finite marker automaton,
the carry automaton, and a DFA for reversed regular control can therefore be
intersected. The cases `a=1` and `a=−1` reduce to equality and parity.

**Scope:** `n` is supplied to the algorithm. This does not decide the
unconstrained union over every translated-letter count.

**Use:** any valuation, height, or congruence argument that restricts `n` to a
finite computable set now yields a terminating affine reachability algorithm.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#fixed-translated-letter-count).

### D2-D06: Private-prime peeling

**Kind:** decidable stratum
**Evidence:** audited
**Disposition:** stock

For

```text
F(z)=az,      G(z)=bz+1,
```

suppose some prime `p` satisfies `v_p(a)=0` and
`β=v_p(b)<0`. In a word containing `n≥1` occurrences of `G`, the first
translation term is the unique least-valued translation term. Its valuation
differs from that of the endpoint term by the constant `v_p(x)+β`.

Outside the critical source shell `v_p(x)+β=0`, the valuation of the target
therefore determines the only possible `n`:

```text
n=(v_p(y)−v_p(x))/β        if v_p(x)+β<0,
n=1+v_p(y)/β               if v_p(x)+β>0.
```

Impossible integers are rejected; `y=0`, `x=0`, and `n=0` are handled
separately. [`D2-D05`](#d2-d05-prescribed-translation-count) decides the
remaining fixed-count instance, including regular control.

If `v_p(b)>0`, reverse the word and conjugate by `u=−bz`. The translated
multiplier becomes `b⁻¹`, and the corresponding noncritical condition is
`v_p(y)≠0`.

**Scope:** the theorem needs a prime absent from the pure multiplier `a` but
present in `b`. It leaves one exact source shell for negative valuation, or
one target shell for positive valuation.

**Use:** peel mixed-prime affine pairs before invoking module or building
machinery. It decides every prescribed endpoint outside the critical shell
without bounding the pure-letter runs.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#private-prime-peeling).

### D2-D07: Bounded valuation orthants

**Kind:** decidable stratum
**Evidence:** audited
**Disposition:** stock

Let finitely many rational affine maps `fᵢ(z)=aᵢz+bᵢ` preserve a common
bounded rational interval. Suppose that at every prime the weights

```text
−v_p(a₁), …, −v_p(a_k)
```

have one weak sign. Then rational point-to-point reachability is decidable,
including under regular control.

For nonpositive slope weights, denominator weight never exceeds the maximum
of its current value and the translation weights. For nonnegative slope
weights, once the current weight exceeds every translation weight, it cannot
decrease. A successful path therefore has an effective denominator bound at
every input prime. Rational affine operations introduce no new denominator
primes, and a bounded interval contains only finitely many rationals with a
fixed denominator bound. The problem reduces to finite graph reachability.

The hypotheses are effective: rowwise valuation signs are computable, and a
common invariant rational interval is a rational linear-feasibility problem.
For example,

```text
z↦(2/3)z,      z↦(4/5)z+1/5
```

is covered on `[0,1]` despite multiplicatively independent slopes.

**Scope:** boundedness is essential to finiteness. Incompatible valuation
signs at even one prime remain outside the theorem.

**Use:** this is the first audited mixed-prime affine stratum beyond the
common-multiplier and single-base records.

**Source:** the deterministic denominator-weight precursor is
[`bournez-kurganskyy-potapov-2018-piecewise-affine-reachability.md`](references/bournez-kurganskyy-potapov-2018-piecewise-affine-reachability.md).
The nondeterministic regular-control theorem is proved in
[`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#bounded-valuation-orthants).

### D2-D10: Real-trap exterior

**Kind:** decidable stratum
**Evidence:** formalized reduction; audited decision corollary
**Disposition:** stock

Every critical-shell block is the increasing real contraction

```text
T_m(u)=1/5+(3/5)(2/3)^m u.
```

Lean proves that the closed interval `[1/5,1/2]` is invariant under every finite schedule. The
zero-wait block `T₀(u)=1/5+(3/5)u` is extremal on both exterior components. If a schedule `w`
sends `x` to `y>1/2`, then `x>1/2` and

```text
y−1/2 ≤ (3/5)^|w|(x−1/2).
```

If it sends `x` to `y<1/5`, then `x<1/2` and

```text
1/2−y ≤ (3/5)^|w|(1/2−x).
```

For positive distances `A,D`, `realTrapLengthBound(A,D)` is the first `N` satisfying

```text
(3/5)^N < D/A.
```

The corresponding inequality proves `|w|<N`. This is an exact computable bound obtained by a
terminating rational-power search. Audited [`D2-D05`](#d2-d05-prescribed-translation-count)
then decides the finitely many translated-letter counts below `N`, including regular control.
When the target is a `5`-adic unit, `PeriodicShell.shellPrefixesUnit_iff` makes the intermediate
shell guard automatic.

**Scope:** this decides exact block-schedule reachability to every rational target outside
`[1/5,1/2]`; for a `5`-adic unit target this is exactly guarded shell reachability. It gives no
length bound for a target in the closed trap, including one reached from an exterior source after
entering it. The count-by-count decision step remains audited rather than Lean-formalized. No
full `M₂(3)` decision theorem follows.

**Artifact:** `MixedPrimeDebt.realTrapLengthBound`,
`MixedPrimeDebt.shellRun_mem_realTrap`, `MixedPrimeDebt.shellRun_above_half_envelope`,
`MixedPrimeDebt.shellRun_above_half_length_lt_bound`,
`MixedPrimeDebt.shellRun_below_one_fifth_envelope`, and
`MixedPrimeDebt.shellRun_below_one_fifth_length_lt_bound` in
[`MixedPrimeRealTrap.lean`](MatrixMortality/MixedPrimeRealTrap.lean).

**Use:** remove both real exterior components before attacking the variable-schedule critical
shell. Real contraction and monotonicity leave exactly the recurrent target interval
`[1/5,1/2]`; further progress inside it must use arithmetic or exact address structure.

**Next:** intersect the fixed-source pre-exit relation with targets in `[1/5,1/2]` using the
three-adic carrier recurrence and `5`-adic address constraints. Do not seek another global real
height drift inside the invariant trap.

### D2-M01: Benchmark critical shell

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

The benchmark

```text
z↦(2/3)z+1,      z↦(3/5)z+1
```

is conjugate by `h(z)=15−5z` to

```text
F(z)=(2/3)z,      G(z)=(3/5)z+1.
```

Private-prime peeling at `p=5` decides every original source satisfying
`v₅(3−x)≠0`. A second chart and reversed peeling at `p=2` decide every target
satisfying `v₂(6y−15)≠0`. Only the endpoint shell

```text
v₅(3−x)=0,      v₂(6y−15)=0
```

survives both tests.

In normalized coordinates, write a critical state as `5u` with `v₅(u)=0`.
A block `F^mG` remains critical exactly when

```text
T_m(u)=(1+3u(2/3)^m)/5
```

is a `5`-adic unit. Its first guard digit forces odd `m` when `u≡2 mod 5`,
even `m` when `u≡3 mod 5`, and forbids continuation for residues `1,4`.
Once a path leaves the shell, it cannot return. [`D2-O05`](#d2-o05-universal-exit-suffix-collapse)
sharpens private-prime peeling: every fixed target permits at most two nonempty suffix lengths
after any exit, and [`D2-D05`](#d2-d05-prescribed-translation-count) decides both.

**Scope:** the guarded maps describe every maximal shell-preserving prefix.
They do not yet decide the infinite union of possible exits. This corrects the
stronger claim that the benchmark had been reduced to a self-contained shell
reachability problem.

**Use:** concentrate the benchmark attack on an effective representation of
reachable critical states together with accepting exits. [`D2-O02`](#d2-o02-critical-shell-periodic-saturation)
rules out residue-only exclusion: a decision representation must synchronize the `5`-adic
carry with the `2`- and `3`-exponents or rational height.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#critical-shell-dynamics).

**Next:** [`D2-D10`](#d2-d10-real-trap-exterior) removes targets outside `[1/5,1/2]`.
Represent the exact shell-prefix and accepting-exit relation from a specified rational source
inside that closed trap, or construct a higher-period rational rewrite family with an
all-other-waits exclusion theorem.

**Issue:** [#7, Formalize affine peeling and decide the `M₂(3)` benchmark
shell](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/7).

### D2-O01: Canonical Collatz reachability is not automatic

**Kind:** obstruction
**Evidence:** external theorem
**Disposition:** active

For odd integers `q≥3` and `d≥1`, let

```text
T_{q,d}(n)=n/2          when n is even,
T_{q,d}(n)=(qn+d)/2     when n is odd,
```

and let `R(x,z)` mean that `z` is some iterate of `x`. Dhiman--Pandey prove
that, for every odd pair satisfying

```text
q+d=2^s,
```

the full binary relation `R` is not first-order definable in Büchi arithmetic
`⟨ℕ,+,V_q⟩`. Equivalently, no finite automaton recognizes the standard
synchronous base-`q` encoding of `R`. The theorem includes `T_{3,1}`.

The proof extracts the powers of two from a hypothetical definition of `R`
using reachable orbit floors, then contradicts Cobham's theorem. It neither
embeds universal computation nor assumes the Collatz conjecture.

**Scope:** this is an automaticity obstruction, not an undecidability theorem.
It does not exclude fixed-target unary slices, annotated or redundant
encodings without a finite-state projection to the canonical one,
asynchronous transducers, pushdown or counter machines, or arbitrary decision
algorithms. The source does not cover parameters outside `q+d=2^s`.

**Use:** retire any proposal that represents the full two-variable Collatz
reachability relation by an ordinary synchronous finite automaton in its
canonical base. A finite-nucleus decision attack must use a genuinely richer
annotation, a restricted slice, or a stronger machine model.

**Source:**
[`dhiman-pandey-2026-collatz-reachability-nondefinability.md`](references/dhiman-pandey-2026-collatz-reachability-nondefinability.md).

**Next:** test whether the fixed-target GPI₂ slice remains nonautomatic, and
whether a finite annotated representation would project back to the forbidden
full relation.

### D2-O02: Critical-shell periodic saturation

**Kind:** obstruction and rewrite seed
**Evidence:** formalized core; audited strengthening
**Disposition:** active

For

```text
q_m=3(2/3)^m,      T_m(u)=(q_m u+1)/5,
```

every nonempty finite wait schedule `w=(m₀,…,m_(n−1))` has a rational periodic orbit wholly
inside the `5`-adic unit shell. If

```text
T_w(u)=(Q_n u+C_n)/5^n,
Q₀=1, C₀=0,
Q_(j+1)=q_(m_j)Q_j,
C_(j+1)=5^j+q_(m_j)C_j,
```

then `Q_n`, `C_n`, and `5^n−Q_n` are `5`-adic units, and

```text
u_w=C_n/(5^n−Q_n)
```

is the required fixed point. Backward inversion
`u_j=q_(m_j)^−1(5u_(j+1)−1)` proves that every cyclic phase is a unit. Lean proves this for an
arbitrary finite list of rational `5`-unit scales before specializing to the benchmark.

For the same schedule, let `λ_w=Q_n/5^n`. Lean proves

```text
T_w^k(u)−u_w = λ_w^k(u−u_w),
v₅(T_w^k(u)−u_w)=v₅(u−u_w)−kn.
```

Hence a rational source `u≠u_w` can follow repeated copies of `w` inside the unit shell only
when `kn≤v₅(u−u_w)`. Fixed-block pumping is computably bounded away from the unique periodic
source, even though varying rational schedules can be aperiodic.

The varying-schedule valuation topology is now exact inside every uninterrupted negative
`3`-adic chamber. The carrier is rational, not implicitly integral: write

```text
u=c/3^d,      d>0,      v₃(c)=0.
```

A wait `m` remains in the chamber precisely with positive next depth, and then

```text
d'=d+m−1,      c'=(2^m c+3^d')/5.
```

The sole exit is the boundary `d=1,m=0`. In reverse, a target `c'/3^d'` has the complete
predecessor fan

```text
m=0,…,d',      d=d'+1−m,      c=(5c'−3^d')/2^m.
```

Lean proves both completeness and pairwise distinctness. If `v₅(c')=0` as well, every displayed
predecessor carrier has `v₅(c)=0`, so all `d'+1` branches remain in the critical shell. Thus
bounded reverse branching is false uniformly across depths even though each individual fan is
finite.

For an arbitrary uninterrupted schedule, Lean executes the same carrier recurrence and proves
the Łukasiewicz balance

```text
d_end+length=d_start+sum(waits).
```

Its affine slope is `3^length(2/3)^sum(waits)/5^length`. Hence fixed endpoint depths and fixed
length determine the slope. Two such bridges which agree at one rational source agree globally;
within-length point collisions are exactly affine-map relations and belong to the existing raw
kernel. Only cross-length carrier equality can create a genuinely source-specific collision.

That collision has a complete affine normal form. Write a schedule map as `a_wu+b_w`. Lean
proves for every nonempty `w` that

```text
v₅(a_w)=v₅(b_w)=−|w|.
```

Schedules of unequal lengths have unequal slopes and therefore one collision source

```text
u_(w,v)=(b_v−b_w)/(a_w−a_v).
```

The two differences are each governed by the longer schedule's strictly smaller valuation, so
`v₅(u_(w,v))=0`. Hence source-shell exclusion cannot prune any cross-length pair. This does not
make every collision a legal target witness. Its common output is exactly

```text
y_(w,v)=(a_w b_v−a_v b_w)/(a_w−a_v),
```

and Lean proves it is a unit exactly when

```text
v₅(a_w b_v−a_v b_w)=−max(|w|,|v|).
```

The two determinant terms each have valuation `−|w|−|v|`, so acceptance requires exact
cancellation through the shorter schedule length.

The one-gap debt-bridge slice has a sharper normal form. Suppose `short` and `long` remain in the
negative `3`-adic chamber, begin and end at the same depths, and
`|long|=|short|+1=n+1`. Balance forces

```text
a_long=(2/5)a_short.
```

Put `C_w=5^|w|b_w`. This is a rational `5`-unit for every nonempty schedule and obeys the exact
suffix recurrence

```text
C_(m::w)=3^|w|(2/3)^sum(w)+5C_w.
```

In particular the newly prepended wait does not enter the cleared offset. Lean reduces the
common target and its acceptance condition to

```text
y=(C_long−2C_short)/(3·5^n),
y is a 5-unit  ↔  v₅(C_long−2C_short)=n.
```

The equation is necessary and sufficient, but it is not yet an algorithm: the suffix recurrence
has unbounded length and varying powers. Nor is its right side automatic. The exact debt-safe
pair

```text
[4] versus [0,5],   depth 2 → depth 5,   2/9 ↦ 55/243
```

has a `5`-unit collision source but target valuation one. Its cleared offsets overcancel beyond
the required shorter length.

The one-bit `3`-adic carrier orientation is saturated rather than decisive. Lean checks the two
unit-target collisions

```text
[1]  versus [1,1]    at 1/3 ↦ 1/3,
[1]  versus [1,2,0]  at 19/42 ↦ 8/21.
```

At depth one the first carrier is congruent to `1` modulo three; the second source and target
carriers are congruent to `−1`. All displayed endpoints are `5`-adic units. The orientation is a
lawful within-chamber invariant, but both of its values support cross-length accepted collisions.

Every fixed infinite schedule has a unique orbit in `ℤ₅×` because the inverse branches contract
by `1/5`; a periodic schedule's coded orbit is rational by the displayed formula. At every
finite precision, the transition relation is maximal: for `k≥1`, each admissible source modulo
`5^(k+1)` and each unit target modulo `5^k` determine one wait modulo `2·5^k`. The rational
one-step fixed points

```text
x_m=(5−q_m)^−1
```

are dense in the two admissible cylinders `u mod 5∈{2,3}`. Their internal transition graph is
nevertheless rigid:

```text
T_k(x_m)=x_n  ↔  k=m=n  or  (m,n,k)=(0,1,2).
```

The benchmark action is nevertheless nonfree at higher depth. A published affine identity gives
the distinct schedules

```text
w=[10,2,2,0,0,0,0,0,0,0,0,0,1],
v=[0,0,1,2,0,2,1,1,2,0,6,0,0]
```

with `T_w=T_v` globally. Lean checks the affine equality, equality of their rational periodic
points, and unit membership at every phase of both cycles. This is a guarded relation at the
common periodic source. More strongly, all phases of any shell schedule are units exactly when
its output is a unit. Since the two sides have the same output, substitution preserves every
intermediate shell guard in every word context. Lean checks this contextual law.

The raw alphabet is the canonical rewrite owner. Lean factors every boundary-shifted schedule
pair as the single raw context `T D^last _ D^first` and checks the `z=5u` conjugacy between raw
words and shell schedules. With `D<T`, orient every equal-length balanced raw relation from its
lexicographically larger side to its smaller side. This proves termination, but not confluence:
the published rule has two nonjoinable self-overlap critical pairs. The checked finite basis
consists of the published length-27 relation, the length-29 base member of an infinite family,
and three independent length-30 relations. It has 45 proper critical overlaps, all nonjoinable,
although no critical overlap occurs below length 52.

The length-29 rule proliferates. Put

```text
P=D T^10 D^2 T D^2 T,
Q=T^2 D^6 T^2 D^2 T D T D T D^2 T^2 D^2 T.
```

For every `k≥0`, Lean proves that the two distinct words

```text
P D^9 T (D T)^k D^2,
Q T (D T)^k D^2 T^2
```

have the same affine action and common length `29+2k`. The proof computes the entire pump as
`(DT)^k(z)=(2/5)^k z+(10/9)(1−(2/5)^k)`. The `k=0` member is the finite-basis rule; `k=1`
is one of the seven length-31 normal-form collisions found by census.

Prefixing by `T` gives exact shell schedules

```text
[2,1^k,9,2,2,0^9,1],
[0,0,2,1^k,0,2,0,2,1,1,2,0,6,0,0],
```

where powers denote repeated entries. Lean proves their raw factorization, equal action in every
schedule context, identical intermediate-guard domains, and a common rational all-unit cycle for
every `k`.

This nonfreeness survives unit normalization exactly. Lean realizes the raw action by invertible
homogeneous matrices, proves exact matrix-product equality for every odd-family pair, proves the
two sides are permutations, and transports the relation through arbitrary independent generator
scaling. The two sides contain `16+k` dilations and `13+k` translations, so normalization
multiplies both products by one common nonzero scalar.

The apparent infinite schema has a finite cancellative source. In any group, equalities
`AC=BCV` and `ASC=BSCV` force `AS^kC=BS^kCV` for every `k`: the first isolates the conjugate
`CVC⁻¹`, and the second proves that it commutes with `S`. Lean proves the generic pump and the
exact odd-word factorization. This does not contract the positive rewrite system, where
cancellation is unavailable, and it does not shorten a witness: every family member preserves
both length and letter content.

Exact enumeration of all `2^n` raw words finds no relation outside this basis through length 30.
At length 31 the five-rule census finds seven independent normal-form collisions. One is now the
formal `k=1` family member; the remaining six are computational evidence, not theorem claims.
The maintained checker additionally verifies that the family instances `k=1,…,11` have two
irreducible sides. Since their lengths are at most 51 and the first critical overlap has length
52, they lie outside the five-rule congruence.
The checked finite basis is therefore a reduction accelerator, not a complete presentation of
the affine kernel.

Rationality does not restore rigidity. From every admissible rational source, apply the `k=1`
transition theorem recursively with a chosen next residue. Each legal wait class is modulo ten,
so it has representatives beyond any prescribed bound. Choosing strictly increasing
representatives gives an aperiodic wait schedule whose entire orbit remains rational and in the
unit shell; representatives can also be chosen to avoid every earlier state.

**Scope:** Lean checks the finite rational all-phases cycle, the distinct published schedules,
their affine equality in arbitrary contexts, their common guarded periodic source, exact
repeated-block displacement and unit bounds, the exact two- and three-adic walls, the complete
negative-depth predecessor fan, arbitrary debt-safe schedules and their balance, and
same-length collision rigidity; it also checks the unique unequal-length collision source, its
automatic source-unit theorem, the adjacent-length cleared-offset criterion and rejected target,
both carrier-orientation examples, contextual guard preservation,
and the raw/shell
conjugacy, the contextual boundary factorization, the infinite
odd-length raw kernel family, its guarded contextual cycles, exact homogeneous equality under
every independent generator scaling, its two-seed group pumping law, and three independent
length-30 relations. Infinite-schedule
completion, finite-precision completeness,
the rational aperiodic construction, density, period-one single-wait rigidity, Knuth–Bendix
critical-pair census, and exhaustive raw-word census are audited. The result does not decide exact
target or accepting-exit reachability from a specified source. Point collisions from a fixed
rational source may also identify distinct affine maps.

**Artifact:** `MixedPrimeKernel.wordAction_cassaigne`,
`MixedPrimeKernel.wordAction_kernelOddFamily`, `MixedPrimeKernel.kernelOddFamily_ne`, the three
`wordAction_kernel30*` theorems,
`MixedPrimeNormalization.wordProduct_scaledAffineGenerator_kernelOddFamily`,
`MixedPrimeNormalization.scaledAffineGenerator_not_injective`, and
`MixedPrimeNormalization.wordProduct_kernelOddFamily_of_zero_one`,
`PeriodicShell.shellPeriodicCycle`, `PeriodicShell.shellPrefixesUnit_iff`,
`PeriodicShell.shellRun_eq_wordAction`, `PeriodicShell.shellRun_benchmarkRelationShift`,
`PeriodicShell.benchmarkRelationContextGuard`, `PeriodicShell.benchmarkRelationCycle`,
`PeriodicShell.kernelOddScheduleContextGuard`, `PeriodicShell.kernelOddScheduleCycle`, and
`PeriodicShell.shellRun_repeat_unit_bound`, together with
`MixedPrimeDebt.shellStep_debtState_eq_iff`, `MixedPrimeDebt.debtPredecessor_fan`,
`MixedPrimeDebt.debtPredecessor_state_injective`, `MixedPrimeDebt.shellRun_debtSafe`,
`MixedPrimeDebt.debtRunDepth_balance`, and
`MixedPrimeDebt.debtSafe_sameLength_collision_global`,
`MixedPrimeDebt.collisionSource_eq_of_shellRun_eq`,
`MixedPrimeDebt.collisionSource_fiveUnit`,
`MixedPrimeDebt.collisionTarget_fiveUnit_iff`,
`MixedPrimeDebt.shellOffset_cons`,
`MixedPrimeDebt.adjacentDebtBridge_slope`,
`MixedPrimeDebt.adjacentDebtBridge_collisionTarget_fiveUnit_iff`,
`MixedPrimeDebt.adjacentDebtBridge_targetOvercancellation`,
`MixedPrimeDebt.positiveOrientation_crossLengthCollision`, and
`MixedPrimeDebt.negativeOrientation_crossLengthCollision`, in
[`MixedPrimeKernel.lean`](MatrixMortality/MixedPrimeKernel.lean),
[`MixedPrimeNormalization.lean`](MatrixMortality/MixedPrimeNormalization.lean),
[`PeriodicShell.lean`](MatrixMortality/PeriodicShell.lean),
[`MixedPrimeDebt.lean`](MatrixMortality/MixedPrimeDebt.lean) and
[`MixedPrimeDebtBoundary.lean`](MatrixMortality/MixedPrimeDebtBoundary.lean), with the source record in
[`cassaigne-nicolas-2012-semigroup-freeness.md`](references/cassaigne-nicolas-2012-semigroup-freeness.md)
and the exact census/critical-pair certificate in
[`audit_mixed_prime_kernel.rs`](tools/audit_mixed_prime_kernel.rs). The full arithmetic audit is
[`m32-gpi2-residue-blindness-2026-08-30.md`](audits/m32-gpi2-residue-blindness-2026-08-30.md).

**Use:** reject state-independent finite forbidden wait blocks, residue-only bounded `5`-adic
exclusion, eventual shell exit or periodicity, unbounded pumping of one fixed schedule away from
its periodic point, valuation-only uniformly bounded reverse fanout outside the positivity
restriction of [`D2-S04`](#d2-s04-real-trap-ternary-predecessor-nucleus), source-specific
collision mechanisms at one fixed debt-bridge length, cross-length source-shell exclusion, the
one-bit `3`-adic carrier
orientation as a global separator, automatic target acceptance from source unitality, universal
strict state-height drift, and a compiler whose period-one configurations must remain in that set
after every single wait. Also
reject the hope that unit normalization restores a free action or that the odd family supplies a
strict shortening pump. The live information is exact fixed-source endpoint equality across the
ordered schedule and a parametric description of the positive affine congruence beyond its
cancellative envelope.

**Next:** classify the three length-30 relations and six residual computational length-31
relations into even-length or further parametric families, distinguishing new group relations
from positive-congruence phenomena. For debt-safe prefixes, census affine-map equality within
each length and source-specific collisions only across lengths. Then attack cross-length carrier
equality against the fixed source. In the adjacent-length slice, decide or saturate the exact
cleared-offset equation while retaining the target; `D2-O03` shows that source equality and
acceptance alone are saturated. Then attack chamber exits and reentries, residual stabilizers,
and accepting exits without assuming a canonical rewrite normal form.

### D2-O03: Fixed-source adjacent saturation

**Kind:** obstruction and fixed-source family
**Evidence:** formalized
**Disposition:** active

One rational source supports an exact parametric family of adjacent-length collisions inside the
negative `3`-adic debt chamber. For every `m≥0`, the distinct schedules

```text
short_m=[1,m+2],      long_m=[3,1,m]
```

are debt-safe from depth one to depth `m+2`, have lengths two and three, and satisfy

```text
collisionSource(short_m,long_m)=43/24,
T_short_m(43/24)=T_long_m(43/24)=(11(2/3)^m+9)/45.
```

Every terminal wait `m=10k` is accepted. After clearing the power of three, the target numerator
is

```text
N_k=11·2^(10k)+9·3^(10k).
```

Modulo `25`, both `2^10` and `3^10` equal `24`, so

```text
N_k ≡ 20·24^k  (mod 25).
```

Consequently `5∣N_k` and `25∤N_k`; Lean proves the exact statement `v₅(N_k)=1`, including
`k=0`. Division by the target denominator, whose valuation is also one, leaves a `5`-adic unit.
Because a unit final phase is equivalent to unit membership at every schedule prefix, both sides
are accepted shell paths. Their debt depths remain positive by the displayed endpoint theorem.

The targets are pairwise distinct. The base `2/3` is positive and not one, hence its natural
powers are injective; the affine target formula preserves that injectivity. Thus this family
cannot cycle or pump one fixed target.

The family also survives the complementary endpoint shell from private-prime peeling. If `u_m`
is its normalized target, Lean proves

```text
v₂(1−2u_m)=0.
```

Under `u=3−y_original`, this is exactly `v₂(6y_original−15)=0`. The proof writes
`1−2u_m=(27−22(2/3)^m)/45`: the second numerator term has positive `2`-adic valuation, while
`27` and `45` are units. Hence the entire collision ray, not only the accepted `m=10k`
subfamily, lies on the two-adic target pole.

Fixed-target intersection with this ray is decidable without search. For a prescribed rational
target `y`, define

```text
m_y=max(0,v₂((45y−9)/11)).
```

Lean proves

```text
∃m, (11(2/3)^m+9)/45=y
↔ (11(2/3)^m_y+9)/45=y.
```

If a witness exists, the displayed transformed target equals `(2/3)^m`, whose `2`-adic
valuation recovers `m`; the converse uses `m_y` directly. Thus no infinite fixed-target
subfamily survives, and this one parametric-ray intersection is completely effective.

**Scope:** the theorem gives one fixed source, infinitely many accepted chamber-contained
cross-length collisions, and unbounded terminal waits and raw-word lengths. The shell schedule
lengths remain two and three. The target varies injectively with `m`, so this does not decide
fixed-target reachability outside the ray, accepting-exit reachability, or `M₂(3)`. It does not
classify all adjacent bridges or all accepted residue classes. Meeting the endpoint pole is only
a necessary hard-shell condition, not a mortality witness.

**Artifact:** `MixedPrimeDebt.fixedSourceAdjacentFamily`,
`MixedPrimeDebt.fixedSourceAdjacentFamily_target_injective`,
`MixedPrimeDebt.fixedSourceAdjacentFamily_targetPole`,
`MixedPrimeDebt.fixedSourceAdjacentFamily_target_exists_iff`,
`MixedPrimeDebt.fixedSourceAdjacentFamily_ten_mul_numerator_mod`,
`MixedPrimeDebt.fixedSourceAdjacentFamily_ten_mul_numerator`, and
`MixedPrimeDebt.fixedSourceAdjacentFamily_ten_mul_accepted` in
[`MixedPrimeDebt.lean`](MatrixMortality/MixedPrimeDebt.lean).

**Use:** reject any proposed bound on accepted waits or raw witness length that depends only on
the fixed rational source and continued residence in one negative-depth chamber. Fixed-source
equality and target acceptance are both saturated; a decision argument must retain the specified
target or an accepting exit condition.

**Next:** the target-pole intersection and the ray's own fixed-target query are closed. Record
[`D2-O04`](#d2-o04-forced-exit-surface) decides every controlled continuation after the forced
exit. Seek other adjacent collision rays or reachable pre-exit families not conjugate to this one.

### D2-O04: Forced-exit surface

**Kind:** obstruction and decidable continuation cone
**Evidence:** formalized reduction; audited decision corollary
**Disposition:** active

The accepted `D2-O03` targets cannot take one more shell-preserving block. Put

```text
u_k=(11(2/3)^(10k)+9)/45,
E(k,r)=T_r(u_k).
```

For every `k,r≥0`, Lean proves

```text
v₅(E(k,r))=−1.
```

The proof clears the denominator and shows that the exit numerator has valuation exactly one.
Modulo `25` it is

```text
5·24^k·(4·2^r+3·3^r).
```

The final factor is nonzero modulo five in both parity classes of `r`, so it contributes no
additional factor of five. Every later shell block remains outside the critical shell and lowers
the valuation once more: a tail `w` has valuation `−1−|w|`. Thus these are genuine forced exits,
not merely endpoints at which the present schedules stop.

The exit surface has an exact two-adic coordinate law

```text
75E(k,r)−15=(2/3)^r(9+11(2/3)^(10k)).
```

The carrier in parentheses has valuation two at `k=0` and valuation zero at every `k>0`.
Consequently `(k,r)↦E(k,r)` is injective. More strongly, membership of a prescribed rational
target `y` requires only two equality tests. Define

```text
r₀=max(0,v₂(75y−15)−2),
r₁=max(0,v₂(75y−15)),
k₁=⌊max(0,v₂(((75y−15)/(2/3)^r₁−9)/11))/10⌋.
```

Lean proves

```text
∃k,r, E(k,r)=y  ↔  E(0,r₀)=y ∨ E(k₁,r₁)=y.
```

The equality tests reject negative valuations, nonmultiples of ten, and every spurious truncated
candidate. In particular no fixed target has an infinite fibre, even after adjoining the first
exit block.

The entire controlled continuation cone is decidable, not only its first exit surface. For a
further shell tail `w`, define

```text
L_y=max(0,−v₅(y)−1).
```

Lean proves that every continuation reaching `y` has `|w|=L_y`, and that its full short-side
schedule from `43/24` has exactly `L_y+3` shell blocks. In raw `F,G` coordinates these schedules
form a regular language: the first wait is one, the second is `2 mod 10`, and the remaining waits
are arbitrary. The fixed block count is the translated-letter count. Therefore the audited
prescribed-count algorithm [`D2-D05`](#d2-d05-prescribed-translation-count), including regular
control, decides whether any such continuation reaches `y`.

**Scope:** this decides the complete continuation cone generated by the `D2-O03` collision ray,
including arbitrary post-exit tails. It does not represent exits from other reachable
shell states or decide whether every relevant benchmark witness can be rewritten into this cone.
No mortality or full `M₂(3)` decision theorem follows.

**Artifact:** `MixedPrimeDebt.fixedSourceAdjacentExitTarget_fiveNegative`,
`MixedPrimeDebt.fixedSourceAdjacentExitTarget_displacement`,
`MixedPrimeDebt.fixedSourceAdjacentExitTarget_displacement_twoValue`,
`MixedPrimeDebt.fixedSourceAdjacentExitTarget_tail_fiveNegative`,
`MixedPrimeDebt.fixedSourceAdjacentExitTarget_exists_iff`, and
`MixedPrimeDebt.fixedSourceAdjacentExitTarget_injective` in
[`MixedPrimeDebt.lean`](MatrixMortality/MixedPrimeDebt.lean), together with
`MixedPrimeDebt.fixedSourceAdjacentContinuationSchedule_run`,
`MixedPrimeDebt.fixedSourceAdjacentExitTarget_tail_length`,
`MixedPrimeDebt.fixedSourceAdjacentContinuation_exists_iff_lengthCandidate`, and
`MixedPrimeDebt.fixedSourceAdjacentContinuation_translate_count` in
[`MixedPrimeExit.lean`](MatrixMortality/MixedPrimeExit.lean).

**Use:** reject an argument that the accepted collision ray can support an infinite fixed-target
fibre by an uncontrolled exit or post-exit tail. The entire continuation cone is reduced to one
fixed-count regular-control query; the remaining infinite seam starts with other pre-exit states.

**Next:** [`D2-O05`](#d2-o05-universal-exit-suffix-collapse) removes arbitrary post-exit tails
from every exit, not only this cone. Classify the reachable pre-exit states and their exit images.

### D2-O05: Universal exit-suffix collapse

**Kind:** structure theorem and decidable suffix reduction
**Evidence:** formalized reduction; audited decision corollary
**Disposition:** active

Write the critical-shell transition as

```text
T_m(u)=(3(2/3)^m u+1)/5.
```

If `u` is a `5`-adic unit and `T_m(u)` leaves the unit shell, Lean proves the exhaustive
classification

```text
T_m(u)=0  or  v₅(T_m(u))=−1  or  v₅(T_m(u))>0.
```

The negative case cannot lie below `−1`: the numerator is a sum of two units, so its valuation
is nonnegative before division by five. A zero or positive exit reaches valuation `−1` after any
one further block. Once negative, each later block lowers the valuation exactly once.

Consequently, let a nonempty suffix `w` continue an arbitrary exit to a fixed target `y`. Lean
proves

```text
v₅(y)=−1−|w|  or  v₅(y)=−|w|,
```

and hence

```text
|w|=max(0,−v₅(y)−1)  or  |w|=max(0,−v₅(y)).
```

These are consecutive target-derived candidates. The empty suffix is the immediate exit itself.
For any fixed exit state and target, the audited prescribed-translation-count algorithm
[`D2-D05`](#d2-d05-prescribed-translation-count) therefore decides the remaining suffix query
using at most two block counts; unrestricted suffix control is regular.

**Scope:** this theorem is uniform over every rational critical-shell state, exit wait, and later
schedule. It does not enumerate the shell prefixes reachable from a fixed source, bound the exit
wait, or decide which resulting exit state can reach the target. The benchmark still quantifies
over an infinite family of pre-exit prefixes and exit images. No full `M₂(3)` decision theorem
follows.

**Artifact:** `MixedPrimeDebt.shellStep_fiveUnit_exit_cases`,
`MixedPrimeDebt.shellRun_fiveUnit_exit_nonempty_tail_value_cases`, and
`MixedPrimeDebt.shellRun_fiveUnit_exit_nonempty_tail_length_cases` in
[`MixedPrimeExit.lean`](MatrixMortality/MixedPrimeExit.lean).

**Use:** remove arbitrary post-exit scheduling from the master obstruction. A decision procedure
need only represent the exact set of shell-preserving prefixes together with their first exit
images; each image has a uniformly finite target-derived suffix query.

**Next:** after [`D2-D10`](#d2-d10-real-trap-exterior), construct an effective normal form,
automaton, or finite union of rational cones for the fixed-source pre-exit relation and its
first-exit image inside `[1/5,1/2]`. The remaining infinite quantifier must be cut before the exit,
not after it.

### D2-O06: Real-trap backward saturation

**Kind:** obstruction and backward saturation
**Evidence:** formalized
**Disposition:** active

The invariant interval left by [`D2-D10`](#d2-d10-real-trap-exterior) is saturated in reverse.
For a rational target

```text
1/5<y≤1/2,
```

put `δ=y−1/5`. Choose `m` so that

```text
(2/3)^(m+1)<(10/3)δ≤(2/3)^m
```

and set

```text
x=δ/((3/5)(2/3)^m).
```

The adjacent-power inequalities give `1/5<x≤1/2`, and direct substitution gives `T_m(x)=y`.
Lean proves this for every rational `y` in the half-open trap. If `y` is a `5`-adic unit, reverse
unitality makes `x` a unit as well. Iteration yields the exact saturation theorem

```text
∀n, ∃x,w, |w|=n,
  1/5<x≤1/2, v₅(x)=0, and T_w(x)=y.
```

Since the excluded lower endpoint `1/5` is not a `5`-adic unit, this covers every guarded target
in the closed real trap.

**Scope:** the source depends on `n`. This kills target-only real or translated-count bounds, not
reachability from one specified source. Together with the fixed-source varying-target family
[`D2-O03`](#d2-o03-fixed-source-adjacent-saturation), it shows that neither endpoint alone can
control witness length. It does not decide simultaneous fixed-source/fixed-target reachability or
`M₂(3)`.

**Artifact:** `MixedPrimeDebt.exists_shellStep_realTrap_predecessor`,
`MixedPrimeDebt.exists_shellStep_realTrap_unit_predecessor`, and
`MixedPrimeDebt.exists_shellRun_realTrap_unit_predecessor_of_length` in
[`MixedPrimeRealTrap.lean`](MatrixMortality/MixedPrimeRealTrap.lean).

**Use:** reject real contraction, target position, or target unitality as a source-independent
bound inside the trap. The surviving invariant must couple the exact fixed source to the ordered
arithmetic address.

**Next:** characterize the intersection of one fixed-source forward orbit with the backward-
saturated guarded trap. Candidate representations must retain `2`/`3` exponent order and the
`5`-adic carry; one-sided endpoint invariants are saturated.

### D2-S04: Real-trap ternary predecessor nucleus

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Real order repairs the globally false bounded-reverse-fan shortcut inside the sole recurrent
interval. For a target `1/5<y≤1/2`, put

```text
τ=(10/3)(y−1/5)
```

and let `c` be the unique exponent bracketed by

```text
(2/3)^(c+1)<τ≤(2/3)^c.
```

The inverse of `T_m(x)=y` is

```text
x=(y−1/5)/((3/5)(2/3)^m).
```

Its real-trap condition is exactly

```text
τ≤(2/3)^m<(5/2)τ.
```

Consequently every real-trap predecessor wait satisfies

```text
c≤m+2  and  m≤c,
```

so `m` is one of `c`, `c−1`, or `c−2`. Lean defines the computable exponent `c` as
`realTrapMaxPredecessorWait(y)` and proves fixed-source one-step reachability equivalent to the
three corresponding rational equalities. The factor `3` is sharp: `y=49/150` has exactly the
three waits `0,1,2`, with respective predecessors `19/90`, `19/60`, and `19/40` in the trap.
Since `shellStep m` is injective, this is an exact ternary bound on predecessor pairs, not only on
wait labels.

**Scope:** outside the real trap, a negative-depth target can still have arbitrarily many
shell-legal predecessors, as proved by [`D2-O02`](#d2-o02-critical-shell-periodic-saturation).
Inside the trap, the complete backward graph is locally finite with branching at most three, but
its depth remains unbounded. Local finiteness gives exhaustive semidecision and finite search at
each prescribed length; it does not decide nonreachability from a fixed source, guarded shell
reachability, or `M₂(3)`.

**Artifact:** `MixedPrimeDebt.realTrapMaxPredecessorWait`,
`MixedPrimeDebt.shellStep_realTrap_wait_window`,
`MixedPrimeDebt.exists_shellStep_realTrap_iff_three_candidates`, and
`MixedPrimeDebt.shellStep_realTrap_wait_window_sharp` in
[`MixedPrimeRealTrap.lean`](MatrixMortality/MixedPrimeRealTrap.lean).

**Use:** replace the unbounded debt-chamber predecessor fan by an exact ternary inverse tree after
intersecting with the real survivor. The remaining obstruction is depth, not local branching.

**Next:** find a target-dependent height or congruence making the ternary inverse tree finite up
to equivalence, or exhibit a fixed-source recurrent branch that defeats every finite nucleus.

### D2-S05: Fixed-source real-trap rays

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

The target-side ternary window has an exact source-side dual. Write

```text
U(d,μ)=1/5+(3/10)(2/3)^d μ,   2/3<μ≤1.
```

For every wait `m` and source `x∈(1/5,1/2]`, direct normalization gives

```text
x∈(1/3,1/2]   ⇒ T_m(x)=U(m,2x),
x∈(2/9,1/3]   ⇒ T_m(x)=U(m+1,3x),
x∈(1/5,2/9]   ⇒ T_m(x)=U(m+2,(9/2)x).
```

Thus varying the wait changes only the target band depth. Each fixed source has one normalized
mantissa, and one-step membership is a single rational equality at the computable target depth
`realTrapMaxPredecessorWait(y)`, with the lower-depth guard `0`, `1`, or `2` selected by the
source interval. This sharpens the three target-derived candidates of
[`D2-S04`](#d2-s04-real-trap-ternary-predecessor-nucleus) to one candidate once the source is
fixed. The earlier identity
`T_(d−2)(2/9)=U(d,1)` is the lower interval's boundary case, not an isolated ray.

**Scope:** this decides one shell block, not an arbitrary fixed-source shell prefix. After the
first block, its chosen depth changes which of the three source intervals controls the next
mantissa, producing a countable iterated-ray system.

**Artifact:** `MixedPrimeDebt.shellStep_realTrap_upperRay`,
`MixedPrimeDebt.shellStep_realTrap_middleRay`,
`MixedPrimeDebt.shellStep_realTrap_lowerRay`, and the three
`exists_shellStep_realTrap_*_iff_candidate` theorems in
[`MixedPrimeRealTrapAddress.lean`](MatrixMortality/MixedPrimeRealTrapAddress.lean).

**Use:** represent the remaining forward relation by exact depth/mantissa transitions rather than
an unstructured infinite wait alphabet. One transition has no wait branching after the target
depth is known.

**Next:** classify iteration of the three fixed-source ray maps, retaining the active `5`-adic
carry, or find a finite quotient of their depth/mantissa skew product.

### D2-S06: Spectator-prime denominator skeleton

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Let `p` be any prime at which `2`, `3`, and `5` are units. For every shell schedule `w` and
rational state `x`, Lean proves

```text
min(v_p(T_w(x)),0)=min(v_p(x),0).
```

The negative part of `v_p` is the exponent of `p` in the reduced denominator. Therefore every
denominator exponent outside the active primes `2`, `3`, and `5` is invariant through arbitrary
shell execution. The statement does not assume the `5`-adic guard, so it also applies to the
first-exit image. A source and target with different spectator-prime denominator exponents are
unreachable for every schedule.

**Scope:** numerator residues and the active `2`-, `3`-, and `5`-adic coordinates remain
uncontrolled. Equal spectator denominator skeletons are necessary, not sufficient.

**Artifact:** `MixedPrimeDebt.shellRun_spectatorDenominator`,
`MixedPrimeDebt.shellRun_spectatorDenominator_of_ne_active`, and
`MixedPrimeDebt.shellRun_ne_of_spectatorDenominator_ne` in
[`MixedPrimeSpectator.lean`](MatrixMortality/MixedPrimeSpectator.lean).

**Use:** reject all endpoint pairs whose prime-to-30 denominator skeletons differ before entering
the critical-shell search. The unresolved arithmetic is supported on the active primes plus
numerator carry.

**Next:** combine the invariant spectator skeleton with
[`D2-S05`](#d2-s05-fixed-source-real-trap-rays) and seek an exact classifier for the remaining
active-prime depth/mantissa system.

### D2-S07: Period-ten shell guard

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For every `5`-adic unit source `x`, the one-step shell guard is exactly periodic in the wait:

```text
v₅(T_(m+10)(x))=0  ↔  v₅(T_m(x))=0.
```

The proof uses the exact valuation

```text
v₅((2/3)^10−1)=2.
```

Consequently `T_(m+10)(x)−T_m(x)` has valuation one. Adding or subtracting this positive-shell
perturbation preserves a unit output. Iteration gives period `10k`, and Euclidean division gives
the finite classifier

```text
v₅(T_m(x))=0  ↔  v₅(T_(m mod 10)(x))=0.
```

Combined with [`D2-S05`](#d2-s05-fixed-source-real-trap-rays), every guarded one-step orbit is a
single normalized-mantissa ray whose admitted depths are determined by ten residue tests.

The same calculation exposes the full finite-precision hierarchy. After a fixed tail of length
`ℓ`, changing its incoming wait by

```text
2·5^(ℓ+1)
```

preserves the final unit guard, and every incoming wait reduces modulo this period. The exponent
is sharp uniformly. Every nonempty schedule has an explicit `5`-adic unit zero preimage. For the
schedule `m::tail`, this source reaches zero, whereas changing `m` by only `2·5^ℓ` changes the
final output by a `5`-adic unit. Thus no fixed modulus can classify incoming waits through tails
of all lengths.

The no-go is formal for every positive modulus, not only powers of five. Given `M>0`, take a tail
of length `v₅(M)` and its unit zero preimage. The waits `m` and `m+2M` are congruent modulo `M`;
lifting the exponent gives exactly enough initial precision loss that the first schedule still
outputs zero while the second outputs a unit. Hence every fixed congruence quotient identifies
opposite guard outcomes at some depth.

**Scope:** the result excludes uniform fixed-modulus compression, not finite automata with richer
annotations, unbounded counters, or target-dependent arithmetic. It does not decide fixed-target
reachability. For a fixed unit target the guard is automatic from final unitality, and
[`D2-S08`](#d2-s08-twelve-class-target-depth-collapse) removes this growing precision from the
actual fixed-endpoint seam.

**Artifact:** `MixedPrimeDebt.shellStep_fiveUnit_add_ten_iff`,
`MixedPrimeDebt.shellStep_fiveUnit_add_ten_mul_iff`, and
`MixedPrimeDebt.shellStep_fiveUnit_iff_mod_ten`, the three
`shellRun_tail_fiveUnit_*precisionPeriod*` theorems,
`MixedPrimeDebt.shellRun_shellZeroPreimage`,
`MixedPrimeDebt.shellZeroPreimage_fiveUnit`, and
`MixedPrimeDebt.shellRun_tail_precisionPeriod_sharp`, and
`MixedPrimeDebt.shellRun_fixedModulus_sharp` in
[`MixedPrimeFiveCarry.lean`](MatrixMortality/MixedPrimeFiveCarry.lean).

**Use:** replace every unbounded outgoing guarded-wait test by ten exact residue tests, but reject
any proposed all-depth quotient whose wait modulus is fixed independently of the remaining tail.

**Next:** use the sharp hierarchy only for proposed tails without a fixed unit output. In the
fixed-endpoint problem, attack the exact rational mantissa left by
[`D2-S08`](#d2-s08-twelve-class-target-depth-collapse).

### D2-S08: Twelve-class target-depth collapse

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Write every real-trap target uniquely as

```text
U(d,μ)=1/5+(3/10)(2/3)^d μ,   2/3<μ≤1.
```

The one-step equality has the exact shift law

```text
T_(m+k)(x)=U(d+k,μ)  ↔  T_m(x)=U(d,μ).
```

Consequently, for every fixed source in `(1/5,1/2]`, every `d≥2`, and every `k≥0`, the set of
nonempty shell prefixes reaching `U(d+k,μ)` is nonempty exactly when the corresponding set for
`U(d,μ)` is nonempty. Upward transport adds `k` to the final wait. For downward transport, the
sharp three-wait window forces the final wait to be at least `k`; subtracting `k` then gives the
inverse witness. This proves both directions without assuming a chosen predecessor branch.

Five-adic acceptance on a normalized ray is periodic in the target depth:

```text
v₅(U(d+10q,μ))=0  ↔  v₅(U(d,μ))=0.
```

Because final unitality is equivalent to every intermediate shell guard, guarded nonempty
fixed-source reachability for every `d≥2` reduces to the canonical representative

```text
ρ(d)=2+((d−2) mod 10),   2≤ρ(d)≤11.
```

Depths zero and one remain separate because not every reverse branch has a nonnegative final
wait there. Thus the reduction admits twelve canonical target-depth classes: `0`, `1`, and
`2,…,11`.

**Scope:** the theorem concerns nonempty shell-prefix reachability; the empty schedule is the
separate equality test `source=target`. It does not quotient the normalized mantissa `μ`, which
remains an exact unbounded rational parameter, and it does not decide its reverse orbit. It does
not address a nonunit first-exit target.

**Artifact:** `MixedPrimeDebt.shellStep_realTrapBandPoint_shift_iff`,
`MixedPrimeDebt.exists_nonempty_shellRun_realTrapBandPoint_shift_iff`,
`MixedPrimeDebt.realTrapBandPoint_fiveUnit_add_ten_mul_iff`,
`MixedPrimeDebt.exists_guarded_shellRun_realTrapBandPoint_add_ten_mul_iff`, and
`MixedPrimeDebt.exists_guarded_shellRun_realTrapBandPoint_representative_iff` in
[`MixedPrimeRealTrapDepth.lean`](MatrixMortality/MixedPrimeRealTrapDepth.lean).

**Use:** normalize every guarded fixed-target search to one of twelve depths before reverse
search. Unbounded Archimedean target depth and the period-fifty pole feeder are no longer master
obstructions; only exact mantissa dynamics can distinguish their deep targets after this cut.

**Next:** classify the exact rational mantissa orbit at depths `0,…,11`, combining the spectator-
prime denominator skeleton with the two pole branches near mantissas `2/3` and `9/10`.

### D2-S09: Centered lower-mantissa recurrence

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For a normalized target `U(d,μ)`, every predecessor in the real trap is exactly one of the
following candidates:

```text
source       final wait       availability
μ/2          d                always
μ/3          d−1              d≥1
2μ/9         d−2              d≥2 and μ>9/10.
```

The three sources occupy the disjoint intervals `(1/3,1/2]`, `(2/9,1/3]`, and
`(1/5,2/9]`. Lean proves the converse as well: there is no fourth predecessor. This is the exact
reverse recurrence left by [`D2-S08`](#d2-s08-twelve-class-target-depth-collapse).

The lower branch is the only unbounded depth reset. Write the unit mantissa in lowest terms as
`μ=a/b`, so `gcd(a,b)=1` and `5∤b`, and put

```text
N=10a−9b.
```

If the lower predecessor has normalized depth `n`, its exact new mantissa is

```text
ν = 3^(n−3) N / (2^(n−1)b).
```

All cancellation against the inherited denominator is explicit:

```text
gcd(N,b)=gcd(2,b).
```

Thus no spectator prime, factor of five, or hidden odd factor disappears. The two-adic cases are
complete:

```text
b odd       ⇒ v₂(N)=0,
4∣b         ⇒ v₂(N)=1,
b=2c, c odd ⇒ N=2(5a−9c),
               v₂(N)=1+v₂(5a−9c).
```

The exact normalized transition is

```text
v₂(ν)=v₂(N)−(n−1)−v₂(b),
v₃(ν)=(n−3)+v₃(N)−v₃(b).
```

On the unique secondary wall `b=2c` this contracts to

```text
v₂(ν)=v₂(5a−9c)−(n−1).
```

Hence every anomalous cancellation is concentrated in one centered residual, rather than spread
through the reverse tree.

That residual does not descend. For every `d≥7`, define

```text
a_d = 3^(d−1),
b_d = 10·3^(d−3) − 2^(d−1),
μ_d = a_d/b_d.
```

Lean proves that `μ_d` is reduced, `5∤b_d`, and `9/10<μ_d≤1`. It lies on the secondary wall
with exact unbounded cancellation:

```text
v₂(b_d)=1,
10a_d−9b_d=9·2^(d−1),
v₂(5a_d−9(b_d/2))=d−2.
```

The normalized lower recurrence returns `μ_d` itself, and its real-trap state is its own lower
predecessor:

```text
U(d,μ_d)=2μ_d/9,
T_(d−2)(U(d,μ_d))=U(d,μ_d).
```

The state is a five-adic unit. Every repetition `[d−2]^k` fixes it, and every intermediate
shell phase remains a unit. These guarded self-loops disprove every strict height, odd-part, or
centered-valuation descent asserted uniformly across repeated lower branches. They are the
singleton periodic cycles already guaranteed abstractly by
[`D2-O02`](#d2-o02-critical-shell-periodic-saturation); the new content is their exact reduced
coordinate on the unique [`D2-S09`](#d2-s09-centered-lower-mantissa-recurrence) cancellation wall.

**Scope:** the record gives an exact address and valuation recurrence, not a finite orbit
classifier. The fixed family is recognizable and does not itself create a hard fixed-endpoint
fibre. The upper and middle branches and nonperiodic transitions through the lower wall remain
unbounded exact rational dynamics. The formulas assume a reduced five-adic-unit mantissa when
invoking the gcd statement.

**Artifact:** `MixedPrimeDebt.shellStep_realTrapBandPoint_iff_three_predecessors`,
`MixedPrimeDebt.lowerCenteredNumerator_gcd`, the three
`lowerCenteredNumerator_twoValue_*` theorems,
`MixedPrimeDebt.lowerNormalizedMantissa_twoValue`,
`MixedPrimeDebt.lowerNormalizedMantissa_threeValue`, and
`MixedPrimeDebt.lowerNormalizedMantissa_twoValue_of_exactlyOne_denominator`, together with the
`lowerFixed*` and `shellRun_replicate_lowerFixedPoint*` family, in
[`MixedPrimeRealTrapMantissa.lean`](MatrixMortality/MixedPrimeRealTrapMantissa.lean).

**Use:** split every reduced reverse state first by `v₂(b)=0`, `1`, or at least `2`. Only the
middle case merits a centered-cancellation search; all other lower-branch valuation updates are
rigid. Recognize and quotient the explicit fixed loops rather than attempting a global descent.

**Next:** classify nonperiodic transitions on the secondary wall, or construct a target-dependent
finite quotient that treats the explicit fixed loops as terminal strongly connected components.

### D2-O07: Guarded real-pole reset

**Kind:** obstruction and depth reset
**Evidence:** formalized
**Disposition:** active

The third branch of [`D2-S04`](#d2-s04-real-trap-ternary-predecessor-nucleus) contains the whole
unbounded-depth obstruction. Parameterize the real trap by

```text
U(d,μ)=1/5+(3/10)(2/3)^d μ,   2/3<μ≤1.
```

Lean proves `realTrapMaxPredecessorWait(U(d,μ))=d`. For arbitrary target depth `d≥2`, source
depth `n≥7`, and normalized source mantissa `ν∈(2/3,1]`, put

```text
μ=9/10+(27/20)(2/3)^n ν.
```

Then `2/3<μ≤1` and the exact deepest-branch identity is

```text
T_(d−2)(U(n,ν))=U(d,μ).
```

Thus every target band of depth at least two contains points whose deepest predecessor has any
prescribed depth at least seven and any prescribed normalized mantissa. The branch is countably
full before imposing the shell guard.

The reset is not an artifact of rejected exits. For every `k≥0`, take `n=50k+50`, `ν=1`, and
`d=4`. Both endpoints of

```text
T₂(U(50k+50,1))
  = U(4, 9/10+(27/20)(2/3)^(50k+50))
```

are `5`-adic units. The proof clears their denominators and checks

```text
3^(50k+49)+2^(50k+49) ≡ 20·124^k  (mod 125),
19·3^(50k+49)+4·2^(50k+49) ≡ 75·124^k  (mod 125).
```

The first numerator has valuation one and the second valuation two, exactly cancelling the
respective denominator powers of five. Hence one fixed target depth and one fixed wait support
guarded predecessors of unbounded source depth, although the rational endpoints vary with `k`.
The same deep-band ray has a fixed source inside the real trap:

```text
T_(50k+48)(2/9)=U(50k+50,1).
```

Both endpoints are `5`-adic units, and the targets are pairwise distinct because their exact
maximal predecessor waits are `50k+50`. Thus the sole real survivor admits accepted one-step
witnesses with one fixed source and unbounded waits; only the target varies.
The two other prime coordinates are exact:

```text
v₂(U(50k+50,1))=v₂(T₂(U(50k+50,1)))=0,
v₃(U(50k+50,1))=1−(50k+50),
v₃(T₂(U(50k+50,1)))=−(50k+50).
```

Thus fixed Archimedean target depth four conceals unbounded three-adic debt while the two-adic
wall remains clear. Lean also proves the displayed targets pairwise distinct, so this ray has no
infinite fixed-target fibre.

**Scope:** this refutes a finite-state quotient based only on Archimedean depth, relative branch,
and the `5`-unit bit, and it refutes a source-only wait bound within the real trap. It does not
give one fixed target infinitely many predecessors, an arbitrary guarded mantissa reset, an
infinite prescribed depth word, a counter simulation, or a decision theorem. Exact simultaneous
fixed-source/fixed-target reachability remains open.

**Artifact:** `MixedPrimeDebt.realTrapBandPoint`,
`MixedPrimeDebt.realTrapMaxPredecessorWait_bandPoint`,
`MixedPrimeDebt.shellStep_realTrap_poleBranch_full`, and
`MixedPrimeDebt.shellStep_realTrap_guardedPoleReset`,
`MixedPrimeDebt.shellStep_twoNinths_bandPoint`,
`MixedPrimeDebt.shellStep_realTrap_guardedPoleFeed`,
`MixedPrimeDebt.shellStep_realTrap_guardedPoleFeed_target_injective`,
`MixedPrimeDebt.shellStep_realTrap_guardedPoleReset_twoThreeValues`, and
`MixedPrimeDebt.shellStep_realTrap_guardedPoleReset_target_injective` in
[`MixedPrimeRealTrap.lean`](MatrixMortality/MixedPrimeRealTrap.lean) and
[`MixedPrimeRealTrapReset.lean`](MatrixMortality/MixedPrimeRealTrapReset.lean).

**Use:** concentrate reverse-search invariants on the pole branch near normalized mantissa
`9/10`. A lawful finite nucleus must retain enough exact mantissa or arithmetic information to
separate its full depth resets; depth and shell status alone are saturated.

**Next:** decide whether the guarded pole-reset relation admits arbitrary finite concatenation,
or find a height/congruence that contracts after quotienting its explicit period-fifty ray.

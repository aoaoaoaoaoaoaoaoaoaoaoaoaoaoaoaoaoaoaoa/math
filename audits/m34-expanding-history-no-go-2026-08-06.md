# Expanding-Affine History No-Go Audit

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a750b48-2d60-83ea-a973-53cbf88829c6)

## Enemy Lock

```text
MASTER: prove M₃(4) undecidable.
VICTORY: a total computable four-generator 3 × 3 mortality reduction with a complete
         arbitrary-product converse.
LIVE OBSTRUCTION: uniformly compile the unrestricted paired zero language into three states,
                  or exclude a delimited uniform class strongly enough to force another route.
KILLED LANES: exact rank-three realization; nonerasing three-role macros; rational maps from the
              checked phase-local suffix state; global terminal-history uniqueness; generic
              single-valuedness of history-sensitive phase graphs.
```

## Verdict

The report's main no-go argument is correct for its explicit finite-mode affine-coordinate
hypotheses. A source-dependent expanding positional code cannot uniformly recognize the
universal paired zero language, even if it is noninjective, deliberately collides all terminal
histories, uses mixed signed radices, or carries an arbitrary finite mode graph.

The phrase “carried on finitely many rational curves” is too broad without an additional chart
compatibility hypothesis. The proof requires one cleared integral coordinate whose every chart
transition is either stationary or affine with integer multiplier of absolute value at least
two. Arbitrary rational reparameterizations between curves need not obey the reverse bound. The
durable result uses the exact affine-coordinate hypothesis and rejects the broader slogan.

Lean checks the orbit formula, phase-only degeneracy, reverse bound, finite reverse orbit, exact
finite automaton, regularity, universal paired-zero equivalence, and terminal computability
contradiction. The remaining metatheoretic step is extraction of a `ComputablePred` certificate
from the report's encoded rational normalization data. Its algorithm is the displayed finite
graph search; it is audited rather than implemented in mathlib's primitive-recursion calculus.

## Reset-Affine Normal Form

For source-dependent parameters `rₓ,aₓ,dₓ,z₀`, set

```text
Gₓ = [[rₓ,aₓ,dₓ],     T = [[1, 0,0],
      [ 0, 0,−1],          [0,−1,0],
      [ 0, 0, 1]],         [0, 0,1]].
```

The right-to-left recurrence is

```text
z(ε)=z₀,                 σ(ε)=+1,
z(ty)=z(y),              σ(ty)=−σ(y),
z(xy)=rₓz(y)+aₓσ(y)+dₓ, σ(xy)=−1.
```

`ResetAffineHistory.wordProduct_mulVec_column` proves on every arbitrary control word `y`

```text
G_y (z₀,1,1)ᵀ = (z(y),σ(y),1)ᵀ.
```

No intended-language condition occurs. Empty words, adjacent toggles, toggle-only words, data
read in erase phase, and malformed controls use the same identity.

For a row `(u,v,w)`, `ResetAffineHistory.coefficient_eq` gives

```text
(u,v,w) G_y (z₀,1,1)ᵀ = u z(y) + v σ(y) + w.
```

The report permits a rational conjugacy and a nonzero scalar for each generator and boundary.
Conjugacy cancels between adjacent factors, while the scalars multiply the coefficient by a
nonzero word-dependent factor. They therefore do not change its zero language; the checked
normal form captures the only part used below.

## Toggle Rigidity

The paired decoder satisfies `D(ty)=D(y)`. If a same-zero representation has one zero `y`, then
both phase signs at the same history coordinate vanish:

```text
u z(y) + v σ(y) + w = 0,
u z(y) − v σ(y) + w = 0.
```

Thus `v=0`. This is `ResetAffineHistory.phaseWeight_eq_zero_of_toggle_pair`; it assumes neither
history uniqueness nor injectivity of `z`.

If `u=0`, zero depends only on the two phase values. The empty word and one toggle reach both
phases, so existence is exactly

```text
v+w=0  or  −v+w=0.
```

Lean checks this as `ResetAffineHistory.exists_zero_of_left_zero_iff`. On a mortal same-zero
source, `v=0` and the nonzero empty paired coefficient then force `u≠0`; its zero set is one
history fiber. The finite-orbit proof does not need that sharpening and allows one target point
per mode.

## Reverse Contraction

Clear every denominator in `z₀`, the finitely many target values, and every phase-dependent
translation. The integral recurrence has states `(q,X)` and transitions

```text
(q,X) ↦ (q′,X)             or
(q,X) ↦ (q′,rX+D),  |r|≥2.
```

Choose `N` at least the absolute value of every target and translation. If `Y=rX+D` and
`|Y|≤N`, then

```text
2|X| ≤ |r||X| = |Y−D| ≤ |Y|+|D| ≤ 2N,
```

so `|X|≤N`. Negative radices and mixed radices require no separate case. Stationary transitions
preserve the coordinate. Induction over a reverse path therefore traps every predecessor in

```text
Q × {−N,…,N}.
```

`ExpandingAffineHistory.predecessor_natAbs_le` checks the one-step inequality.
`start_natAbs_le_of_run_natAbs_le` checks its iteration, and `reverseOrbit_finite` proves that the
complete reverse orbit of any bounded target section is finite whenever the mode set is finite.
The theorem allows an instance-dependent number of modes and arbitrarily many accepting paths.

`ClearedResetAffineHistory.machine_step_toggle` and `machine_step_data` instantiate the generic
machine with the paired phase flip and data reset. `ClearedResetAffineHistory.reverseOrbit_finite`
then gives the report's two-phase result directly.

## Exact Finite Automaton

Finiteness of the enclosure alone does not identify the accepted language. The formalization
therefore constructs the automaton explicitly.

`CagedState` refines a mode-coordinate pair by `|X|≤N`. `cagedStep` sends any transition leaving
the box to a dead state. An accepted original run cannot leave and later re-enter: every
intermediate state is a predecessor of the final target and hence lies in the reverse box.
Conversely, every live caged run projects to the original recurrence. Lean checks both directions
as

```text
ExpandingAffineHistory.cagedRun_eq_some
ExpandingAffineHistory.run_eq_of_cagedRun_eq_some.
```

The resulting finite `cagedDFA` recognizes the target language exactly.
`ExpandingAffineHistory.targetLanguage_isRegular` proves regularity. Since the control alphabet
is finite in every compiler under attack, ordinary finite-graph reachability decides whether the
language is empty. Cycles may recognize infinitely many null-history extensions; no witness
bound or terminal-history uniqueness is used.

A chart on which the target row vanishes identically needs no coordinate search.
`ExpandingAffineHistory.modeLanguage_isRegular` constructs its coordinate-forgetting finite-mode
automaton. Empty charts contribute nothing. Thus finite unions of whole, empty, and finite-point
charts have the same decidable nonemptiness boundary.

## Universal Contradiction

For the fixed-width primitive-recursive universal Neary family, define

```text
universalPairedZero(e)
  ↔ ∃y, pairedCoefficient ℚ source.width (source.body e) y = 0.
```

Lean checks

```text
universalPairedZero(e) ↔ CodeHalts(e)
```

as `Undecidability.UniversalNeary.universalPairedZero_iff_codeHalts`. The proof explicitly removes
the empty-word loophole with `pairedCoefficient_nil_ne_zero`, then uses the checked arbitrary
terminal-history theorem and `UniversalNeary.tagHaltsFrom_iff_codeHalts`.

Consequently `universalPairedZero` is not computable. The terminal declaration

```text
Undecidability.UniversalNeary.no_computable_sameZero_predicate
```

rejects every computable predicate with the same sourcewise zero-existence answers. Applying the
finite caged-automaton algorithm to a total reset-affine compiler would produce exactly such a
predicate, contradicting this theorem.

## Scope

The obstruction includes:

- arbitrary source-dependent signed integer radices with absolute value at least two;
- arbitrary rational phase-dependent digits and initial offsets after denominator clearing;
- noninjective history codes and intentional terminal-history collisions;
- arbitrary source-dependent affine target rows;
- finite source-dependent mode graphs, with no uniform bound on their size;
- coordinate-stationary phase transitions and expanding affine data transitions;
- singular normalized data matrices;
- every word in the control free monoid.

It does not include:

- a genuinely two-dimensional projective history orbit;
- an infinite target section not reducible to finitely many coordinate values or whole modes;
- nonexpanding arithmetic with nonzero translations;
- denominator-generating transitions whose cleared multiplier is not fixed integral data;
- Möbius or other rational chart changes not sharing the affine coordinate above;
- a singular or ideal mechanism without a total finite-chart normalization;
- general three-state scalar zero reachability.

The report's “finitely many rational curves” claim is accepted only under the explicit transition
law formalized by `ExpandingAffineHistory`.

## Separator Audit

The contradiction occurs before adjoining a separator. In the two-phase subcase with `u≠0`, the
report's separator audit is nevertheless correct. Scaling each data matrix by `rₓ⁻¹` makes `e₁`
a common fixed column. The normalized reachable boundary column retains nonzero homogeneous
coordinate, and every terminal row satisfies `λe₁=u≠0`. The existing fixed-anchor rank-one
compiler therefore excludes control-only, one-separator, exterior-separator, adjacent-separator,
and malformed-bridge false positives. Independent denominator clearing preserves mortality.

No new separator declaration is retained: `HistoryFracture.lean` already owns the stronger
generic fixed-anchor lift used by this architecture.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Exact reset-affine orbit formula on all controls | promotion | Lean theorem |
| A zero and its leading toggle force a phase-blind row | promotion | Lean theorem |
| The `u=0` case is a two-phase test | promotion | Lean theorem |
| Every bounded reverse orbit of the finite-mode expanding recurrence is finite | promotion | Lean theorem |
| Its bounded-target language is regular | promotion | Lean-constructed DFA |
| Whole target charts reduce to finite-mode regular languages | promotion | Lean theorem |
| Universal paired zero existence is noncomputable | promotion | Lean theorem |
| No total effectively normalized expanding-affine same-zero compiler exists | promotion | checked spine; computability extraction audited |
| The conclusion covers arbitrary finite rational-curve charts | rejected as stated | needs the explicit shared affine-coordinate law |
| General three-state scalar zero reachability is decidable | rejected | outside every proved hypothesis |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every total paired-route compiler whose hidden history is one expanding affine
         coordinate, whose residual control is finite, and whose zero section is finite-mode.
REMAINS: a genuinely two-dimensional projective history orbit; an infinite target section;
         nonexpanding or denominator-generating arithmetic with infinite reverse behavior; a
         singular ideal mechanism; or a different three-role source/direct mortality route.
DISTANCE: construct one of those escapes uniformly from the unrestricted universal source and
          prove its complete separator converse, or kill a broader escape class without reducing
          general three-state reachability to a finite affine graph.
```

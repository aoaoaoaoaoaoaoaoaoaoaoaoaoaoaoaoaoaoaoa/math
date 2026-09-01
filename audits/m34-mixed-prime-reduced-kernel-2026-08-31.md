# M₃(4) Reduced Mixed-Prime Fork-Kernel Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `0bba0f7` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeReducedKernel.lean`](../MatrixMortality/GuardedMixedPrimeReducedKernel.lean)
**Computational owner:**
[`audit_mixed_prime_fork.py`](../tools/audit_mixed_prime_fork.py)

## Verdict

The block-coded mixed-prime route now pays a precise reduced-kernel tax. Every exact realization
of the fixed `bcbc` endpoint language supplies three positive macro words `x,y,z` satisfying

```text
wordAction(y z x y x) = wordAction(x z y x y)
```

on every rational state, with distinct raw sides and reduced length
`N=2|x|+2|y|+|z|`. The data actions have different slopes and fixed points. The toggle fixed
point is uniquely constrained beyond the fixed point of the more contracting data action.

Exact exhaustive search finds no necessary triple for `N≤36`. Thus any exact code in this family
has `N≥37`. This is a computational lower bound, not an unbounded impossibility theorem. `M₃(4)`
remains open.

## Context Cancellation

The full flat and nested fork images share the same encoded prefix and suffix. Every raw `D,T`
word acts bijectively on `ℚ`. Lean proves surjectivity of each word action and cancels both fixed
contexts from equality of the full fork actions. The surviving words are exactly

```text
y z x y x,       x z y x y.
```

If these reduced words were literally equal, restoring the common contexts would contradict the
literal extinction theorem `G3-S10`. Hence they are a genuine equal-action pair. Lean separately
computes both lengths as `2|x|+2|y|+|z|`.

## Degenerate Boundaries

Exact endpoint semantics makes the three macro actions pairwise distinct and forbids one common
fixed point. The reduced equation sharpens these conditions:

- `x`, `y`, and `z` are all nonempty;
- the slopes of `x` and `y` differ;
- the rational fixed points of `x` and `y` differ.

The empty cases are not discarded by convention. Lean closes them from the reduced action
equation. If one data macro is empty, cancellation gives commutation between the other data macro
and the toggle; uniqueness of the nonempty fixed point produces the forbidden common point. If
the toggle is empty, the scalar equation identifies the two data fixed points and again produces
the forbidden common point.

## Exterior Geometry

Write the data slopes and fixed points as `(a,p)` and `(b,q)`, and the toggle data as `(c,r)`.
All slopes lie strictly between zero and one. Direct expansion of the reduced action equation
gives

```text
A(p-r) = B(q-r),
A = (1-a)(1-bc(1-a(1-b))),
B = (1-b)(1-ac(1-b(1-a))),
B-A = (a-b)(1-c).
```

Lean proves `A>0` and `B>0`. Therefore:

- if `b<a`, then `B>A` and `q` lies strictly between `p` and `r`;
- if `a<b`, then `A>B` and `p` lies strictly between `q` and `r`.

Equivalently, the fixed point of the smaller-slope, more contracting data action lies between the
other data fixed point and the toggle fixed point. Lean proves that all nonempty-word fixed points
lie in `[0,5/2]`, so the middle data fixed point is strictly interior. This determines the side of
the toggle before any endpoint or mantissa condition is tested.

## Exact Search

The checker represents an affine action by an exact rational slope and offset. For

```text
X(t)=at+b,   Y(t)=ct+d,   Z(t)=et+f,
```

the fork equation is one linear equation

```text
[ec(1-a+ac)-1]b + [1-ae(1-c+ac)]d + (c-a)f = 0.
```

The first bracket is strictly negative and the second strictly positive for physical nonempty
slopes. Equal data slopes force equal data actions, already forbidden. For every positive length
partition of `N`, the checker chooses one macro as the target, exhausts the other two words,
exhausts every possible target count of `D`, and solves the unique target offset. Prime valuations
make the count determine the slope uniquely.

Target membership is exact. At length at most `16`, all actions of the required length and
`D`-count are hashed. Longer targets split as `u++v`; every `u` is enumerated and every `v` is
hashed, with the required right action recovered by exact affine division. The only numerical
prune is

```text
0 ≤ offset ≤ (5/2)(1-slope).
```

It is necessary: `D` and `T` preserve `[0,5/2]`, and every positive word is a strict contraction
whose fixed point lies in that interval. Final candidates are recomposed and asserted equal by
`Fraction` arithmetic.

The audited command is

```text
/home/main/.local/libexec/cpu-lanes uv run --script \
  tools/audit_mixed_prime_fork.py 27 36
```

The bounded run used checker SHA-256
`79beb13f5924aacb2ce9cae2580b5f916da940c0cd3839371da9a640eec4c31f`. The committed checker,
SHA-256 `d5a905ae14c6d5096ee935caee8f2346b5b2989252de5089bf5aaaf31a5b7972`, adds the independent
backward-normal-form mode below without changing the bounded-length search. A separate identical
search over `N=1,…,26` also returned no candidate. At `N=36`, the search covered `289460`
enumerated-word trials and `3299586` exact target-slope solves. The complete total-length result
is no candidate for any `N≤36`.

## Valuation And Thin Cuts

The affine equation also yields an exact 2-adic sieve. Let `d_w` be the number of `D` letters in
`w`, and assume each macro contains `D`. Slopes and offsets are 2-adic integers because their
denominators are odd, and `v₂(s_w)=d_w`. In the displayed offset equation, the coefficients of
`u_x` and `u_y` have the forms

```text
-1 + s_y s_z[1+s_x(s_y-1)],
 1 - s_x s_z[1+s_y(s_x-1)].
```

The bracketed terms are 2-adic units. Subtracting `u_y-u_x` from the equation leaves only terms
divisible by `2^min(d_x,d_y)`. Hence

```text
v₂(u_y-u_x) ≥ min(d_x,d_y).
```

Modulo two, a word offset records the parity of its leading `T` run until the first `D`.
Consequently the leading `T` runs of `x` and `y` have equal parity. This is a necessary condition,
not a universal contradiction; known mixed-prime kernel relations exhibit nontrivial 2-adic
carries.

The checker also owns an exact backward-normal-form mode. If a candidate target has `d` dilates,
`t` translates, and homogeneous offset numerator `U`, a final letter can be removed only by

```text
final D:  3 | U,  U' = U/3;
final T:  5 | U,  U' = U/5 - 2^d 3^(t-1).
```

Memoized recursion explores both lawful predecessors. The command

```text
/home/main/.local/libexec/cpu-lanes uv run --script \
  tools/audit_mixed_prime_fork.py thin 3 100
```

exhausts every `x,y` with `1≤|x|,|y|≤3` and every `z` with `1≤|z|≤100`; it finds no admissible
triple. This rectangular cut is independent of the total-length bound `N≤36` and does not extend
that bound to `N≤106`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Common action contexts cancel from the full fork equality | promotion | Lean surjectivity and injectivity |
| Every exact code supplies the reduced equal-action pair | promotion | Lean composition |
| The reduced raw words are distinct | promotion | Lean reduction to `G3-S10` |
| Every macro word is nonempty | promotion | Lean fixed-point obstruction |
| The data slopes and fixed points differ | promotion | Lean affine rigidity |
| The displayed balance and exterior order hold | promotion | Lean rational algebra and positivity |
| The more contracting data fixed point lies strictly inside `[0,5/2]` | promotion | Lean interval invariance |
| If every macro contains `D`, the displayed 2-adic offset bound holds | promotion | exact valuation audit |
| A necessary macro triple exists with `N≤36` | rejected | exact exhaustive search |
| A necessary triple has `|x|,|y|≤3` and `|z|≤100` | rejected | exact backward-normal-form search |
| No necessary macro triple exists at any length | open | no unbounded theorem is claimed |
| A triple at `N≥37` satisfies the endpoint converse | open | the search tests only the fork tax |
| `M₃(4)` follows | rejected | the longer kernel and normalized-mantissa branches remain |

## Formal Validation

The owner module and root import compile warning-free under the repository toolchain. The focused
default namespace linter and Lean LSP report no diagnostics. Publication-facing declarations are
listed in [`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom sets contain only
`propext`, `Classical.choice`, and `Quot.sound`. The checker passes pinned Ruff formatting and
linting, `ty`, its bounded self-check, and the checked thin rectangle. No proof aperture, project
axiom, unsafe declaration, linter suppression, floating-point arithmetic, or external certificate
is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
FORMAL TAX: positive distinct equal-action pair yzxyx = xzyxy.
GEOMETRY: toggle fixed point lies beyond the more contracting data fixed point.
COMPUTATIONAL CUT: reduced length N >= 37.
LIVE ESCAPE: a longer physical triple plus the complete endpoint and mantissa converse.
```

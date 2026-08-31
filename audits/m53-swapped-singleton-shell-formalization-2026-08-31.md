# Swapped Distinguished-Boundary Singleton-Shell Audit

**Date:** 2026-08-31
**Target:** the depth-`β` singleton poles after one distinguished-boundary transfer in the
swapped ternary setter
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** both physical singleton targets are impossible at the exact shell-witness interface

## Statement

Put `ρ=3^β`, `μ=2ρ−1`, and `H=5ρ−1`. After maximal common-suffix cancellation in the
distinguished-boundary depth-`β` shell, the unmatched upper and lower words have equal length
`2β+1`. A prospective singleton pole has normalized equation

```text
C_target Δ + 2ρHμ = 0,       Δ=[A]₃−[B]₃.
```

For target `D_b`, this equation requires

```text
Δ=2(2ρ−1)(5ρ−1)/(18ρ²−40ρ+17).
```

When `β≥3`, hence `ρ≥27`, the quotient lies strictly between one and two and cannot be an
integer. For target `D_c`, the equation is equivalent to

```text
Δ=2μ=4ρ−2.                                              (1)
```

## Carry Classification

Under the swapped nonzero ternary digits, (1) has one carry pattern. There are words `T,z` with
`|T|=β−1` and `|z|=β−2` such that

```text
A=T·00·z·10,       B=T·11·z·01.                        (2)
```

The Lean proof derives (2) by splitting both length-`2β+1` words above and below the `3^β`
place. The low pair is the unique binary pair whose swapped codes differ by two; after its carry,
the high pair is the unique pair whose codes differ by four. Injectivity of the nonzero-digit
ternary code identifies both common fronts.

## Physical Extinction

The upper Neary spelling in (2) has a first `b` role after `s` initial `c` roles, where
`0≤s≤β−3`. Its exact prefix is

```text
1^(s+1)·0^β·1^(β−s−2)·10,
```

so the lower carry partner is

```text
1^(s+1)·0^(β−s−2)·11·0^s·1^(β−s−2)·01.                (3)
```

If `s=0`, the first tile carries `b`. Its lower image begins either `0` or `110`, whereas (3)
begins `10`. If `s>0`, the first tile must be `R_c`; after its initial one, the encoded body must
produce the first zero by position `s`. An all-`c` body cannot do this because `|body|≥β−1`. If
the body instead reaches its first `b`, that code contributes `β` consecutive zeros. Position
`β−2` of (3) is already one, while the physical word is still inside that zero run. Both cases
are contradictory.

## Formalization

[`SwappedSetterSingletonShell.lean`](../MatrixMortality/SwappedSetterSingletonShell.lean)
contains the following publication-facing declarations:

- `twoMarkerDiscrepancy_pattern`, the unique carry (2);
- `singletonB_pole_false`, the strict-fraction obstruction;
- `singletonC_pole_iff`, the exact reduction to (1);
- `SingletonShellPoleWitness`, the equal-length physical suffix-cancellation interface;
- `singletonShellPoleWitness_false`, the complete composition with the Neary upper and lower
  languages.

The witness records the actual preceding tile word, target letter, two uncancelled prefixes,
cancelled common suffix, both length equations, both physical factorization equations, and the
exact pole equation. No regular-language approximation replaces either spelling.

Direct Lean elaboration, the project linter gate, and transitive axiom inspection pass without a
proof aperture or warning. The four audited theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Scope

This result closes exactly the distinguished-boundary singleton shell. The surviving first
multi-transfer block `D_c^(β+1)→singleton` enters from a different two-transfer projective state
and does not imply an equal `2β+1` prefix witness. There is therefore no lawful carrier adapter
and no new `MM-S46` theorem. Its separate direct algebraic extinction is `MM-S50`.

The result does not prove that every arbitrary-depth projective state has distinguished-boundary
ancestry. It may be reused whenever such ancestry supplies `SingletonShellPoleWitness`.

## Artifacts

- [`MM-S08`](../SALVAGE.md#mm-s08-swapped-distinguished-boundary-beta-shell)
- [`SwappedSetterSingletonShell.lean`](../MatrixMortality/SwappedSetterSingletonShell.lean)
- [`m53-swapped-setter-2026-07-25.md`](m53-swapped-setter-2026-07-25.md#elimination-of-the-beta-shell)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)

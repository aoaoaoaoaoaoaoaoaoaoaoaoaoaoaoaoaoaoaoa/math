# M₅(3) empty-front backward-chamber audit

## Boundary

This audit concerns one arbitrary physical block immediately before the local `MM-O29`
`D_b;D_c;D_c` backward ray. It proves a first-letter exclusion for the `MM-S104` slope chamber
and a sharper estimate for one literal `(R_c,D_b)` branch. It does not classify every
`c`-leading predecessor or prove global reachability, mortality, or a Lyapunov function.

## Seed ray

For an empty target of width `β=offset+1`, let `U` be its punctuated discarded-prefix code and
let `X` be the exact `D_b` antecedent constructed in `MM-O29`. The encoded target length gives

```text
3^(offset+2) ≤ 2U+1.
```

Two explicit positive polynomial certificates then prove

```text
H < X,       H=5·3^β−1.
```

The proof is uniform in the target letters. No sampled-word premise enters the theorem.

## Physical cut

Write `ρ=3^β`, `r=ρ−2`, and `μ=2ρ−1`. For a physical block with punctuated upper code `P`,
lower code `V`, and upper power `A`, its inverse action on any `X>H` is

```text
f(X)=(P−cA)/V,
c=Hμ/(H+rX),
0<c<3.
```

For `β≥6`, Lean proves

```text
first role letter b  →  ¬(1<f(X)<r/(r−3)).
```

The proof exhausts the relative spelling lengths:

| lower spelling | first tile | result |
|---|---|---|
| shorter than upper | any `b`-letter tile | `f(X)>r/(r−3)` |
| longer than upper | any `b`-letter tile | `f(X)<1` |
| equal | erasure | `f(X)<1` |
| equal | `R_b` | `f(X)>r/(r−3)` |

The inequalities use exact ternary prefix bounds rather than a finite block catalogue.
Consequently every physical predecessor entering the `MM-S104` slope interval is `c`-leading.

## Canonical branch

For body `b c^(β−2)` and block `(R_c,D_b)`, the compiler codes are exactly

```text
P=45ρ²−4ρ−1,
2V=90ρ²−9ρ+7,
A=27ρ.
```

If its backward image `x` is above one, the positive correction in the physical formula and the
code gap yield

```text
(x−1)/x < 1/(80ρ).
```

`deletionCSuccessorSlope_eq` separately records the exact next inverse-`D_c` slope for a
near-diagonal carrier. The audit does not combine these statements into a generic successor
chamber: a valid `MM-S104` carrier can have next slope greater than one. Nor does the slope
interval force a `c`-leading block to equal `(R_c,D_b)`; the remaining classification must use
the exact `3H` gcd channel.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterEmptyFrontChamber.lean`](../MatrixMortality/SwappedSetterEmptyFrontChamber.lean).

The focused module and aggregate umbrella compile without warnings. The namespace passes the
default linters, every public theorem is listed in `AxiomAudit.lean`, the reviewed axiom snapshot
contains only the standard axioms, and the aperture scan is empty. The global linter gate is
currently blocked by unrelated concurrent declarations in `CubicReturnNonPure`, the
`Transverse*` modules, `PeriodicHistory`, `SeparatedTwoCOrbit`, and `TwoStateObstructions`; this
lane does not alter them. The consuming entry points are `physicalEmptyFrontSeed_above_terminal`,
`bLeading_physicalBackwardBlock_avoids_deletionCChamber`, and
`canonicalRcDbBackward_epsilon_lt`.

## Consequence

The contraction ancestry has one fewer colour: `b`-leading blocks are impossible. The remaining
target is arithmetic rather than Archimedean. Pull the `MM-S104` divisibility channel backward
through a `c`-leading block to decide whether a nonempty suffix after `(R_c,D_b)` survives.

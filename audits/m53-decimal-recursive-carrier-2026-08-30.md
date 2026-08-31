# Decimal Setter Recursive Carrier Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** repeated multi-shell resonances have an exact two-unit carrier; the initial
leading-`b` head is impossible, but the generalized carrier enters a compatible last-digit
two-cycle and the upper-length-two branch escapes that digit law

This audit continues the decimal carry after the one-transfer peel. It does not prove
arbitrary-depth projective avoidance or settle `M₅(3)`.

## Exact Carrier

Write one J-fraction block as

```text
u=P/(μ10^m),       v=GV/(Eμ10^m),       T=EP+GV.
```

Represent a peeled projective state by two decimal units:

```text
t=N/(10μD).
```

One transfer has the exact numerator

```text
R=NT−10μGVD,
F(u,v,t)=R/(Eμ10^mN).                              (1)
```

If the following block is a multi-role pole with trace `T₊` and lower code `V₊`, then

```text
RT₊=EμG10^mNV₊.                                    (2)
```

All factors on the right other than `10^m` are decimal units, while `T₊` has shell `(1,1)`.
Consequently

```text
(ν₂(R),ν₅(R))=(m−1,m−1).                           (3)
```

Writing `R=10^(m−1)N'` turns (1) into

```text
F(u,v,t)=N'/(10μ·EN).
```

Thus the next carrier is exactly

```text
(N,D) ↦ (N',EN).                                   (4)
```

`peeledNumerator_multi_shell` proves (3); `peeledStep_factor` proves (4). This is an
all-depth recurrence, not a depth-two approximation.

## Depth-Two Entry

At the distinguished reset, a nonresonant A-to-A false pole forces the first raw discrepancy
to have shell `(m₁−1,m₁−1)`. Suffix exhaustion writes

```text
P₁−V₁=10^(m₁−1)H,
```

where `H` is a decimal unit. Cancelling this suffix from the depth-two trace identity gives

```text
K₂H=10μGV₂T₃.
```

Expanding `K₂` yields the first instance of the recursive carrier:

```text
(HT₂−10μGV₂)T₃=HEμG10^(m₂)V₃.                     (5)
```

`depthTwo_suffix_to_peeled` checks the cancellation and (5) in one theorem.

The raw upper spelling leaves a `β+2`-digit head. `peeledHead_trichotomy` proves its complete
grammar:

```text
b…    : bTag = 1 0^β 1;
c b…  : terminal head = 1 1 0^β;
c c…  : a two-c head.
```

The `bTag` code ends in decimal digit `5`, so it is not a `5`-adic unit.
`bTag_cannot_head_equalDepth` excludes it at every peel depth. The terminal head has code
`G/9` by `terminalHeadWord_code_eq` and returns to the already peeled distinguished reset.
Therefore the genuinely new nonresonant depth-two A-to-A input has a two-`c` head ending in a
decimal unit digit.

## Last-Digit Cycle

For a multi-role block, write `T=10τ`. The emitted residues are

```text
τ≡1,       μ≡7,       G≡3,       V≡7,       E≡7       (mod 10).
```

When `m≥3`, equation (3) makes `100∣R`. Cancelling one factor of ten in (1) forces

```text
N≡7D                                             (mod 10).    (6)
```

The denominator update `D'=EN` and the next copy of (6) then give

```text
D'≡9D,       N'≡3D                              (mod 10).
```

After a second transition the pair returns:

```text
D''≡D,       N''≡7D                             (mod 10).    (7)
```

Lean proves (6) through `peeledNumerator_forces_lastDigit` and the exact period two through
`peeledLastDigit_twoStep`.

This is a no-go for the proposed final-digit closure. The first `N=H` is a raw encoded head,
so its forbidden final digit can kill `bTag`. After one transition, `N'` is the generalized
product residual in (1), not a raw `peeledHeadWord`; residue `3` is lawful. No checked theorem
identifies it with an encoded head, and (7) shows that the unit residues themselves remain
compatible indefinitely.

The upper-length-two case is separate. Equation (3) then gives only one factor of ten, so the
modulo-`100` cancellation used in (6) does not fire. The ordinary-reset two-c chamber does not
apply automatically because a generalized carrier need not lie in its source interval.

## Exact Frontier

The all-depth A-shell state is now the pair `(N,D)`, not a single raw discrepancy head. A
closure must do at least one of the following:

1. prove a structural bridge from the generalized product residual `N'` to a restricted
   suffix language stronger than its unit residue;
2. construct a higher-digit invariant that breaks the period-two unit cycle;
3. kill the generalized upper-length-two transition by a new chamber or arithmetic identity.

Treating every `N'` as another encoded head is invalid. Treating the ordinary length-two
chamber as a generalized-carrier theorem is also invalid.

## Verification

The narrow module build, Lean language-server diagnostics, namespace lint, and selected
transitive axiom snapshots pass without warnings, suppressions, or proof apertures. The
publication-facing declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`,
matching `verification/axioms.txt`.

## Artifacts

- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`DecimalSetterCarry.lean`](../MatrixMortality/DecimalSetterCarry.lean)
- [`DecimalSetterChamber.lean`](../MatrixMortality/DecimalSetterChamber.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s17-recursive-decimal-carrier)

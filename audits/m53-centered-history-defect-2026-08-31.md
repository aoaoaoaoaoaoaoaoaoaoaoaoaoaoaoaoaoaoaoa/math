# Centered-History Defect Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** later swapped-ternary poles differ from the closed first-multi interface by one exact
history-defect term

The shell-free theorem
[`MM-S55`](../SALVAGE.md#mm-s55-physical-role-block-shell-completion) closes every physical pole
in the special two-transfer state produced immediately after the ordinary reset. A later fold
begins from a general homogeneous carrier. This audit determines exactly when that carrier may
be reinterpreted as a fresh raw head and computes the correction when it may not.

## Exact Fold

Put `ρ=3^β`, `μ=2ρ−1`, `H=5ρ−1`, `R=2−ρ`, and `K=RHμ`. For a block `z`, write

```text
A_z=3^m_z,      C_z=RP_z−HV_z.
```

Its centered transfer is

```text
T_z(x,y)=(A_zy, KV_zx+C_zy).                            (1)
```

`CenteredContinuant` stores the four coefficients of the product of these transfer matrices.
Lean proves by induction that applying this continuant is definitionally the same left-to-right
block fold. Both incoming coordinates survive: after a middle block `m`, a prospective target
pole has residual

```text
K C_tV_m x+(C_tC_m+KV_tA_m)y.                           (2)
```

Equation (2) is the exact obstruction to replacing a general carrier by the first-transfer
state.

## Raw-Head Test

Define homogeneous defects

```text
D(x,y)=y−Rμx,
ε_z(x,y)=A_zy−RP_zx.                                    (3)
```

Substituting (1) into (3) and using `C_z=RP_z−HV_z` gives

```text
ε_z(T_z(x,y))=−A_zHV_zD(x,y).                           (4)
```

Every physical role block has `V_z≠0`; also `A_z` and `H` are nonzero. Therefore a completed
block lies on its canonical raw-head ray if and only if the preceding carrier lies on the
ordinary-reset ray. This is both necessary and sufficient. The alternative distinguished reset
does not help: its defect is exactly

```text
D(3,RH)=R²≠0.                                           (5)
```

Thus a sliding-window reuse of `MM-S55` is invalid unless the complete earlier history proves a
genuine projective return to the ordinary reset.

## Pole Correction

For first, middle, and target blocks `f,m,t`, put

```text
L=C_tC_m+KV_tA_m,
E=Pole_t(T_m(A_f,RP_f)).                                 (6)
```

Here `E` is exactly the canonical first-multi residual killed by `MM-S55`. For an arbitrary
carrier `q`, direct expansion of (2) gives

```text
A_f Pole_t(T_mq)=q_xE+Lε_f(q).                          (7)
```

If `q=T_f(s)` and the target residual vanishes, combine (4) and (7), then cancel the nonzero
upper power `A_f`:

```text
s_yE=HV_fL D(s).                                         (8)
```

Equation (8) is the complete later-history correction. There is no second hidden coordinate in
the projective equation. If `D(s)=0` and `s_x≠0`, Lean rescales `s` to the ordinary reset,
transports the zero residual through the nonzero scale, and invokes
`physicalFirstMultiTransfer_pole_false`. Hence any later false pole in this interface must have
nonzero ordinary defect.

The defect recurrence itself is

```text
D(T_zs)=R(P_z−μA_z)s_y−HV_zD(s).                         (9)
```

For a live state, normalize by its denominator coordinate:

```text
δ(s)=D(s)/s_y.
```

Equations (1) and (9) give

```text
δ(T_zs)=[R(P_z−μA_z)−HV_zδ(s)]/[RP_z−HV_zδ(s)].         (10)
```

The same denominator pencil proves that `z` is a pole exactly when

```text
δ(s)=(R/H)(P_z/V_z).                                    (11)
```

The ordinary reset has coordinate zero and the distinguished reset has coordinate `R/H`.
Lean cancels the nonzero physical factors to prove that the threshold in (11) equals `R/H` if
and only if `P_z=V_z`; under the compiler length envelope it then invokes the checked Neary
decoder to obtain `TagHaltsFrom`. Thus terminal equality is exactly the distinguished threshold,
while every false pole is another physical threshold hit of (10).

The entry gap `P_z−μA_z` in (9)-(10) is the exact history datum omitted by shell-only arguments.
It also destroys the simplest real invariant: the singleton `D_c` sends the ordinary reset to
the negative coordinate `R/H`, while `D_b` sends it to the positive coordinate `H/P_Db`.

## Boundary

This audit does not prove that a nonempty physical history never returns to the ordinary ray,
nor does it exclude every nonzero solution of (8). Fixed residue classes are known to saturate
in bounded diagnostics, but those computations do not prove that every finite semantic quotient
fails. The remaining mathematical target is precise: prove threshold avoidance for (10)-(11),
retaining enough Neary suffix ancestry to distinguish terminal equality from a false pole.

## Verification

[`SwappedSetterHistory.lean`](../MatrixMortality/SwappedSetterHistory.lean) contains the centered
state and continuant, exact fold theorem, defect transport, raw-head equivalence, distinguished
reset separation, two-block residual, canonical correction identity, defect recurrence, and
ordinary-return adapter to `MM-S55`. It also contains the normalized recurrence, exact pole
threshold, terminal-threshold equivalence, and singleton sign split. The module builds
warning-free, its namespace passes all default environment linters, and the publication-facing
declarations are listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterHistory.lean`](../MatrixMortality/SwappedSetterHistory.lean)
- [`MM-S55`](../SALVAGE.md#mm-s55-physical-role-block-shell-completion)
- [`MM-S57`](../SALVAGE.md#mm-s57-centered-history-defect-transport)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)

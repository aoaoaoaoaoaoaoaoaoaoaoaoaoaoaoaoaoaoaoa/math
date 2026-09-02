# M₃(2) Jacobi and Prime-Handoff Audit

Date: 2026-08-05

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. In the
rank-`(3,2)` guard, the checked residue is an even-reset-defect primitive execution with unbounded
reduced denominators. The missing theorem must globally amortize the mandatory nonmaximal Smith
steps or construct an orbit which survives them.

## Adjudication

| Submitted claim | Class | Judgment |
| --- | --- | --- |
| the primitive denominator tail obeys the displayed Jacobi recurrence | rejected | the diagonal coefficient and one sign were dropped |
| diagonal similarity removes the content split | restatement | only the corrected off-diagonal products are content-free; the checked endpoint determinant calculus already owns this fact |
| the three normalized transfers have product `−I` only at three unit activities | salvage, culled | the matrix multiplication is correct for the submitted auxiliary transfer, but that transfer is not the guard recurrence |
| constant rational activity has finite semisimple projective order only at `1`, `1/2`, `1/3` | salvage, culled | correct for the auxiliary matrix, but finite order is stronger than one periodic rational ray and has no consuming master theorem |
| a repeated prime passes from reverse content `k` to forward content `h` | rejected | outside fixed scale-reset support, the exact implication is the opposite |
| every height-neutral tail eventually lies on one of those torsion rails | open, ill-posed | the proposed rails do not govern the guard; the original global amortization problem remains |

## Correct Recurrence

For consecutive primitive endpoint reductions, put `q=pᵃ`, `q′=pᵇ`, and

```text
h k = DL(q−1).
```

The already formalized elimination is

```text
q′ˢ h′ t″ = (A + Dqˢ − Lq′)t′ + kt.
```

Thus the associated tridiagonal diagonal is `Lq′−Dqˢ−A`, not `L(q′−1)`. Across one edge the
off-diagonal product is, up to the chosen sign, `DLqˢ(q−1)` and is independent of the split
`h,k`; this limited Jacobi observation is valid. It does not yield the submitted transfer
`N(w)`, its activity formula, or its torsion rails.

There is a second logical gap independent of the wrong coefficient. A product which fixes one
rational solution ray need not be scalar in projective space. Classifying when a transfer has
finite projective order therefore does not classify periodic or height-neutral denominator
tails.

## Reverse Persistence

Let two consecutive primitive reductions have complementary contents

```text
h k   = DL(q−1),
h′ k′ = DL(q′−1),
```

and let `R=A+D−L`. If

```text
d ∣ k,
d ∣ L(q′−1),
gcd(d,LR)=1,
```

then Lean proves

```text
gcd(d,h′)=1,
d ∣ k′.
```

The proof uses no primality or depth assumption. The target denominator of the first step is
coprime to `k`. The reverse endpoint identity gives

```text
L(r′−Rt′)=kX,
```

so `r′≡Rt′ (mod d)`. Since `d∣L(q′−1)`, the next raw denominator is also congruent to `Rt′`
modulo `d`, hence is coprime to `d`. The next forward content cannot absorb any part of `d`, and
the complementary determinant identity forces all of it into `k′`.

Artifact:
`ReturnGuard.PrimitiveEndpointReduction.recurrentBoundaryDivisor_persists` in
[`ReturnGuardContinued.lean`](../MatrixMortality/ReturnGuardContinued.lean).

## Exact Counterexample

The handoff inequality fails inside the even-reset-defect guard stratum. Take

```text
p=3,  s=2,  A=−446,  D=500,  L=56,  R=−2,  q=27.
```

The two primitive reductions

```text
(−2,1) ─[a=3,h=2]→ (2,−1) ─[a=3,h=2]→ (−2,1)
```

hold exactly. In both steps

```text
k = DL(q−1)/h = 364000.
```

The primitive divisor `13` satisfies `13∣q−1`, `13∣k`, and
`gcd(13,pDLR)=1`, yet `13∤h′`. Both structure witnesses and the persistence theorem were checked
by `norm_num` during reconstruction; no example declaration was retained.

This is also a direct falsifier for the submitted recurrence: with denominator signs
`1,−1,1`, its left side is

```text
364000 − 1456 + 729·2 = 364002 ≠ 0.
```

The coefficients arise from lawful guard parameters `center=−223/28` and `reset=27/28`; the
projective endpoint is a bounded-denominator fixed ray, so the example does not enter the live
unbounded residue.

## Wound

```text
MASTER VERDICT: still open
REMOVED: the content-free N(w) torsion reduction and maximal-prime alternation lane
REMAINS: global nonmaximal amortization in an even-R, unbounded-denominator execution
DISTANCE: prove that the gauged v≥2 losses force repetition or a certificate, or construct one coefficient-aligned nonperiodic survivor
```

The theorem sharpens prime transport but does not shorten that final implication. A primitive
factor separated from its next occurrence by smaller waits is transported by an invertible
projective bridge; its next allocation is an incidence condition, already represented by the
exact-order quotient automata, not an alternation law.

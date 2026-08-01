# M₃(2) Fixed-Cusp And Record-Ascent Audit

Date: 2026-08-01

## Source

The audited input was the three substantive replies in the public Pro transcript
`6a6e2ce8-e940-83ea-b8ac-0765fa785970`. The replies were reconstructed in chronological
order before comparing their formulas. Raw prompts and transcript exports remain ephemeral.

## Accepted Core

For the cumulative endpoint pair `(R,β)`, one wait `a` has the exact prequotient

```text
t = R − L(pᵃ−1)β = hβ′.
```

Primitive normalization gives `|h|=gcd(|DR|,|t|)`. Complementary reverse content satisfies
an exact reset-defect factorization and, at a terminal target, the wait-free boundary

```text
k ∣ L(A+D−L).
```

This does not bound the terminal wait: every positive wait has an explicit integral terminal
predecessor. The canonical complete quotient

```text
Zᵢ = −DL Rᵢ₋₁/Rᵢ
```

obeys one generalized continued-fraction recurrence with fixed forbidden cusp `Z=−L`. The wait
is the p-adic approximation depth to the fixed ray `R=Lβ`.

At critical depth `s=2`, two primitive steps with `a≤b` satisfy

```text
p^(a+b)|hh′| ≤
  (|D| + (1+|L|)(|A|+|L|)) H(R,β).
```

The corresponding decoder is a fixed order-three core, whose cube is `−I`, followed by one
wait-dependent shear.

## Repairs

The first report proposed a “full fresh core” after a loss bounded by `Ba`. A later reply
corrected that loss to an unspecified polynomial `B a^κ`; the final reply silently restored
`Ba`. The claimed cyclotomic lower bound and checkpoint propagation therefore have no stable
proof boundary. They were rejected rather than recorded as theorems.

The old denominator-ratio and unit-tail chart duplicated the cumulative numerator recurrence
without improving the hot path. Its published formula had already required a numerator repair.
Those declarations and the superseded cumulative-endpoint audit were deleted. The fixed-cusp
quotient is now the sole continued-fraction presentation.

## Kernel Boundary

Lean checks:

```text
PrimitiveEndpointReduction.content_natAbs_eq_gcd_driftSource_prequotient
PrimitiveEndpointReduction.resetDefect_eq_complement_mul
PrimitiveEndpointReduction.complement_dvd_terminalBoundary
terminalPredecessorPair_step
cumulativeCompleteQuotient_recurrence
cumulativeCompleteQuotient_sub_forbiddenCusp
cumulativeWaitForm_hasValue
PrimitiveEndpointReduction.twoStep_contentBudget
criticalDecoder_factor
criticalDecoderCore_cube
```

The formal result is local and absolute. It does not prove that fresh cyclotomic mass exceeds
height already accumulated before a moving record ascent. The live theorem is a global shear
or active-core amortization principle, not another local cancellation identity.

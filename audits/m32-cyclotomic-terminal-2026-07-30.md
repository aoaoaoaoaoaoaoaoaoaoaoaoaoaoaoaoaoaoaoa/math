# M₃(2) cyclotomic terminal-congruence audit

Date: 2026-07-30

## Claim

For a positive wait `a`, let one integral decoded step be

```text
pˢᵃ m̃ = (A−Lpᵃ)m + Dn,
ñ      = (A−L)m + Dn.
```

Suppose `(m̃,ñ)=g(m′,n′)` with `m′,n′` coprime. For every integer divisor
`d ∣ pᵃ−1`,

```text
d ∣ g
  ↔
(A−L)m ≡ −Dn (mod d).
```

No primality hypothesis on `d` is required.

## Proof decomposition

1. If `a>0` and `d ∣ pᵃ−1`, an explicit Bézout identity proves
   `IsCoprime d p`.
2. The checked difference identity gives

   ```text
   pˢᵃ m̃ − ñ = L(1−pᵃ)m.
   ```

   Hence `d ∣ m̃` if and only if `d ∣ ñ`; cancellation of `pˢᵃ` is lawful by
   the preceding coprimality.
3. Because `(m′,n′)` is primitive, a divisor divides `g` exactly when it divides
   both `m̃` and `ñ`.
4. The identity `ñ=(A−L)m+Dn` turns divisibility of `ñ` into the displayed
   projective congruence.

The proof uses no field division. It therefore remains meaningful when a
denominator or `(A−L)` is noninvertible modulo `d`; the congruence is the
cross-multiplied projective incidence relation.

## Semantic boundary

The theorem is local to one legal positive wait. It does not bound `a`, the
common factor `g`, or the number of successive cancellation events. It does
not imply equality with the terminal rational point. Its contribution is to
identify the cancellation branch exactly: every swallowed cyclotomic factor
divides the integral terminal defect of the source state.

## Lean artifacts

- `ReturnGuard.divisor_pow_sub_one_isCoprime_base`
- `ReturnGuard.divisor_dvd_commonFactor_iff`
- `ReturnGuard.integralStep_cyclotomic_dvd_numerator_iff_terminalDefect`
- `ReturnGuard.integralStep_cyclotomic_cancel_iff_terminalCongruent`

All are in
[`ReturnGuardArithmetic.lean`](../MatrixMortality/ReturnGuardArithmetic.lean).

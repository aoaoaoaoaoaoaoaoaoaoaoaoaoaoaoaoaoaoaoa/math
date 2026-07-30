# M₃(2) finite-quotient completeness

Date: 2026-07-30

## Question

Could two primitive-prime quotient automata, synchronized by the same physical wait, exclude a
terminal address which each projection admits?

An exhaustive reconnaissance over the small exact-order factors for bases `2`, `3`, and `5`
found no strict product certificate. The obstruction is structural and does not depend on the
sample.

## Zero-wait kernel

For integral residual parameters `(A,D,L)`, residue zero gives

```text
M₀ = ⎡ A−L  D ⎤.
     ⎣ A−L  D ⎦
```

Its kernel is the terminal equation

```text
(A−L)n + Dd = 0,
```

whose projective solution is the decoded terminal residual `τ=−D/(A−L)`. The canonical
numerator-denominator pair of `τ` is primitive, so it remains a nonzero homogeneous vector in
every prime quotient. Lean proves that `M₀` annihilates this pair.

Therefore any quotient invariant containing terminality contains the absorbing cancellation
state after one more residue-zero transition.

## Complete certificate criterion

Let `R` be the reset state. The following are equivalent:

1. some invariant contains `R` and excludes cancellation and terminality;
2. some invariant contains `R` and excludes cancellation;
3. cancellation is unreachable from `R`.

For `2 → 3`, use the zero-wait kernel. For `3 → 2`, take the reachable closure of `R`; it is
invariant by construction. Thus ordinary finite-quotient certificate synthesis is one finite
graph-reachability problem. The terminal predicate contributes no additional separation.

The canonical rational-to-integral lift makes the result physical: a cancellation-free
invariant proves the original matrix pair immortal without a separately supplied terminal
exclusion proof.

## Product obstruction

A synchronized two-prime state is a pair of projective quotient states. A sound product
certificate must exclude cancellation in either coordinate, because swallowing either factor
breaks ordinary projective simulation after primitive reduction.

Project any synchronized invariant onto its left coordinate. Given a projected state and any
left residue, choose the same natural wait in the synchronized system. Closure supplies the
projected successor. The projection is therefore a single-factor invariant; cancellation
freeness and reset membership project as well. The same argument applies on the right.

Hence every safe synchronized invariant yields safe certificates in both components. In
particular, no product can certify an instance missed by either factor. The hoped-for
incompatible-history effect cannot occur in this architecture.

## Consequence

The finite-quotient program divides sharply:

- if some prime quotient cannot reach cancellation, it alone proves immortality;
- if every tested quotient can reach cancellation, ordinary products add nothing.

The surviving local-global object must continue *through* cancellation. It must record the
valuation removed from the common gcd, reconstruct the reduced projective state, and resume.
This may yield a finite cancellation nucleus; if the required valuation memory is unbounded,
that memory is a candidate carrier for the missing computational stack.

## Lean artifacts

- `ReturnGuard.IsTerminalPairMod`
- `ReturnGuard.rationalPair_terminalResidual_isTerminalPairMod`
- `ReturnGuard.quotientTransition_zero_terminal_eq_cancelled`
- `ReturnGuard.terminal_mem_forces_cancelled`
- `ReturnGuard.HasCancellationFreeInvariant`
- `ReturnGuard.hasQuotientCertificate_iff_hasCancellationFreeInvariant`
- `ReturnGuard.not_physical_isMortal_of_cancellationFreeQuotient`
- `ReturnGuard.QuotientReachable`
- `ReturnGuard.hasCancellationFreeInvariant_iff_cancelled_unreachable`
- `ReturnGuard.hasQuotientCertificate_iff_cancelled_unreachable`
- `ReturnGuard.not_physical_isMortal_of_cancelled_unreachable`
- `ReturnGuard.HasSynchronizedCancellationFreeInvariant`
- `ReturnGuard.hasSynchronizedCancellationFreeInvariant_imp_components`
- `ReturnGuard.hasSynchronizedCancellationFreeInvariant_imp_quotientCertificates`

The implementation is
[`ReturnGuardQuotientCompleteness.lean`](../MatrixMortality/ReturnGuardQuotientCompleteness.lean).

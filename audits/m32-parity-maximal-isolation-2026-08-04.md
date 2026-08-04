# `M₃(2)` parity and maximal-isolation audit

Date: 2026-08-04

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy lock

The master problem is `M₃(2)`: decide mortality for every pair of `3 × 3` integer matrices or
compile an undecidable source into such a pair with both arbitrary-word implications checked.
The current rank-`(3,2)` attack reduces one concrete family to a deterministic rational guard.
Before this audit, its live split-spectrum escapes were global re-expansion across changing
wait frames and an infinite run of maximal Smith allocations `v=1`.

This audit reconstructs a submitted attack on those escapes. It promotes only statements that
remove one of them. The submitted report is not retained as a repository artifact.

## Verdict

| Claim | Classification | Reason |
| --- | --- | --- |
| the guard prime is odd | promotion | follows from the two adjacent unit hypotheses and is now checked generically |
| odd `A+D−L` forbids physical mortality | promotion | parity propagates through every lifted primitive execution at every depth and contradicts the canonical physical target |
| a maximal step has odd target numerator | promotion | exact cancellation gives a shorter proof than the submitted valuation split |
| consecutive maximal steps are impossible | promotion | the next Smith coordinate `v` is even |
| the Smith quotient is a new split-independent state | restatement | elimination returns the existing one-dimensional guarded state |
| exact-order tokens reset or cancel at divisible waits | restatement | existing checked cyclotomic and order theorems already imply it |
| a scheduled core is locally height-bounded | open | plausible local accounting, but no checked consumer changes the master frontier |
| every nonperiodic survivor yields an unbounded exact-order antichain | rejected | the report assumes, but does not prove, unconditional global core extraction |

## Adjacent units force an odd prime

The parameter record assumes that `α` and `α−1` are p-adic units. At `p=2`, write
`α=n/d` in lowest terms. Unit valuation gives equal 2-adic valuations for `n` and `d`;
coprimality forces both valuations to vanish, so `n` and `d` are odd. The numerator `n−d` of
`α−1` is then even and nonzero, contradicting its unit valuation.

The proof is stated once in `PadicValuation` for any pair of adjacent rational units and is
consumed by `Parameters.prime_odd`. It is not duplicated inside guard dynamics.

## Odd-resultant immortality

Put `R=A+D−L`. A cumulative endpoint step has

```text
p^(sa)t′ = r − L(pᵃ−1)t,
r′ = Dr + (A−L)t′.
```

Because `p` is odd, `pᵃ−1` is even. If `r` is odd, the first equation makes the scaled target
denominator odd. The removed primitive content and primitive target denominator are therefore
both odd. If `R` is odd, the coefficient sum `D+(A−L)` is odd, so the second equation makes the
scaled target numerator, and hence the primitive target numerator, odd.

The reset endpoint numerator is `R`. Induction through the existing decoded-to-primitive
execution lift keeps every reachable primitive endpoint numerator odd. The canonical physical
target represents the terminal residual, whose terminal coordinate and therefore endpoint
numerator are zero. The contradiction proves physical immortality itself, rather than a
surrogate statement about a separately supplied cumulative execution. No new execution type or
content register was added.

## Maximal cancellation collapses

At critical depth two, a maximal Smith allocation has `v=1`, `u=q−1`, and

```text
m = Lt + q²ηt′,
r = (q−1)m,
ηr′ = Dm + (A−L)ηt′,
ηθ = DL.
```

The submitted proof split according to the 2-adic valuations of `D`, `L`, and `η`. That split
is unnecessary. Substitute `m`, replace `DL` by `ηθ`, and cancel the nonzero factor `η`:

```text
r′ = θt + (Dq² + A−L)t′.
```

The source numerator `r` is even, so source primitivity makes `t` odd. Since `u=q−1` is even
and `gcd(u,θ)=1`, `θ` is odd. In the remaining stratum `R` is even; `q` is odd, hence
`Dq²+A−L` is even. The displayed identity makes `r′` odd. A maximal step therefore cannot be
terminal.

If another primitive step follows, its denominator equation makes the next forward content
odd. Thus the next `u` is odd. Since `uv=q′−1` is even, the next `v` is even. In particular,
maximal steps cannot be consecutive; every maximal step is followed by a branch on the
formally contracting `v≥2` side.

## No false antichain reduction

The report correctly observes that the signed Smith factors do not carry a second dynamical
register. Its proposed complete quotient eliminates to the existing guarded scalar recurrence,
so a new quotient definition and transition theorem would only duplicate the present ontology.

The exact-order reset-or-cancel statement is likewise already the composition of the checked
primitive-order theorem with the checked cyclotomic reset theorem. A wrapper would add no
mathematics.

The later product inequalities are conditional accounting. They do not prove that every
unbounded-denominator survivor creates superbudget, pairwise-coprime cyclotomic cores. Without
that extraction theorem, the claimed “single exact enemy” of an unbounded divisibility
antichain does not follow. The global nonmaximal amortization problem remains live.

## Checked boundary

Lean now checks:

- `PadicValuation.odd_prime_of_adjacent_units`;
- `ReturnGuard.Parameters.prime_odd`;
- `ReturnGuard.not_physical_isMortal_of_resetResultant_odd`;
- `PrimitiveEndpointReduction.maximalCancellation_targetNumerator_odd`;
- `PrimitiveEndpointReduction.maximalCancellation_next_v_even`.

Artifacts: [`PadicValuation.lean`](../MatrixMortality/PadicValuation.lean),
[`ReturnGuardDynamics.lean`](../MatrixMortality/ReturnGuardDynamics.lean),
[`ReturnGuardCumulative.lean`](../MatrixMortality/ReturnGuardCumulative.lean), and
[`ReturnGuardSmith.lean`](../MatrixMortality/ReturnGuardSmith.lean).

The proposed complete-quotient definitions, a second execution structure, exact-order wrapper
theorems, scheduled-core API, and the initial valuation case split were culled. The surviving
code is confined to declarations consumed by the parity obstruction.

## Strategic consequence

The odd-resultant parameter stratum is immortal. In the even-resultant stratum, the infinite
maximal throat is closed: maximal steps are isolated and cannot terminate. `M₃(2)` remains
open because local `v≥2` contraction has not been converted into a global invariant along an
unbounded-denominator rational execution. The next attack must prove that amortization or
construct an orbit defeating it; it must not assume an unproved cyclotomic antichain extraction.

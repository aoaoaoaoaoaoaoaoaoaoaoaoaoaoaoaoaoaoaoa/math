# M₄(3) zero-framed Lag decision audit

**Date:** 10 August 2026

**Status:** exact source classification formalized; `Lₙ` retired

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide the zero-framed binary context-2 Lag node of the promised overlap-queue trunk

## Verdict

The reported classification is correct and stronger than required. For every `n>0` and binary
words `U,V,W`, without either compiler promise,

```text
Accepts(n,U,V,W) ↔ (n=1 ∧ U=ε) ∨ (V=ε ∧ U∈0*).
```

Lean proves the equivalence over the repository's chronological trace relation, then constructs
the corresponding decision procedure and composes the formula with the checked mortality
compiler. This removes `Lₙ`; it does not decide the other scanner kernels or `M₄(3)`.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`5cb071fa338f46b484f21764d2df4ba4d2bc0227`. Its transient final report has SHA-256 digest
`eb00fe173e9037d62e2f83712c71831d9e1d448ca0fb2944a779d2a7218e4dc3`.

## Reconstruction

Every nonempty accepting trace has one last predecessor. Since the target is the singleton `0`,
that predecessor is exactly `10` with `U=ε` or `00` with `V=ε`.

Lean reconstructs the complete backward cone of `10`. Any predecessor using context `01` would
append `W0ⁿ⁺¹`; after cancellation of the final zero, a nonempty all-zero suffix would equal an
all-one word. Hence only `11` predecessors occur, and a trace of length `k` starts at `1ᵏ⁺¹0`.
Comparison with `10ⁿ` forces `n=1` and a zero-length prefix trace.

For the `00` branch, if `U` contains `1`, then containment of `1` is invariant: a surviving tail
keeps it, while consuming the only `1` through context `10` appends another from `U`. Thus
reachability of `00` forces `U∈0*`. Conversely, `V=ε` and `U=0ᵐ` give the explicit orbit

```text
10ⁿ → 0ⁿ⁺ᵐ → 0ⁿ⁺ᵐ⁻¹ → ⋯ → 0.
```

The proof covers arbitrary intermediate words and does not assume intended block structure.

## Promotion Boundary

Formalized:

- the exhaustive last-step split;
- the exact backward cone of `10`;
- the forward `1`-containment invariant;
- both constructive accepting traces;
- the unconditional classification and induced decision procedure;
- the mortality classification under the existing compiler promises.

Rejected as unnecessary:

- a separate promised-positive classification, since the unconditional theorem subsumes it;
- orbit-search machinery or a finite-state simulator;
- any further universality attack on `Lₙ`.

Open:

- decisions for reset scanner `Bₙ` and periodic-conjugate scanner `C`;
- the original and retuned parabolic matrix lanes;
- `M₄(3)`.

## Artifacts

- [`MatrixMortality/OverlapLagDecision.lean`](../MatrixMortality/OverlapLagDecision.lean)
- [`MatrixMortality/OverlapLag.lean`](../MatrixMortality/OverlapLag.lean)

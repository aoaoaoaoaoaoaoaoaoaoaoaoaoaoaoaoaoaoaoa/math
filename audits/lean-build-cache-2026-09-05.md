# Shared Lean Build And Verification Cache

## Scope

Lean/mathlib `v4.33.1`, starting from `30687d1`. This change preserves the mathematical
statements and reviewed transitive dependencies. It replaces blanket imports and the
monolithic check transaction with native Lake compilation and verification targets.

## Checked Boundary

- The full gate passes over all discovered first-party modules. Its output is byte-identical
  to `verification/axioms.txt`: 3,127 reviewed declarations, 7,754 report lines.
- Every default environment linter runs, including slow checks. Source-policy scans consume
  the complete first-party import closure, separately from compiled artifacts.
- `m35`, `m44`, and `m92` have explicit endpoint-type probes. The universal source and the
  separate endpoint constructions no longer share one compulsory aggregate import.
- The publication gate checks published proof roots, semantic HTML, and the reproducible
  PDF. Auxiliary certificates remain in `all` and `symbolic`.
- All auxiliary checks passed, including 20,272,272 bounded source words and the existing
  exact matrix, mixed-prime, and Frankl certificates. This is supplementary evidence, not
  an additional trust premise of the Lean endpoints.

The previous root aggregates omitted three tracked files:
`DecimalSetterThreeBlockAllEraseCurrent`, `SwappedSetterFringeSmall`, and
`SwappedSetterFringeBridge`. All three now compile and enter the full environment-lint gate.
Their inclusion is not a new mortality-cell resolution.

## Cache Acceptance

The native store is `~/.cache/lake`, physically `/data/main/lean-cache/artifacts`.
Dependency package pools remain separate. The maintained Lean/Lake launcher enables the
same cache for existing worktrees without modifying their manifests or copying package trees.

A disposable `.worktrees/cache-audit` checkout exercised these boundaries:

| Experiment | Observed result |
| --- | --- |
| Identical foundations target in a second worktree, `--no-build` | Passed in 3.45 s; compiled artifacts and the verification receipt were restored |
| Add a prohibited token inside a source comment | Compilation succeeded; the source-policy gate rejected the target instead of reusing its earlier success |
| Restore the original source, `--no-build` | Passed in 1.30 s; the original successful result was reused |
| Remove `Classical.choice` from one expected transitive set | Gate rejected the changed snapshot and printed the expected/actual difference |
| Warm `m92`, `--no-build` | Passed in 1.73 s |
| Overlapping `proofs m92 publication`, `--no-build` | Passed in 3.15 s after the graph-construction fix below |

Times are single wall-clock observations during other bulk work, not benchmark medians.
The foundational compilation graph shrank from 8,706 jobs to 1,711 after removing blanket
mathlib imports. The final `m92` verification graph has 2,514 jobs, normally cache hits.

The tests caught three implementation defects before release. Custom Lake actions need an
explicit current-package scope to enter the shared artifact cache; otherwise their receipts
remain local. Mathlib's hash-command linter also reports prohibited audit commands as info
when warnings are errors. The audit now uses named non-hash commands, preserves all enabled
options, and compares the complete report byte-for-byte.

Fetching overlapping module graphs from asynchronous `JobM` continuations triggered repeated
`Task.get` diagnostics in Lake's synchronous export-info continuation, matching the site in
[Lean issue 14612](https://github.com/leanprover/lean4/issues/14612). The first stress run was
terminated; bounded reruns reproduced the failure. Graph construction now remains in `FetchM`;
only execution runs asynchronously. The overlapping build then passed in 28.91 s and its
no-build replay in 3.15 s, without diagnostics. No compiler binary, dependency, or lint option
was changed to obtain that result.

## Trust And Limits

This is trusted-local artifact reuse, not independent kernel reproduction or a public CI
attestation. Cache misses execute the same Lean checks; failures do not produce successful
receipts. Native cache hashing is not a cryptographic authentication mechanism. No upload
service was configured. Cache retention is currently manual; see `BUILDING.md` for controls.

The original 3,139-line `AxiomAudit.lean` repeated the declaration inventory already encoded
in the reviewed snapshot. Its replacement reads that single inventory and checks the same
transitive sets. The direct audit driver remains available for uncached replay.

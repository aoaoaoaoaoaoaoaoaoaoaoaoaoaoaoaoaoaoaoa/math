# Rank-Two Kernel-Bifurcation Audit

**Date:** 2026-08-10  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `15e2cb00084586a1f7dfb8fadab9b28d4862a9a3` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a796342-48ac-83ea-8597-c8d5c8d1b662

## Verdict

No uniform paired recognizer, mortality family, or universal lower bound is obtained. The report
does isolate the correct rank-two geometry, but its statement that the common-kernel architecture
is deleted is too broad. A transient guard may be refreshed after each data action; the exact
theorem only erases a route difference already confined to the common kernel.

The promoted result is therefore a bifurcation, not a no-go: common kernels have an exact
route-erasure law, while transverse kernels retain one bilinear fibre intersection.

## Checked Common-Kernel Law

Let `K` lie in the kernels of both data maps `B,C`, suppose `T(K)⊆K`, and let `δ∈K`. Lean proves

```text
B(T^[n] δ)=0,       C(T^[n] δ)=0
```

for every `n`. Thus toggles can delay erasure but cannot move that particular difference back
into a data-visible coordinate; the next data action kills it. The theorem does not assert that
all route differences lie in `K` or that a compiler cannot manufacture a new guard afterward.

## Checked Transverse-Fibre Law

In coordinates with the two quotient projections

```text
π_b[x:y:z]=[y:z],       π_c[x:y:z]=[x:z],
```

suppose a point maps projectively to `[u:v]` and `[r:s]`, with `s≠0`. Writing the two ray scales
and equating the shared third coordinate yields a nonzero common scale. Lean proves that the
point is projectively equal to

```text
[rv : us : vs].
```

This is exactly the bilinear survivor. It does not construct the shift-equivariant predecessor
states that would make the formula a complete same-zero compiler.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| A common-kernel route difference is erased at the first later data action | promotion | `commonKernel_route_erased` |
| Two transverse quotient fibres intersect in `[rv:us:vs]` | promotion | `sameRay_bilinearFibrePoint` |
| Every common-kernel compiler is impossible | rejected | guard refresh after a data action is outside the theorem |
| A surviving rank-two compiler must have distinct kernels | rejected | depends on the preceding overclaim |
| The junk reserve supplies a uniform invariant surface | rejected | only qualitative discussion; no source-computable construction |
| `M₃(4)` follows positively or negatively | rejected | neither master direction is closed |

## Master Delta

```text
MASTER VERDICT: still open.
SHARPENED: rank-two paired constructors split into common-kernel guard refresh and transverse
           bilinear recurrence.
REMOVED: treating a common-kernel coordinate as persistent across the next data action.
REMAINS: one source-computable all-word invariant and exact terminal section, or a positive-only
         projective lower bound covering both kernel branches.
```

## Artifact

- [`PositiveResetNoGo.lean`](../MatrixMortality/PositiveResetNoGo.lean)

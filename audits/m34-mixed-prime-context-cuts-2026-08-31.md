# M₃(4) Mixed-Prime Contextual-Cut Audit

**Date:** 2026-08-31
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `4fb94a7` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeOddFamilyParikh.lean`](../MatrixMortality/GuardedMixedPrimeOddFamilyParikh.lean)
**Certificates:**
[`certify_mixed_prime_context_cuts.py`](../tools/certify_mixed_prime_context_cuts.py) and
[`audit_mixed_prime_kernel.rs`](../tools/audit_mixed_prime_kernel.rs)

## Verdict

The infinite odd mixed-prime kernel family cannot supply the reduced `bcbc` fork outside the
already forbidden centralizer exits. Lean proves the unbounded Parikh-cut obstruction after the
literal contextual decomposition has supplied one of seven exact off-centralizer certificates.
The word decomposition which produces those certificates is audited, not internalized in Lean.

The same cut invariant contracts the completed five-rule presentation more sharply than the
earlier generic cell bounds. Its `50` rules and all `405` genuinely new second-critical branch
pairs leave only the internal/internal cell. That cell has total length at most `2m-5`: at most
`113` for the completed rules and `171` for the second-critical pairs. Exact union-find replay
rejects every second-critical placement through those bounds, covering `799,088,198` fixed
geometries.

This kills the odd family at every depth and the first two critical generations as one-context
repairs. It does not solve the parametric word equation in the convergent quotient: an arbitrary
conversion may contain several rewrite windows and need not expose one second-critical pair as a
single common-context core.

## Uniform Odd Family

Let `Uₖ,Vₖ` be the odd-family pair of common length `m=29+2k`. Their dilation counts agree. Lean
proves the exact proper balanced cuts:

```text
balanced positive prefixes: {3},
balanced positive suffixes: {m-3}.
```

The letters immediately after the prefix cut disagree. The only possible short aligned blocks
at the complementary suffix cut also disagree. These facts eliminate the internal/internal,
internal-prefix/comparable-suffix, comparable-prefix/internal-suffix, and same-shorter cells in
both relation orientations. They are packaged as
`OddFamilyOffCentralizerCutCertificate`, whose seven constructors are all contradictory.

The two omitted exits are deliberate. A full prefix or suffix comparison makes one data macro a
literal border of the other and enters the centralizer branch already rejected by `G3-S08` and
`G3-S13`. If the two data words have equal length, prefix comparison makes them literally equal,
so the two fork layouts coincide and cannot expose distinct `Uₖ,Vₖ` windows.

The Lean theorem consumes the seven cut certificates. It does not claim that arbitrary lists
supply them automatically; the extraction uses the fixed `YZXYX/XZYXY` block geometry and the
positivity hypotheses from `G3-S11`.

## Finite Cut Census

The independent Python certificate reconstructs the `50` completed rules from the five base
relations. For every oriented equal-Parikh pair it enumerates every proper prefix and suffix with
equal dilation count and checks that the letters immediately before and after each prefix cut
disagree.

The five base rules have prefix-cut set `{3}`. Each of the `45` first-critical rules has
`{3,a}`, where `28≤a≤32`; its complementary suffix cuts are `{m-a,m-3}`. The exact
`(m,a,m-a)` histogram is:

```text
(52,28,24):1  (53,29,24):1  (54,28,26):1  (54,30,24):1
(55,28,27):3  (55,29,26):1  (55,31,24):3
(56,29,27):3  (56,30,26):1  (56,32,24):3
(57,30,27):3  (57,31,26):3
(58,31,27):9  (58,32,26):3  (59,32,27):9
```

Among the `450` critical overlaps of the completed system, `45` reproduce completed rules and
`405` are new branch pairs. Every new pair has exactly three balanced prefix cuts `{3,a,b}`, with
`28≤a≤32` and `53≤b≤61`. Their length histogram is:

```text
77:1  78:2  79:4  80:13  81:22  82:29
83:52  84:69  85:60  86:63  87:63  88:27.
```

The canonical full payload contains all `455` word pairs and their cut sets. Its SHA-256 is
`d77b9f7121fe75630329f8bc2a94ba31eb27fe9c198dd801bb9898e425b5e306`.
The certificate source SHA-256 is
`44776ac42c71a4b9a2bc69208b2f49fdb62c5914861915ccceed2c5ba8a3162a`.

## Cell Contraction

Write a one-context fork model as

```text
Y Z X Y X = P U Q,       X Z Y X Y = P V Q,
```

and put `x=|X|`, `y=|Y|`, `z=|Z|`, `m=|U|=|V|`, `p=|P|`, `q=|Q|`, and
`r=min(x,y)`. Since every audited pair differs at both endpoints, `p,q` are its exact mismatch
cuts. Comparing each with `r` gives the same `3×3` partition used in `G3-S13`.

If both cuts are internal, let `M=max(p,q)`. Positivity and block geometry give

```text
4M+5 ≤ N = 2x+2y+z = m+p+q ≤ m+2M,
```

and hence `N≤2m-5`. In every other off-centralizer cell, the aligned copy of the shorter macro
forces a proper balanced prefix or suffix cut. Immediate disagreement on the two sides of every
audited cut excludes the required continuation. A cut which reaches the whole macro is exactly a
full-prefix or full-suffix centralizer exit, not a finite cell.

Thus the completed rules need only the already exhaustive all-cell search through `N=120`, since
their internal bound is `113`. For the second-critical pairs, an all-cell search through `120`
and an internal-only search from `121` through `171` are exhaustive.

## Exact Replay

For fixed `x,y,z,p,U,V`, each position of `X,Y,Z` is one binary letter variable. Equal positions
outside the relation window are unioned; positions inside it are bound to the displayed letters
of `U,V`. Union-find decides consistency exactly, and any unbound class can be set to `D` to
construct a witness. The checker recomposes every alleged witness before reporting it.

Compile and replay the second-critical search with:

```sh
rustc --crate-name mixed_prime_kernel_audit --edition 2021 -D warnings -C opt-level=3 \
  tools/audit_mixed_prime_kernel.rs -o /tmp/mixed-prime-kernel-audit
for s in {0..11}; do
  /tmp/mixed-prime-kernel-audit fork-context-g2 1 120 all "$s" 12
done
for s in {0..5}; do
  /tmp/mixed-prime-kernel-audit fork-context-g2 121 171 internal "$s" 6
done
```

Every shard returns `FORK_CONTEXT_NONE`. The first tranche covers `779,044,642` geometries; the
second covers `20,043,556`; their union is `799,088,198`. Every run reconstructs and checks
`450` raw overlaps, `45` old pairs, `405` new pairs, zero left-side inclusions, and the exact
second-generation length histogram. The canonical project check runs the construction and
self-check, but omits the 799-million-geometry research replay. The audited Rust source SHA-256 is
`108635879fad5f6046b2b05e55cebb099a68419b1ccbb8a21f82fdbf8860ad2e`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The odd family has only the displayed proper balanced cuts | promotion | Lean for all depths |
| An off-centralizer odd-family contextual fork exists | rejected | Lean seven-cell cut certificate plus audited extraction |
| A first- or second-critical one-context repair exists | rejected | exact cuts, finite bounds, assignment-complete replay |
| Every arbitrary quotient fork exposes one such context | open | multiple rewrite windows need not localize |
| The finite convergent quotient has no non-common-fixed fork | open | existential word equation remains |
| The full mixed-prime affine kernel has no usable fork | open | other kernel relations remain |
| `M₃(4)` follows | rejected | endpoint-uniform non-common-fixed compiler still absent |

## Formal Validation

The formal module and root import build warning-free. Lean LSP reports zero diagnostics, including
no hints. `AxiomAudit.lean` reports only the reviewed foundational axioms for every promoted
theorem. The Python certificate is dependency-free, typed, Ruff-clean, and canonical-gated. The
Rust auditor compiles under `-D warnings`, reconstructs both relation generations in `self-check`,
and owns the exact long replay interface.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
ODD FAMILY: globally dead as a one-context fork outside the forbidden centralizer.
FINITE QUOTIENT: first and second critical one-context repairs are dead.
LIVE QUOTIENT NODE: arbitrary multi-window solutions of YZXYX ≡ XZYXY.
LIVE KERNEL NODE: new equal-action families outside the completed five-rule quotient.
```

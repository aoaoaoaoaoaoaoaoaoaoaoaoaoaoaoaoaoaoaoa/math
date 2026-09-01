# M₃(4) Mixed-Prime Fork-Quotient Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `14441f4` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeForkQuotient.lean`](../MatrixMortality/GuardedMixedPrimeForkQuotient.lean)
**Computational owner:**
[`audit_mixed_prime_kernel.rs`](../tools/audit_mixed_prime_kernel.rs)

## Verdict

The first critical completion of the five audited mixed-prime relations does contain a genuine
fork-shaped collision. Its reduced length is `312`. Its macro words are positive and have
pairwise distinct slopes. It nevertheless lies exactly on the common-fixed diagonal forbidden by
the complete `bcbc` endpoint language: the three macro actions are `F,F²,F⁴` for one strict affine
contraction `F`.

Lean checks the collision, its exact critical-pair derivation, its distinct raw sides, its lengths,
its common fixed point, its power collapse, and rejection of its endpoint code. A generic Lean
theorem kills every full-triple conjugacy lift for the same reason. Audited word bounds and exact
assignment search eliminate every other placement of one of the five base relations or their
`45` first-overlap critical pairs.

This classifies the one-context, first-critical hull. It does not classify arbitrary multi-step
derivations in the generated congruence or the full affine kernel. `M₃(4)` remains open.

## Exact Witness

Let `A=cassaigneRight` and `B=cassaigneLeft`. The right word starts and ends in `T`, so write

```text
A=T M T.
```

Define

```text
K=T M,       H=B M,       R=H K,
X=K,         Y=K R,       Z=H.
```

The length-`53` self-overlap of `A` has two one-step reductions

```text
U=B A.tail,       V=A.dropLast B.
```

Each branch has the same affine action: both are contextual replacements of `A` by `B` in the
common overlap source `A A.tail=A.dropLast A`. Lean proves the literal factorizations

```text
R K=U Q,       K R=V Q,       Q=M K,
```

and then

```text
Y Z X Y X=P U Q,       X Z Y X Y=P V Q,
P=K R R K.
```

Consequently the reduced fork words are distinct but have equal action. Their macro lengths are

```text
|X|=26,       |Y|=104,       |Z|=52,
2|X|+2|Y|+|Z|=312.
```

Lean computes pairwise unequal slopes and the exact common fixed point

```text
p=6560881480/3955045357.
```

It then proves, for every rational state,

```text
Z=F²,       Y=F⁴
```

at action level, where `F` is the action of `X`. Thus the distinct raw macros encode three
different powers of one contraction, not three independent endpoint controls.

## Centralizer Collapse

The explicit witness is the terminal case of a general construction. Suppose the common fork
prefix includes the literal equality `YZX=XZY`, and write `Y=XA` with `A` nonempty. Cancelling
`X` gives

```text
A(ZX)=(ZX)A.
```

The commuting-word theorem supplies a primitive word `R` and positive exponents `s,t` with
`A=Rˢ`, `ZX=Rᵗ`. Split `R=HK` at the suffix cut occupied by `X`. For some `0≤k<t`,

```text
X=K Rᵏ,       Y=K R^(k+s),       Z=R^(t-k-1) H.
```

After the remaining common context is cancelled, the equal-action core is

```text
Rˢ K = K Rˢ.
```

Lean proves the action-level conclusion independently of the free-word decomposition. The
nonempty contraction `Rˢ` has a unique rational fixed point. Commutation makes `K` fix it. Since
`R=HK`, `H` fixes it as well, and therefore so do `X,Y,Z`. The existing common-fixed theorem then
rejects the complete endpoint converse for every source and target.

## Context Cells

Consider one fixed relation core `U,V`, one orientation, and positive words `X,Y,Z` satisfying

```text
Y Z X Y X=P U Q,       X Z Y X Y=P V Q.
```

Put

```text
x=|X|, y=|Y|, z=|Z|, m=|U|=|V|,
p=|P|, q=|Q|, N=2x+2y+z=m+p+q, r=min(x,y).
```

Every one of the `50` cores differs in its first and last letter. Hence `p,q` are the exact
mismatch cuts. A cut is internal when it is below `r`; otherwise the shorter of `X,Y` is a
literal prefix or suffix of the longer. This gives a complete `3×3` partition. The two cells
where one word is the shorter prefix but the other is the shorter suffix are length-impossible.

### Internal/Internal

Let `M=max(p,q)`. Then `x,y≥M+1`, so

```text
4M+5≤N≤m+2M.
```

Thus `N≤2m-5≤113`, since every first-critical core has `m≤59`.

### One Comparable Cut

If the prefix is internal and the suffix comparison reaches length `x+y`, then `YX=XY`; action
cancellation and distinct macro actions propagate the common fixed point to `Z`. Otherwise
elementary length inequalities give `N≤4m-11≤225`.

For the reversed cell, take a globally length-minimal witness and suppose `X` is the shorter word,
so `Y=XA`. Prefix peeling either gives `N≤2m-5`, shortens `Z`, or reaches the full-triple
centralizer. Off those exits, `z<|A|`, `|Y|≤m-2`, and again `N≤4m-11`. Swapping `X,Y` covers the
other two cells.

### Same Shorter Word

Suppose `X` is both the shorter prefix and suffix, so `Y=XA=BX`. Removing the boundary copies of
`X` forces both core branches to contain an aligned square `XX` at the same internal offset.

If `y≥2x`, write `Y=XKX`. Exact inspection of all `50` cores in both orientations finds `770`
aligned-square candidates. Every square root is `D`, `T`, or `DD`; none has the opposite prefix
equal to the constant root letter. Tail periodicity and prefix peeling then give

```text
N≤3m-1≤176.
```

If `x<y<2x`, put `d=y-x`. The two mismatch defects obey

```text
m=δ+2x+ε,       δ,ε≥1.
```

A minimal noncentral witness has `z<max(d,δ)`. Exact integer maximization gives `N≤192`. The
case with `Y` shorter is symmetric.

These are word-combinatorial bounds, not Lean claims. The full-prefix and full-suffix cases are
removed by the formal centralizer theorem rather than a length cutoff.

## Exact Assignment Search

The checker constructs the five base pairs and all `45` proper critical branch pairs from one
rule table. For fixed `x,y,z,p,U,V`, every letter position of `X,Y,Z` is a variable. Positions
outside the relation window impose equality between the two fork layouts; positions inside bind
the variables to the corresponding `D/T` letters of `U,V`. Union-find with optional letter labels
decides this system exactly. If it is consistent, assigning `D` to every free class constructs a
literal witness, which the checker recomposes and verifies.

The exhaustive commands are

```sh
rustc --crate-name mixed_prime_kernel_audit --edition 2021 -D warnings -C opt-level=3 \
  tools/audit_mixed_prime_kernel.rs -o /tmp/mixed-prime-kernel-audit
/tmp/mixed-prime-kernel-audit self-check
/tmp/mixed-prime-kernel-audit aligned-square 5
/tmp/mixed-prime-kernel-audit fork-context 1 120 all 5
/tmp/mixed-prime-kernel-audit fork-context 121 225 one-comparable 5
/tmp/mixed-prime-kernel-audit fork-context 121 176 nonoverlap-same-shorter 5
/tmp/mixed-prime-kernel-audit fork-context 121 192 overlap-same-shorter 5
```

All four searches return `FORK_CONTEXT_NONE`. `self-check` independently compares the existing
affine signature engine against full integer matrices through length `12`, checks the relation
table, verifies all `45` critical overlaps, replays the odd kernel family, checks the exact
length-`312` contextual model, and asserts the complete aligned-square census. The computational
result is assignment-complete on the displayed ranges; the preceding bounds, not a larger search,
make those ranges exhaustive for the stated hull.

The audited checker SHA-256 is
`96992628642c12d82feae3e6a73dc487a503408850cd9a3ea592867c8122108a`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The first Cassaigne critical pair embeds in a reduced fork at length `312` | promotion | Lean literal factorization |
| The two fork words are distinct and have equal action | promotion | Lean contextual rewrites |
| The macro slopes are pairwise distinct | promotion | Lean exact rational products |
| The macros share the displayed fixed point and act as `F,F²,F⁴` | promotion | Lean affine rigidity |
| This explicit macro code satisfies the endpoint converse | rejected | Lean common-fixed obstruction |
| Every full-triple conjugacy lift is common-fixed | promotion | Lean action-level centralizer theorem; audited free-word reduction |
| Another one-context base/first-critical placement survives | rejected | exhaustive cell bounds and exact assignment search |
| The five rules and first critical pairs present the full kernel | rejected | the basis is already known incomplete |
| No multi-step quotient fork exists | open | outside the one-context hull |
| No non-common-fixed mixed-prime fork exists | open | unaudited kernel relations remain |
| `M₃(4)` follows | rejected | the multi-step quotient and endpoint mantissa remain |

## Formal Validation

The formal owner and root module compile warning-free under the repository toolchain. The focused
default namespace linter and Lean LSP report no diagnostics. Publication-facing declarations are
listed in [`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom sets agree with the
reviewed project baseline. The Rust owner is formatted, compiles under `-D warnings`, and passes
its self-check. No proof aperture, project axiom, unsafe declaration, linter suppression,
floating-point arithmetic, or unverified certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
POSITIVE WITNESS: a genuine reduced fork exists at N=312 in the first critical completion.
FORMAL KILL: its macros are F,F²,F⁴ and violate the endpoint converse.
BOUNDED KILL: every other one-context base/first-critical placement is impossible.
LIVE ESCAPE: a noncentral multi-step quotient fork or a new kernel relation, then mantissa.
```

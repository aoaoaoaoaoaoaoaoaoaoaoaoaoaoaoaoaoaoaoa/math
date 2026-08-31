# First Multi-Transfer Trichotomy Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every first swapped-ternary multi-transfer pole in the expected shells passes
through one of three exact all-`c`/singleton shapes

This audit formalizes the first arbitrary-word branch not covered by the distinguished-boundary
one-transfer classifier. It narrows the swapped ternary candidate; it does not prove projective
avoidance or settle `M₅(3)`.

## Upper Grammar

For a role block `z`, let `m(z)` be the length of its Neary upper spelling and `b(z)` the number
of underlying `b` roles. Lean proves

```text
m(z)=|z|+(β+1)b(z).                                      (1)
```

A role block is nonempty and ends in an erasure. Hence `m(z)<β+2` forces `b(z)=0`, so every
role is `c` and `m(z)=|z|`. This converts valuation balances into literal role words without a
finite search.

## Pole Balance

The centered recurrence is

```text
X'=3^mY,
Y'=CY+KVX.                                               (2)
```

The coupling, every physical lower code in scope, and the incoming punctuated coordinate are
`3`-adic units. If the coefficient depth `s` differs from the incoming depth `d`, the two terms
in `Y'` have distinct valuations and

```text
v₃(Y')=min(s,d).                                       (3)
```

A target pole then equates the valuation of its coefficient times `Y'` with that of the scaled
`X` term:

```text
m(middle)=depth(target)+min(depth(middle),depth(first)).  (4)
```

Singleton blocks have depth `β`; multi-role blocks have depth one. Combining these values with
(1) and (4) yields three branches:

```text
middle letters = cc,          target multi-role;
middle letters = c^(β+1),     target singleton;
first letters = cc, middle = D_b, target singleton.      (5)
```

The third branch is the only way a singleton upper length `β+2` can balance the target shell:
the preceding first depth must be two, and (1) makes that first role word `cc`.

## Resonance

Equal coefficient and incoming depths require a singleton middle block and incoming depth `β`.
For both `D_b` and `D_c`, Lean computes the literal swapped upper and lower codes and factors the
new denominator as

```text
Y'=3^β u,      u≡2 (mod 3).                           (6)
```

Thus resonance creates no extra carry: its exact depth remains `β`. The next pole balance
would require either singleton upper length to equal `β+1` or `2β`, both impossible for
`β≥3`. Therefore (5) is exhaustive.

## Exact Boundary

The packaged theorem assumes the physical middle coefficient and lower-code unit laws, the
two expected pole shells, the punctuated incoming unit, and a nontrivial first depth. It proves a
necessary trichotomy. It does not prove reachability of the listed shapes, classify later
multi-transfer histories, or transfer the ternary argument to the decimal setter. The decimal
candidate has a distinct two-prime carrier and separate extinction results.

## Verification

[`SwappedSetterMultitransfer.lean`](../MatrixMortality/SwappedSetterMultitransfer.lean) contains
the exact code calculations, valuation laws, upper grammar, resonant exclusion, and packaged
`firstMultiTransfer_trichotomy_of_pole`. The module builds warning-free and contains no proof
aperture. Publication-facing declarations are listed in `AxiomAudit.lean`; the canonical audit
snapshot is regenerated only after integration with the concurrent research wave.

## Artifacts

- [`SwappedSetterMultitransfer.lean`](../MatrixMortality/SwappedSetterMultitransfer.lean)
- [`MM-S03`](../SALVAGE.md#mm-s03-centered-setter-carry)
- [`MM-S35`](../SALVAGE.md#mm-s35-first-multi-transfer-trichotomy)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)

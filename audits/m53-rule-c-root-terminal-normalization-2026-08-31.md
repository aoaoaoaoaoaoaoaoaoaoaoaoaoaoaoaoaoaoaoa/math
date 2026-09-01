# One-`R_c` Root Terminal Normalization Audit

**Date:** 2026-08-31
**Target:** complete shallow-pole language over the decimal setter root `[R_c]`
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** a shallow pole over `[R_c]` is exactly a literal Neary terminal match; no malformed
pole survives on this root branch

## Cancellation

For the root `ruleCRoot=[R_c]`, direct decimal evaluation gives

```text
9H = lift(10^β),
9Δ = gap(10^β).
```

Substituting these identities into the `MM-S77` shallow equation yields

```text
(9HΔ)P = (9HΔ)V.
```

The checked decimal-unit shells of `H` and `Δ` prove the common factor nonzero. Lean therefore
cancels it exactly and obtains

```text
HitsSquarePole β body target [[R_c]] ↔ P=V.
```

The reverse direction uses the same calibrations and does not assume target nonemptiness,
phase law, or a valuation shell.

## Literal Language

By definition, `P` is the decimal code of

```text
spell (nearyUpper β) target ++ nearyMarker β,
```

and `V` is the code of `spell (nearyLower β body) target`. Both codes use the positive digits
five and seven. The existing exact code injectivity theorem turns `P=V` into equality of these
binary words, and casting back proves the converse. The final theorem is therefore an iff with
the literal Neary terminal equation, not merely a numeric or shell condition.

## Consequence

Every pole over this root is a lawful terminal match. Under the ordinary Neary envelope, the
existing terminal theorem identifies it with tag halting. `MM-S79` supplies one explicit
minimum-body instance, but no body-length hypothesis is used here.

This result does not classify another one-role root or a longer rule-ended root. Those are the
remaining shallow source grammar. Singleton targets and histories of two or more source blocks
belong to separate `MM-S74` branches.

## Verification

The module and root aggregate build without warnings. Dedicated default lint and Lean LSP
diagnostics are clean. The selected transitive axiom audit contains only the reviewed standard
axioms. Forbidden-form and diff checks pass; no proof aperture or linter suppression is present.

## Artifacts

- [`DecimalSetterMinimumBody.lean`](../MatrixMortality/DecimalSetterMinimumBody.lean)
- [`DecimalSetterBridge.lean`](../MatrixMortality/DecimalSetterBridge.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s81-one-r_c-root-terminal-normalization)

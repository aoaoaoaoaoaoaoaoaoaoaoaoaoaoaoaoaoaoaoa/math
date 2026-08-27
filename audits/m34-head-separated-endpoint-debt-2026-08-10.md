# Head-Separated Endpoint-Debt Audit

**Date:** 2026-08-10  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `e656e0d94e383dd4194469bd8b09f32f9ec7d779` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a796337-36f4-83ea-b65b-5c67f016edb5

## Verdict

The report does not supply a universal three-production source and therefore does not settle
`GPCP(3)` or `M₃(4)`. It does remove the arbitrary-trace obligation for a broad, purely local
source class: if every output is nonempty and its head occurs nowhere in the corresponding
consumed word, every aggregate endpoint equality is a lawful execution certificate.

The Neary role merger and direct arbitrary-substring semi-Thue transcription remain rejected.
Their discussion adds no theorem beyond the existing closed-serialization and missing-context
obstructions.

## Checked Debt Argument

For the first production `x` in a trace, an endpoint equality has the form

```text
source · βₓ · β(rest) = αₓ · α(rest) · target.
```

The two initial words `source` and `αₓ` are prefixes of the same word. If `αₓ` is not a prefix of
`source`, then `αₓ=source·d` for a nonempty word `d`, and cancellation gives

```text
βₓ · β(rest) = d · α(rest) · target.
```

The left side begins with `head(βₓ)`. The right side begins with a symbol of `αₓ`. Head separation
makes the equality impossible. Thus the first rule is applicable. Lean iterates this argument,
constructs every intermediate queue, and proves

```text
EndpointEquation system source target trace
  ↔ DerivesAlong system trace source target.
```

It separately derives the repository's stronger `EndpointPrefixForcing` interface, so the prior
literal three-pair compiler applies without modification.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every false endpoint witness has a first nonempty underflow debt | promotion | free-monoid prefix comparison; embodied in the checked first-step argument |
| A fresh nonempty output head forbids every underflow | promotion | `derivesAlong_of_endpointEquation_of_headSeparated` |
| Head separation implies endpoint prefix forcing for all boundaries | promotion | `endpointPrefixForcing_of_headSeparated` |
| The endpoint equation is exact on the head-separated class | promotion | `endpointEquation_iff_derivesAlong_of_headSeparated` |
| A universal three-production family satisfies the criterion | rejected | no family or undecidability proof is supplied |
| Neary's erasure roles can be merged through one phase residue | rejected | conflicts with the previously audited exact lower-channel identities |
| `GPCP(3)` or `M₃(4)` follows | rejected | the universal source remains missing |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: arbitrary-trace soundness as an obligation for head-separated candidates.
SHARPENED: the native-source leaf is now an undecidability construction problem with a local
           causality invariant, not a simultaneous compiler-correctness problem.
REMAINS: three productions, unbounded open word residue, and mixed recurrent drift under every
         positive symbol weighting.
```

## Artifact

- [`EndpointPrefixCompiler.lean`](../MatrixMortality/EndpointPrefixCompiler.lean)

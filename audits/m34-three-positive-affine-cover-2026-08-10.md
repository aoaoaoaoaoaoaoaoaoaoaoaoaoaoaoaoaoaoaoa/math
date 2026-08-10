# Three-Positive Affine-Cover Audit

**Date:** 2026-08-10  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `cb9d7b68f3829beda2c7f1c0559710967c9c15f6` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a79634c-3f10-83ea-9779-8608df6a0cae

## Verdict

No ordinary `GPCP(3)`, three-state scalar-zero family, or master closure is obtained. The report
does, however, remove the positive-spelling ambiguity completely. Carvalho's exponent-one source
can be embedded into one affine exponent slice of `F₂`, and three positive letters cover that
slice exactly. What remains is a domain-extension and joint-detection problem, not positive
normalization.

The report's separate `F×F×ℤ` lower bound is accepted only for the full independent carrier. It
does not apply to the correlated graph of the program-dependent maps.

## Checked Affine Cover

Evaluate positive letters by

```text
x ↦ a,       y ↦ b,       z ↦ b⁻¹a⁻¹
```

and assign weights `1,0,−1`. Lean defines the homomorphism counting the exponent of `a` and proves

```text
exp_a(eval(w)) = #x(w) − #z(w)
```

for every arbitrary positive word. Since the triangle evaluation is already surjective onto
`F(a,b)`, every element of exponent `d` has a positive spelling; the displayed identity forces
that spelling to have weight exactly `d`. Lean packages this as a surjection between the two
subtype slices for every integer `d`.

The positive identity word `xyz` evaluates to one and has weight zero. Padding therefore preserves
both semantic value and the affine constraint.

## Audited Nielsen-Schreier Seam

For a rank-`r` free source with primitive `κ`, put `d=r−1`. The index-`d` subgroup defined by
`a`-exponent divisible by `d` has Schreier basis

```text
a^d,       a^i b a^-i       (0≤i<d)
```

and rank `d+1=r`. A basis isomorphism may therefore be chosen so that ambient `a`-exponent equals
`dκ`. This transports Carvalho's source equivalence to existence of a positive word with exact
weight `d` and equal transported morphism values. The standard Schreier calculation is accepted
as paper algebra; it is not a hidden Lean theorem.

## Full-Pair Boundary

A detector on all independent triples `(a,b,n)∈F×F×ℤ` would force two commuting faithful free
subgroups of `GL₃` at `n=1`. The characteristic-zero centralizer classification excludes this.
The argument does not touch the correlated subgroup `u↦(g(u),h(u),κ(u))`; treating it as a full
direct product would overstate the result.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Three positive letters preserve the affine exponent exactly | promotion | `firstExponent_triangleEvaluate` |
| Every prescribed exponent slice has positive spellings of the matching weight | promotion | `triangleSliceEvaluate_surjective` |
| Positive identity padding preserves value and weight | promotion | `triangle_identity_padding` |
| Carvalho's source embeds into a finite-index exponent slice | audited | explicit Nielsen-Schreier basis |
| A full independent `F×F×ℤ` detector exists in dimension three | rejected | commuting-faithful-factor obstruction |
| The full-pair obstruction excludes the correlated equalizer graph | rejected | independence hypothesis fails |
| The affine slice is already ordinary `GPCP(3)` | rejected | subgroup-domain and weight constraints remain |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: positive spelling selection and identity padding as obstacles.
SHARPENED: extend one program-correlated equalizer from a finite-index subgroup and enforce one
           exact affine weight using the same three controls.
FORBIDDEN: representing two arbitrary free-group values plus an independent counter in GL₃.
```

## Artifact

- [`PositiveFreeCancellation.lean`](../MatrixMortality/PositiveFreeCancellation.lean)

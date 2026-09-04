# M₃(4) Pump-Family Prefix-Kernel Extinction Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `217b3f9` on `wave3-m34-transverse`
**Formal composition:**
[`MixedPrimeAddressInterleavingCollapse.lean`](../MatrixMortality/MixedPrimeAddressInterleavingCollapse.lean)
**Certificate:**
[`certify_mixed_prime_pump_prefix_kernels.py`](../tools/certify_mixed_prime_pump_prefix_kernels.py)

## Verdict

None of the `23` Cayley–Hamilton pump families has a positive proper prefix pair with one affine
action, at any pump depth. Combined with `G3-S27`, every uniform single-cut address insertion into
these relations is forced to an endpoint. `G3-S24` and `G3-S25` already reject those prefix- and
suffix-cloak endpoints. Thus all `23` families are impossible at every single insertion position,
including proposals with different initial cuts on the two relation sides.

## Count-Walk Induction

For a relation pair `Lₖ,Rₖ`, let

```text
Δₖ(j)=#D(Lₖ[0:j])−#D(Rₖ[0:j]).
```

A prefix action collision requires `Δₖ(j)=0`: `G3-S27` proves that equal mixed-prime slopes have
equal length and Parikh vector. The certificate classifies every positive proper zero of every
`Δₖ` by an exact two-cell recurrence.

After at most two transient depths, the synchronized letter-increment word has the exact lasso
`H·C^(k−k₀)·T`, where `C` is a zero-sum two-cell period. Hence there is a recorded `p₀` and
constant pair `(a,b)` such that increasing the pump depth inserts that pair into the complete
count walk at position `p₀+2k`:

```text
Δₖ₊₁ = Δₖ[0:p₀+2k] · (a,b) · Δₖ[p₀+2k:].
```

The finite transients are checked exactly. Twelve families then insert a pair without zero, so
their proper zero set never grows. Eleven insert a pair with exactly one zero, creating exactly
one new balanced cut per depth. The base walks contain `31` proper balanced cuts in total. Every
fixed cut has an exact stationary-prefix certificate, and every transient defect is nonzero.

The eleven ladder families are

```text
l31-01  l31-02  l31-04  l31-06
l32-02  l32-05  l32-06  l32-07  l32-08  l32-13  l32-15.
```

Each moving prefix has an exact pump-power lasso whose finite bridge conjugates the pump to
opposite right extensions `DT/TD`. Their common slope is `2/5`. If `δ` is the current offset
defect and `s` the common prefix slope, the certificate checks the exact fixed-point identity

```text
(1−2/5)δ+s(offset(left macro)−offset(right macro))=0.
```

Consequently `δₙ₊₁=(2/5)δₙ`. Every recorded seed defect is nonzero, so no ladder cell ever becomes
an action collision. Both the count walk and moving prefixes are finite-word lassos, so this is an
induction, not a depth cutoff. Replay through depth `64` audits the symbolic formulas.

The canonical payload digest is

```text
da3c44fb5bd36bd4094917a3c6ac811f8c846bb4cc6494ebf1ee0c333cf6136c
```

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every balanced proper prefix belongs to one base cell or one recorded ladder | promotion | exact two-cell count-walk induction |
| The 31 base balanced prefixes induce equal affine actions | rejected | exact rational defects, all nonzero |
| Any of the eleven infinite balanced ladders reaches zero defect | rejected | exact `δₙ=(2/5)ⁿδ₀` recurrence |
| Any of the 23 families has a proper prefix kernel pair | rejected | complete symbolic certificate |
| Different cut positions on the two relation sides survive | rejected | formal slope homogeneity forces equal cut lengths |
| Any single-cut placement in the 23 families realizes the physical fork | rejected | `G3-S27` plus `G3-S24/S25` |
| A multi-cut or stateful interleaving is impossible | open | outside the one-cut theorem |
| `M₃(4)` follows | rejected | new relations, multi-cut routing, and converse remain |

## Master Delta

```text
DEAD: every single insertion position in all 23 Cayley–Hamilton pump families.
COMBINED: every currently explicit infinite kernel family is dead under uniform one-cut interleaving.
LIVE: multi-cut/stateful address routing, a new kernel geometry, or a separate two-offset channel.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The exact symbolic certificate, warning-as-error Lean build, whole-environment linter, reviewed
axiom snapshot, Lean LSP diagnostics, Ruff, ty, forbidden-aperture scan, and source scour pass.

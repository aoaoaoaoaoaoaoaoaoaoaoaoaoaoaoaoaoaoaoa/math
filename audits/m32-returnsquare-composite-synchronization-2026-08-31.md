# M₃(2) Composite ReturnSquare Synchronization Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

Prime-power ReturnSquare is classified, but the rational-root theorem initially leaves a
multi-prime base `q` with arbitrary q-smooth numerator and denominator exponents. The closure
hypothesis is that mortality still occurs only at `c=−q⁻ⁿ`. This audit tests the first
primewise-intersection step; it does not assume the hypothesis.

## Support

For integer return scales `tᵢ`, the normalized bridge polynomial has constant coefficient
`T=∏tᵢ` and leading coefficient `(−1)^kT²`. Lean now retains the unspecialized rational-root
consequence:

```text
|num(d)| ∣ |T|,             den(d) ∣ |T|².                    (1)
```

For ReturnSquare waits, `T=q^E`. Thus every prime in the canonical numerator or denominator of a
nondegenerate bridge root divides `q`.

## Positive-Valuation State

Fix `p∣q`, put `s=vₚ(q)>0`, `δ=vₚ(d)>0`, and write the normalized product's first
column as `(P,Q)`. One return at scale `t` acts by

```text
P' = t((1−dt)P − d(t−1)Q),
Q' = (t²−1)(P+Q).                                             (2)
```

Every scale has positive p-adic valuation. Therefore `1−dt` and `t−1` are units. Induction
from the rightmost return proves:

- `Q` is always a unit;
- while the accumulated scale valuation `σ≤δ`, `P` is nonzero with valuation exactly `σ`;
- once `σ>δ`, `P` is either zero at the unique crossing or has valuation strictly greater
  than `δ`.

Suppose the word is `[h] ++ tail` and its upper entry vanishes. A singleton cannot vanish under
`δ>0`. In (2), the leftmost cancellation equates a unit multiple of the tail's `P` with a
unit multiple of `d`, so the tail upper coordinate has valuation `δ`. The state trichotomy
forces

```text
tail ≠ [],                  δ = s·waitExponent(tail).         (3)
```

The matrix-product order and the `tail=[]` boundary are explicit in Lean. Applying (3) at two
positive base-prime valuations yields

```text
vₚ(d)vₗ(q) = vₗ(d)vₚ(q).                                  (4)
```

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| canonical numerator and denominator satisfy (1) | promotion | Lean checked without a prime-power hypothesis |
| every fraction prime divides the base | promotion | Lean checked |
| a positive valuation is an arbitrary multiple of the base valuation | replaced | sharpened to the exact common proper-tail exponent (3) |
| positive valuations at different base primes may choose different depths | rejected | contradicted by (4) |
| negative valuations obey the same common exponent | open | the forward unit-state induction does not control denominator crossings |
| arbitrary-composite ReturnSquare is classified | open | no theorem excludes unequal denominator depths and no exact counterexample is known |

Exact searches found no nonresonant rational root for composite bases through the tested finite
radii, but no computational completeness claim is retained. Arbitrary scale chains cannot replace
the geometric hypothesis: scales `(2,4,2,14)` have the exact nonresonant root `d=7/8`.

## Wound

```text
MASTER VERDICT: arbitrary-composite ReturnSquare remains open
REMOVED: arbitrary q-smooth numerator assignments; unsynchronized positive-prime depths; singleton positive-valuation cancellation
EXACT THROAT: synchronize or exclude negative denominator valuations, or construct an exact geometric-scale counterexample satisfying (1)–(4)
```

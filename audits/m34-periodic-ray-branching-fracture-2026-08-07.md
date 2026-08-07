# Periodic-Ray and Branching-Fracture Audit

Date: 2026-08-07

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a76010e-2fc4-83ea-84fa-fccba46fac05)

## Verdict

The report meets its periodic-escape threshold but does not settle `M₃(4)`. Its `bcbb` grammar,
affine section, no-false-zero arithmetic, all-control decoder, and explicit integral lift are
correct and now Lean-checked. The fixed body `bcbb` is therefore unsuitable for a three-state
same-zero lower bound.

The report's adjacent `bcbc` body identifies the correct next obstruction. Its exact grammar is
not promoted here: the written cancellation argument compresses several dead residual states
into an induction that does not state its invariant. Instead Lean proves the stronger fact needed
to kill the present compiler mechanism: `bcbc` contains an injective equal-length binary family
of terminal words. Hence no single affine row section of the injective positional decoder can
recognize its complete terminal language.

## Exact `bcbb` Language

Let `B=bbb`, `C=cbb`, and let `o(b)=b`, `o(c)=bcbbb`. For a width-three history `h`, write `C(h)`
for its consumed word and `P(h)` for its produced word. Lean proves

```text
C(h)b = bP(h)  ↔  h = (B,C)^k
```

for a unique `k`. Length comparison gives twice as many strokes as `c`-heads. Counting `c`
forces every wake to be `bb`. Comparing the first `c` position then forces exactly one `B`
before the first `C`; cancellation recurs.

Terminal normalization forces the initial strokes `cbc,B`, so the complete role language is

```text
P₀Q* ,

P₀ = R_c E_b E_c R_b E_b E_b,
Q  = R_b E_b E_b R_c E_b E_b.
```

This is the bidirectional unbounded classification, not an inference from the two former
witnesses.

## Exact Affine Section

Assign role digits `1,2,3,4` in base five and let `V` be the most-significant-digit-first value.
Then

```text
V(P₀)=8668,        V(Q)=5443,
κ=5443/15624,      α=5417371/9765000.
```

For every role word `w`, Lean proves

```text
κ + V(w) − α5^|w| = 0  ↔  w=P₀Q^k.
```

The converse clears denominators and reduces modulo `15624=5⁶−1`. Since
`gcd(5443,15624)=1`, a zero forces `5^|w|≡1 mod 15624`. The residues of exponents `0,…,5` force
`6∣|w|`; the empty word is rejected by `κ−α=−129/625`. At the resulting length, injectivity of
base-five coding forces the entire word.

The singular controls are

```text
H_b = [[1,−1,2], [0,0,−5], [0,0,5]],
H_c = [[1,−1,3], [0,0,−5], [0,0,5]],
H_t = [[1, 0,0], [0,−1, 0], [0,0,1]].
```

For every arbitrary control word `y`, including empty, toggle-only, adjacent-toggle, and malformed
words, their column state is

```text
(κ+V(D(y)), phaseSign(y)5^|D(y)|, 5^|D(y)|)ᵀ.
```

The phase-blind row `(1,0,−α)` therefore has exactly the zeros of the `bcbb` paired coefficient.

## Integral Mortality Family

Clearing only the outer-product separator by `Δ=152568360000` gives

```text
Ŝ = [[ 53150895000, 0, −29486750353],
     [152568360000, 0, −84641004504],
     [152568360000, 0, −84641004504]].
```

Together with `H_b,H_c,H_t`, this is an explicit four-generator integral family. Lean checks its
cast as `(Δγ)λ`, applies the unconditional separator theorem to every product and separator
placement, and proves

```text
IsMortal{H_b,H_c,H_t,Ŝ}
  ↔ ∃y, pairedCoefficient ℚ 3 bcbb y = 0.
```

The family is mortal because `P₀` is terminal. This is an exact fixed-instance compiler, not a
source-uniform undecidability reduction.

## Certified `bcbc` Branching

For `o(c)=bcbcb`, both four-stroke blocks

```text
flat   = BBB,CBC,BBB,CBC,
nested = BBB,BCB,CBB,CBC
```

are null. Null histories are closed under concatenation. Lean maps every bit word injectively to
the corresponding concatenation of `flat` and `nested`; all images have four strokes per bit.
Prepending the forced terminal strokes `CBC,BCB` gives an injective terminal family whose role
words all have length

```text
6 + 12n
```

for bit words of length `n`. Thus there are at least `2^n` terminal role words at one length.

At any fixed length, an affine equation `κ+V(w)=α5^|w|` fixes one value of the injective code and
therefore at most one word. `BranchingHistory.no_affine_positional_section` formalizes the
contradiction already from the two one-bit forks. The same width argument excludes any fixed
finite union of such rays, although that cardinal corollary is not separately encoded in Lean.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `bcbb` null histories are exactly `(bbb,cbb)^k` | promotion | Lean theorem `PeriodicHistory.bcbbNull_iff` |
| The complete `bcbb` terminal language is `P₀Q*` | promotion | Lean theorem `PeriodicHistory.bcbb_terminal_match_iff` |
| The displayed affine section has no false zero | promotion | Lean theorem `PeriodicHistory.bcbbAffine_zero_iff` |
| The displayed controls match the paired coefficient on every control word | promotion | Lean theorem `PeriodicHistory.bcbb_periodicCoefficient_zero_iff_paired_zero` |
| The four displayed integral matrices have the exact mortality converse | promotion | Lean theorem `PeriodicHistory.bcbbIntegralFamily_mortal_iff_paired_zero` |
| The reported general unique-`c` cyclic family | audited, not formalized | position proof checks; no present master obligation depends on it |
| The complete `bcbc` grammar is `FD(B(DC)*F)*` | not promoted | bounded checks agree, but the report omits the invariant needed by its dead-residual induction |
| `bcbc` has exponentially wide fixed-length terminal slices | promotion | Lean injective binary fork and common-length theorems |
| One affine positional section recognizes `bcbc` | rejected | Lean theorem `BranchingHistory.no_affine_positional_section` |
| `bcbc` needs four states under arbitrary rational same-zero representations | open | no common-shift lower bound supplied |
| `M₃(4)` follows | rejected | fixed-instance compilation is not source-uniform |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: bcbb as a lower-bound candidate; every single affine row section of the injective
         positional decoder as a compiler for bcbc; fixed-width and finite-union periodic-ray
         descriptions as a universal account of terminal histories.
REMAINS: compile the branching bcbc terminal language by genuinely two-dimensional singular
         dynamics, or prove its rational same-zero dimension is at least four under the common
         positive shifts.
DISTANCE: the first exact noncyclic obstruction is isolated. The next attack can work on one
          explicit admissible body and need not revisit grammar discovery, positional digits,
          separator placement, or denominator clearing.
```

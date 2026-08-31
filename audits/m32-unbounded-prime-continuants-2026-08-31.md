# M₃(2) Unbounded Prime Continuants Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The recurrence-digit continuant language from `R32-O23` might still have admitted a finite
dictionary of upper-triangular macro words: classify a bounded stock of cancellations, factor
every longer upper-triangular word into that stock, and reduce endpoint reachability to a finite
macro semigroup. This audit tests that grammar, not decidability of the whole continuant language.

It fails. The fixed cubic recurrence contains upper-triangular words of unbounded length that
cannot be split into two nonempty upper-triangular words. Consequently no bounded-length
dictionary of upper-triangular macros generates every upper-triangular return word by
concatenation.

## Projective Cycle

Let `E=(1,0)` and define four finite rays

```text
P₀=(31,−30),  P₁=(−31,12),  P₂=(−29,−30),  P₃=(1,−18).
```

Lean checks the six exact one-step actions

```text
M₂E    = 3P₂,       M₈P₂  = 90P₃,
M₇P₃  = −12P₀,     M₁₅P₀ = 120P₁,
M₂₁P₁ = 1458P₂,    M₁₉P₁ = −6648E.                    (1)
```

Thus the word `[7,8,21,15]`, written in left-to-right matrix-product order and therefore applied
to rays from right to left, closes the projective cycle at `P₀`:

```text
M₇M₈M₂₁M₁₅ P₀ = −188956800 P₀.                        (2)
```

The entry word `[7,8,2]` sends `E` to `−3240P₀`; `[19,15]` exits from `P₀` through `P₁` back to
`E`. For `k≥0`, put

```text
Wₖ = [19,15] [7,8,21,15]ᵏ [7,8,2].                    (3)
```

Lean proves

```text
|Wₖ|=5+4k,
M(Wₖ)E = ((−188956800)ᵏ(−3240)·120·(−6648))E,
```

so every `Wₖ` is upper triangular.

## Proper-Suffix Census

The `k=0` tail has exactly the nonempty suffixes `[7,8,2]`, `[8,2]`, and `[2]`; (1) sends them
to nonzero multiples of `P₀`, `P₃`, and `P₂`. Adding one cycle introduces three new proper
suffixes beginning at waits `8`, `21`, and `15`; they land on nonzero multiples of `P₃`, `P₂`,
and `P₁`. The full enlarged tail returns to `P₀`. Induction on `k` therefore proves that every
nonempty tail suffix lands on one of the four finite rays.

The proper suffix of `Wₖ` beginning at its second letter is `[15]` followed by the tail and lands
on `P₁`; all later proper suffixes are covered by the tail induction. Each finite ray has nonzero
lower coordinate. Hence every nonempty proper suffix `S` of `Wₖ` satisfies

```text
M(S)₁₀ ≠ 0.                                             (4)
```

If `Wₖ=L ++ S` is a nontrivial split, `S` is a nonempty proper suffix, so (4) makes the right
factor nontriangular. Thus `Wₖ` is prime under concatenation inside the language of
upper-triangular return words.

## Grammar No-Go

Suppose a dictionary consists only of nonempty upper-triangular words and every
upper-triangular word factors into dictionary members. A factorization of `Wₖ` into at least two
members produces a nontrivial split whose two products are upper triangular, contradicting (4):
products of `2 × 2` upper-triangular matrices remain upper triangular. A one-member factorization
requires `Wₖ` itself to be in the dictionary. Since `|Wₖ|=5+4k` is unbounded, neither a finite
dictionary nor any dictionary with a uniform member-length bound can cover the language this
way.

This does not prove that the triangular-word language is nonregular, that no finite automaton can
recognize it, or that the full endpoint-reachability problem is undecidable. A recognizer need not
factor accepted words into accepted macro words.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the six ray transitions (1) hold | promotion | Lean checked |
| the four-letter cycle closes with multiplier `−188956800` | promotion | Lean checked |
| every `Wₖ` is upper triangular and has length `5+4k` | promotion | Lean checked |
| every nonempty proper suffix of `Wₖ` is nontriangular | promotion | Lean-checked uniform induction, including `k=0` |
| upper-triangular words have unbounded concatenation-prime members | promotion | Lean checked |
| a bounded triangular-macro factorization grammar covers the language | rejected | contradicted by the family `Wₖ` |
| no finite automaton recognizes the language | open | irreducible concatenation length does not imply nonregularity |
| the continuant language or `M₃(2)` is decided | open | the family is an obstruction, not a classification |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: bounded-length factorization into triangular macro words; finite triangular-macro dictionaries whose accepted words factor into triangular members
EXACT CUBIC THROAT: recognize or decide the recurrence-digit continuant without assuming accepted-word factorization, or find a global descent invariant compatible with the internal four-ray cycle
```

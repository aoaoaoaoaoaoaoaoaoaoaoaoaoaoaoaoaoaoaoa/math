# M₃(2) Projective-Neutral Insertion Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The fixed cubic comparator assumes complete reader-writer blocks. One possible repair would ask
another terminal context in the same homogeneous matrix representation to count those blocks or
reject missing boundaries.

## Generic Identity

Let `Π` be the word product of an arbitrary alphabet of `2×2` rational matrices. Suppose a word
`N` satisfies

```text
Π(N)=λI.
```

For all context words `L,R`, Lean proves directly from word concatenation and matrix
associativity that

```text
Π(LNR)=λΠ(LR).
```

If `λ≠0`, scalar multiplication is faithful, so

```text
Π(LNR)=0 ↔ Π(LR)=0.
```

The statement is uniform in the generators, alphabet, neutral word, and contexts.

## Cubic Specialization

For either radix bit `b`, `R32-S58` supplies a physical positive reader and proves

```text
Π(reader_b writer_b)=λ_b I,       λ_b≠0.
```

The generic theorem therefore gives, for every pair of physical wait words `L,R`,

```text
Π(L reader_b writer_b R)=0 ↔ Π(LR)=0.
```

Correct blocks are not merely hard to recognize in the same component. They are semantically
absent from its zero language.

## Radix-Carry Witness

The same obstruction survives beyond correct pairs. Let `G₁` be the true writer and let `R₀,R₁`
be the exact readers. Lean checks

```text
(R₀G₁)⁴ G₁ (R₁G₀)²⁵ R₁ = 25³⁰I.
```

After projective normalization, the two mismatch signs are translations by `±125/48`, the clock
conjugates a translation by the ratio `4/25`, and the displayed identity is the radix carry
`−4+(4/25)25=0`.

Lean composes the physical projective realizations into one word, proves its scale nonzero,
proves that all `38,742` waits are positive, and proves its exact length. The generic insertion
theorem then makes this malformed word invisible in every physical context.

## Adjudication

| Claim | Judgment |
| --- | --- |
| projective-identity insertion scales every contextual product | Lean checked |
| nonzero scaling preserves and reflects zero | Lean checked |
| both correct cubic read-write blocks satisfy the hypothesis | Lean checked |
| the malformed radix-carry word is a nonzero scalar identity | Lean checked |
| every wait in the carry word is positive | Lean checked |
| the carry word has length `38,742` | Lean checked |
| the same homogeneous component can count correct blocks | rejected |
| the same homogeneous component can enforce their boundaries | rejected |
| the clock alone enforces one bounded signed digit per level | rejected |
| an independent phase/control component is impossible | not claimed |
| a source grammar saturated under neutral insertion is impossible | not claimed |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: same-component enforcement of block syntax or bounded clock-level multiplicity
GAINED: a generic contextual congruence theorem and an explicit positive radix-carry witness
EXPOSED: independent control or quotient-saturated syntax as mandatory compiler architecture
NEXT: stop adding terminal contexts to the neutral component; move syntax into a separate phase
```

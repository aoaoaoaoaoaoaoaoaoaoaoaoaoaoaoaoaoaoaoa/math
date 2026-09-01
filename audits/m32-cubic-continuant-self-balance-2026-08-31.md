# M₃(2) Cubic Continuant Self-Balance Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S59` proves sound comparison after exactly one cleanup reader per clocked check. A compiler
cannot assume that an arbitrary witness chooses the correct cleanup length. The endpoint itself
must reject every shorter and longer cleanup suffix.

## Affine Residual

Normalize the true radix clock and its reader as inverse affine matrices. Their common fixed
point is `f=149/252` and the clock ratio is `q=4/25`. If the signed mismatch schedule is
`e₀,…,eₙ₋₁` and the word contains `m` cleanup readers, exact multiplication gives

```text
r=qⁿq⁻ᵐ,
t=f(1−r)+(125/48)S,
S=Σᵢeᵢqⁱ.
```

Lean proves this identity by induction for the clock product, the inverse-clock power, and their
composition.

## Endpoint Equation

For an arbitrary affine matrix `[[r,t],[0,1]]`, the split bridge satisfies

```text
M₀M₁₂ [[r,t],[0,1]] M₁₂M₈M₁₂M₁₂M₁₅M₈M₀
  =−15092357529600000(r+4t−1)M₀.
```

Substitution of the clock residual shows that bridge vanishing is equivalent to

```text
S=−(344/2625)(1−qⁿq⁻ᵐ).                     (1)
```

## Valuation Parity

Lean proves by induction on signed digits that every nonzero `S` has valuations

```text
v₂(S)=2j,       v₅(S)=−2k
```

for natural `j,k`. If `n>m`, the right side of (1) has valuation
`v₅=−2(n−m)−3`. If `m>n`, it has valuation `v₂=3−2(m−n)`. Each is odd and therefore cannot
equal the corresponding even valuation of `S`. Thus (1) forces `m=n`. It then reduces to `S=0`,
and the modulo-four signed-radix argument forces every digit to be zero.

## Physical Lift

Each physical reader-writer-clock block realizes its normalized block with a nonzero rational
scale. Lean composes those scales with an arbitrary repeated cleanup reader, inserts the result
into the physical endpoint word, and cancels only a proved nonzero scalar. The final theorem is

```text
wordProduct falseWaitReturn (continuantCheckedZeroWordWithCleanup checks m)=0
↔ m=checks.length ∧ ∀check∈checks, check.1=check.2.
```

Every wait between the two singular endpoint returns is strictly positive.

## Adjudication

| Claim | Judgment |
| --- | --- |
| every nonzero signed radix has even `2`-adic valuation | Lean checked |
| every nonzero signed radix has even `5`-adic valuation | Lean checked |
| the arbitrary-cleanup affine residual has the displayed ratio and shift | Lean checked |
| the split bridge reads `r+4t−1` exactly | Lean checked |
| deficient cleanup is impossible by `5`-adic parity | Lean checked |
| excess cleanup is impossible by `2`-adic parity | Lean checked |
| the physical bridge self-enforces cleanup count and all bit comparisons | Lean checked |
| arbitrary raw waits must form complete clocked check blocks | open |
| the fixed gadget alone gives an instance-dependent mortality reduction | rejected |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: the exact cleanup-count assumption from the designated cubic comparator
GAINED: an endpoint-enforced counter with no extra control state
EXPOSED: block formation and instance-dependent target geometry as the remaining compiler seams
NEXT: classify arbitrary M₀-punctuated words, then add a nonprojective phase or twisted endpoint
```

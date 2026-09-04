# M₃(2) Cubic Internal-Pump Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S64` turns the fixed cubic scalar bridge into reachability of one accepting ray. A source
decoder could survive the known accepting collision only if nonaccepting paths remained unique
after quotienting global scalar-identity insertions. Internal ray stabilizers test that hope.

## Two Pumps

Lean checks two exact factorizations:

```text
suffix                          internal ray  loop and scale              prefix landing
[15,29,11,13,7,8]·c            (4,3)         [1,15,2]·(4,3)=7776000(4,3)  M₁₃(4,3)=−408e₀
[12,8,12,12,15,8]·c            (1,4)         [8,33,12]·(1,4)=−32348160(1,4) M₁₂(1,4)=312e₀
```

The suffix scales are `−72590904000000` and `41923215360000`. The two loop products are not
scalar identities: their upper-right entries are nonzero, and Lean refutes equality with `λI`
for every rational `λ`.

For either row, insert the loop `k` times between the prefix and suffix. Lean proves exact length
`7+3k`, positivity of every wait, injectivity as a function of `k`, and source images

```text
29617088832000000·7776000^k e₀,
13080043192320000·(−32348160)^k e₀.
```

Both scales are nonzero for every `k`. Each word therefore gives an exact scalar bridge zero and
an exact full zero product between two copies of the singular return.

## Safe Merge

The first loop yields the distinct words

```text
S =[15,29,11,13,7,8],
LS=[1,15,2,15,29,11,13,7,8]
```

with `Π(LS)c=7776000·Π(S)c`. This merged ray is `(4,3)`, not the accepting ray. Lean further
enumerates every tail of `LS` and proves its separator incidence nonzero. Since source reading
applies the word from the right, no intermediate state of the longer path accepts. Adding the
left prefix `13` then lands on the accepting ray.

This defeats projective source decoding even when accepting states are excluded and global
scalar-identity insertions are quotiented. A lawful quotient must identify non-scalar loops that
stabilize the particular ray being read.

## Adjudication

| Claim | Judgment |
| --- | --- |
| both loop eigenray equations and all seam scales hold | Lean checked |
| neither loop product is a scalar identity | Lean checked |
| every pumped word is positive and has length `7+3k` | Lean checked |
| each pumped family is injective in `k` as literal words | Lean checked |
| both accepting source-image formulas hold for every `k` | Lean checked |
| every pumped word gives a full mortality witness | Lean checked |
| the displayed nonaccepting projective merge holds | Lean checked |
| all source-reading tails of the longer merge word are nonaccepting | Lean checked |
| quotienting every ray stabilizer gives a finite decoder | open |
| the pumped words are irreducible modulo every lawful alias | not claimed |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: two injective infinite positive bridge families with exact all-k Lean certificates
KILLED: unique nonaccepting source decoding modulo only global scalar identities
EXPOSED: the ray-stabilizer congruence as the next unavoidable quotient
NEXT: determine whether non-scalar stabilizers form a finite effective quotient or a free pump
```

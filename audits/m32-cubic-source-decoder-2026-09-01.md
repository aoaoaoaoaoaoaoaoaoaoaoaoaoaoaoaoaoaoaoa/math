# M₃(2) Cubic Separator-Source Decoder Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S67` proves that the binary pump matrices retain every bit transversely but that the fixed
ray-reaching suffix erases this memory from every later zero observation. The remaining local
question is whether the original separator source retains the stack before that collapse.

## Coordinate

In the common-ray basis, the physical separator source has coordinates `(11,−123)`. If `D(β)`
is the reversed affine address and `Q(β)` the ratio product from `R32-S67`, then the normalized
source image is

```text
(11−123D(β), −123Q(β)),
```

and its projective coordinate is

```text
s(β)=(11/123−D(β))/Q(β).                         (1)
```

The empty word has positive coordinate. Every nonempty word has negative coordinate.

## Valuation Decoder

Lean represents each affine address as `N/E`, where every denominator is a unit modulo `197`.
The residue recurrence is

```text
r([])=0,       r(0::β)=88+29r(β),       r(1::β)=66  in 𝔽₁₉₇.
```

The affine map for zero has fixed point `25`, and `29⁴⁹=1`. Lean proves

```text
(r(β)−25)⁴⁹ ∈ {1,−1},
```

whereas `(109−25)⁴⁹=183`; `109` is the residue of `11/123`. Hence
`v₁₉₇(D(β)−11/123)=0`. Since the false ratio has valuation zero and the true ratio has
valuation one, (1) gives

```text
v₁₉₇(s(β)) = −#{i : βᵢ=1}.                       (2)
```

Equality of source coordinates therefore recovers the true-letter count.

## Real Shell

For every nonempty address, Lean proves

```text
3439607/17712000 ≤ D(β)−11/123 ≤ 49936/230625,
49936/230625 < 625·3439607/17712000.              (3)
```

After (2) fixes the true-letter count, one additional false letter divides `Q` by `625`.
The strict width inequality in (3) makes equality of (1) impossible unless the false-letter
counts also agree. The two counts determine `Q`; then (1) determines `D`; affine-address
injectivity from `R32-S67` determines the complete word.

## Transport

Lean checks the source coordinates, the normalized source formula, projective injectivity of
the normalized action, and transport through the exact physical conjugacy and nonzero physical
scales. Thus

```text
Π(E(β))c = λΠ(E(γ))c  implies  β=γ
```

for the original physical separator source `c` and every rational `λ`.

## Adjudication

| Claim | Judgment |
| --- | --- |
| integral address fraction and modulo-197 recurrence | Lean checked |
| period-49 orbit exclusion of the source residue | Lean checked |
| `197`-adic unit law for every address offset | Lean checked |
| exact nonempty real shell and factor-625 separation | Lean checked |
| valuation recovery of the true-letter count | Lean checked |
| shell recovery of the false-letter count | Lean checked |
| injectivity of the rational source coordinate | Lean checked |
| normalized projective source-action injectivity | Lean checked |
| physical projective source-action injectivity | Lean checked |
| exact census through width `14` | computational cross-check |
| positive left-context equality or zero reader | open |
| arbitrary-word compiler converse | open |
| `M₃(2)` is decided | open |

The bounded cross-check is `tools/certify_cubic_source_decoder.py`; it is not evidence for the
unbounded theorem.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: a projectively faithful source readout of the free binary pump before collapse
KILLED: the claim that the common stabilized ray makes the pump intrinsically write-only
EXPOSED: positive left-context comparison and arbitrary-word syntax as the remaining seams
NEXT: realize target-ray annihilation before the suffix, then prove an all-word converse
```

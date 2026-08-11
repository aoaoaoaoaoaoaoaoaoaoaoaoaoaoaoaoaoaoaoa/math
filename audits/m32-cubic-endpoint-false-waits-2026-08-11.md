# M₃(2) Cubic Endpoint And False-Wait Audit

Date: 2026-08-11

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The surviving non-pure rank-(3,2) fork is reachability between the image and kernel lines of
finitely many singular returns under the infinite unit-return alphabet. The previous free
binary witness did not place its orbit on the actual singular endpoints, leaving open a narrow
geometric impossibility: perhaps the arbitrary cubic twist could not align source, target, and
free selected dynamics simultaneously.

That obstruction is false. One rational physical family aligns the actual endpoints and retains
free selected dynamics. A second family isolates the real wound: its selected alphabet has an
injective free endpoint orbit and no hit, yet seven strictly unselected unit waits reach the
kernel and create a zero. Endpoint geometry closes; arbitrary-wait soundness does not.

## Endpoint Equation

On the cubic trace-zero plane, let `Tₙ` be projected multiplication and let the arbitrary
physical twist be `F∈GL₂(ℚ)`. At a singular index `t`, write `kₜ` for the kernel vector and
`ℓₜ=S kₜ` for the image vector in the trace-pairing symplectic gauge. A unit word
`n₁,…,nᵣ` bridges a right singular return `t` to a left one `s` exactly when

```text
kₛᵀ Ω (F T_n₁)⋯(F T_nᵣ) F S kₜ = 0.                 (1)
```

For fixed cubic data, (1) is one homogeneous polynomial in the four entries of `F`. Choose a
selected unit index `a`, put `P=FTₐ`, and normalize `Rₙ=Tₐ⁻¹Tₙ`. Then every unit return is

```text
Mₙ=P Rₙ,       Rₐ=I.                                  (2)
```

The twist chooses the arbitrary common left factor `P`; the relative selected instruction
`Mₐ⁻¹M_b=R_b` is rigid. Aligning the actual singular source imposes one projective equation
on `P`, leaving two rational parameters up to scalar. A fixed terminal word imposes one more
polynomial equation, while ping-pong conditions are open real inequalities. There is no
dimension obstruction, and the explicit family below supplies the rational witness.

## Common Physical Cubic

Lean defines

```text
A=[[−1,1,0],[0,0,1],[1,0,0]],
U=[[0,−2],[3,0],[0,3]].
```

It proves `det A=1`, `A³+A²=I`, and `A³≠λI` for every rational `λ`. Thus every return
family obeys

```text
M_(n+3)=M_n−M_(n+2).                                  (3)
```

The characteristic polynomial is `X³+X²−1`. Its only possible rational roots are `±1`,
neither a root, so it is irreducible over `ℚ` and is not pure cubic. Explicit left and right
inverses make both physical cuts below rank exactly two in Lean.

For the trace sequence `p_m=Tr(α^m)` of `α³−α−1=0`,

```text
p₀=3, p₁=0, p₂=2,       p_(m+3)=p_(m+1)+p_m.
```

Hence `p_m>0` for every `m≥2`. The trace-plane determinant identity gives
`det Tₙ=p_(n+1)/3`, so the singular index set is exactly `{0}`. Every positive wait is a
unit and `(0,0)` is the only singular punctuation pair.

## Endpoint Alignment With Freeness

For

```text
V*=[[−258,0,−235],[−54,0,−117]],
```

Lean computes

```text
M₀=[[0,−189],[0,−243]],
M₁=[[−774,−46],[−162,126]],
M₅=[[774,−143],[162,−369]],
M₀M₁M₀=0.                                      (4)
```

Thus selected wait one sends the actual singular image to the actual singular kernel.

In the normalized affine coordinate the selected maps are

```text
g₀(z)=(1−5z)/(1−z),
g₁(z)=(1−2z)/(1−2z/5).
```

On `J=[47/10,97/10]` their exact images are

```text
g₀(J)=[475/87,225/37],
g₁(J)=[115/18,105/11],
```

and the two closed intervals are disjoint and strictly contained in `J`. Both maps are
injective there. Comparing the outer letter and cancelling recursively proves that the selected
positive semigroup is free. Equation (4), source alignment, and freeness therefore coexist;
there is no endpoint-placement impossibility theorem.

## Exact False-Wait Family

Keep `A,U` but take

```text
V†=[[8,0,−21],[0,0,−30]].
```

The singular return has image `[79:90]` and kernel `[1:0]`. The selected waits one and five are
upper triangular:

```text
M₁=[[24,58],[0,60]],
M₅=[[−24,−137],[0,−150]].                             (5)
```

Lean proves for every Boolean word that the lower coordinate of its product applied to
`[79:90]` is nonzero. Thus no selected word reaches the actual kernel. In the affine
`z`-coordinate, (5) becomes

```text
g₀(z)=2z/5+11/10,       g₁(z)=4z/25+11/10.
```

Their images of `[1,2]` are disjoint subintervals, and the source `11/10` lies outside both
first-level images. Outer-letter cancellation plus this source separation proves that distinct
selected words have distinct endpoint images. The selected history is free, injective, and
immortal.

Nevertheless the strictly unselected word

```text
[12,12,8,12,12,15,8]
```

has the right-to-left endpoint itinerary

```text
[79:90] →[−49:114] →[41:84] →[−1:100]
        →[26:15] →[7:12] →[1:4] →[1:0].
```

Lean checks every wait is positive and outside `{1,5}`, computes the required returns from the
physical family, and proves the full matrix identity

```text
M₀ M₁₂ M₁₂ M₈ M₁₂ M₁₂ M₁₅ M₈ M₀ = 0.       (6)
```

There is no other singular wait or endpoint pair to blame. Equation (6) is an exact
malformed-wait zero inside the cleanest one-singular non-pure setting.

## Fixed Remaining Recurrence

After one fixed coordinate change, normalize by wait one. The relative return family `Hₙ`
satisfies

```text
H₁=I,
H₅∼diag(2/5,1),
H_(n+3)=H_n−H_(n+2),
```

while `P=FT₁` remains arbitrary in `PGL₂(ℚ)`. The complete bridge predicate is one scalar

```text
δ_(n₁,…,nᵣ)(P)
 = e₂ᵀ(PH_n₁)⋯(PH_nᵣ)P e₂.                         (7)
```

The selected alphabet is `P` and `P diag(2/5,1)`. A universal construction must prove that an
arbitrary positive-wait word solves (7) exactly when a selected word does, and then identify
that selected hit with halting. Selected ping-pong supplies neither implication, as (6) proves.

Finite congruence filters cannot isolate the selected indices by themselves. Modulo any finite
collection of moduli, the invertible ambient has a common period `h`, making waits `1+h` and
`5+h` indistinguishable from the selected waits. A successful syntax guard must use an
unbounded arithmetic invariant or a normalization theorem for the complete recurrence.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| exact singular endpoint polynomial (1) | promotion | audited trace-plane reconstruction |
| arbitrary twist can align source and terminal target | promotion | explicit rational physical witness; terminal zero kernel checked |
| endpoint alignment is incompatible with free selected dynamics | rejected | exact interval ping-pong in the aligned family |
| common ambient and both cuts are physical rank two | promotion | explicit inverse and rank proofs in Lean |
| singular index set is exactly `{0}` | promotion | audited trace recurrence and determinant identity |
| selected `{1,5}` orbit in the false-wait family hits the kernel | rejected | Lean proves a nonzero lower coordinate for every selected word |
| selected ping-pong controls all positive waits | rejected | Lean-checked unselected zero (6) |
| finite congruences isolate the selected alphabet | rejected | ambient periods create indistinguishable unselected waits |
| arbitrary-wait decision or universal all-word compiler | open | no soundness theorem for (7) |
| `M₃(2)` settled by the cubic fork | open | non-pure all-waits reachability remains |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: singular endpoint-placement obstruction; free-orbit placement obstruction; selected ping-pong as an all-waits guard
EXACT CUBIC THROAT: decide or normalize δ_w(P)=0 over every positive wait for the fixed recurrence H_(n+3)=H_n−H_(n+2)
CONSTRUCTIVE OBLIGATION: prove arbitrary-wait soundness before using any selected universal subalphabet
```

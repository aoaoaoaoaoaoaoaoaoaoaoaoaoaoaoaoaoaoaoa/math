# Decimal Setter First-Transfer Audit

Date: 2026-08-30

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

Neither centered reset of the decimal setter can reach a false pole after one completed
transfer. The ordinary reset can reach only the genuine terminal pole at `Z=1`; every other
ordinary-reset case and every distinguished-reset false pole is excluded. The proof couples
the exact `2`/`5` trace shells to complete decimal suffix exhaustion and two disjoint prefix
intervals.

This removes the entire depth-one boundary. It does not prove arbitrary-depth projective
avoidance or `M₅(3)`.

## Setup

Put

```text
ρ=10^β,        μ=(52ρ−7)/9,
E=9(2ρ−7),     G=502ρ−7,
T_z=EP_z+GV_z.
```

For a regular block `u`, let `m` be its upper spelling length, let `P_u` be its punctuated
upper decimal code, and let `V_u` be its lower decimal code. Every regular block ends in an
erasure. Every `P_u`, `V_u`, `E`, `G`, and `μ` is a unit at both two and five. The target trace
shells proved in `MM-S12` are

```text
multi-role erasure:     (ν₂(T_z),ν₅(T_z))=(1,1),
singleton erasure:      (ν₂(T_z),ν₅(T_z))=(β+1,β).
```

The centered recurrence gives two exact successive-pole identities:

```text
Z=0:   P_u T_z=Gμ10^mV_z,                       (1)
Z=1:   (P_u−V_u)T_z=Gμ10^mV_z.                  (2)
```

`DecimalSetterCarry.resetZero_successivePole_identity` and
`resetOne_successivePole_identity` prove these identities over an arbitrary field from the
literal centered pole equations. `poleEquation_shellBalance` proves their simultaneous
valuation consequences.

## Ordinary Reset

For a multi-role target, equation (1) forces `m=1` at both primes. Admissibility leaves only
the single `c` erasure. Its punctuated upper code is

```text
P_u=(502ρ−7)/9=G/9.
```

Since `E+G=90μ`, its output is exactly

```text
(G/E)(10μ−P_u)/P_u=1.
```

A pole at this value is `P_z=V_z`, the genuine terminal match. For a singleton target,
equation (1) would require simultaneously `m=β+1` and `m=β`, which is impossible. Lean proves
the two shell deductions as `resetZero_multiTarget_length` and
`resetZero_singleTarget_impossible`.

Thus no false pole follows one transfer from `Z=0`.

## Distinguished Reset

Assume equation (2), put `D_u=P_u−V_u`, and discard `D_u=0`, which is already a genuine
terminal match. Positivity of the right side forces `D_u>0`. Because both codes end in digit
seven, ten divides `D_u`.

### Multi-role target

The `(1,1)` target shell forces

```text
ν₂(D_u)=ν₅(D_u)=m−1.                          (3)
```

Hence `m≥2`. Let `w=m−1`. The divisibility `10^w∣D_u` says that the two codes share their
last `w` decimal digits. Exactness at two says `2·10^w∤D_u`. Since every encoded digit is odd,
both words could not continue to the left of that shared suffix: their next-digit difference
would be even and supply one more factor of two. Therefore the lower word is exactly the
shared suffix. If `H` is the remaining punctuated upper prefix, then

```text
|H|=β+2,       D_u=H10^(m−1),
H T_z=10μGV_z.                                 (4)
```

`suffix_exhaustion` and `suffix_exhaustion_factorization` formalize this argument for arbitrary
`5/7` words.

Equation (4) makes the prospective target pole

```text
P_z/V_z=G(10μ−H)/(EH)=:π(H).                  (5)
```

Its positivity forces `H<10μ`. The first upper tile now gives a complete trichotomy.

- A leading `b` gives the prefix `5·7^β·5`, namely `H=10μ+5`, contradicting positivity.
- A leading `c` followed by `b` or by the marker gives `H=G/9`, hence `π(H)=1`; this is the
  genuine terminal match.
- Two leading `c` letters give
  `H≤(2501ρ−35)/45`. Exact rational arithmetic yields `π(H)>58/55`.

In the last case, the same formula also gives `π(H)<6`. A `5/7` code ratio in
`(58/55,6)` must compare words of equal length: a shorter numerator is below one, while a
longer numerator exceeds `50/8>6`. At equal length the punctuated upper word begins by at most
`57`, and the lower word begins by at least `55`, so

```text
P_z/V_z<58/55,
```

contradicting (5). Lean checks the exact endpoints in `forcedPole_doubleC_lower`,
`forcedPole_upper`, `targetPrefix_ratio_lt`, and `forcedPole_ne_prefixTarget`.

### Singleton target

The `(β+1,β)` target shell forces

```text
ν₅(D_u)=ν₂(D_u)+1,
ν₂(D_u)=m−β−1.                                (6)
```

The final digit again makes the latter depth positive. With `w=m−β−1`, the same exact-two
argument exhausts the lower suffix and leaves a prefix `H` of length `2β+2`:

```text
D_u=H10^w,
H T_z=10^(β+1)μGV_z.                          (7)
```

Put `h=H/ρ`. Then (7) again says `P_z/V_z=π(h)`. The leading digit gives `h≥50ρ`, while
positivity gives `h<10μ`; therefore `π(h)<6`. A singleton target has `V_z=7` and
`P_z≥G/9`, so `P_z/V_z>6`. Lean checks the two strict bounds and their contradiction in
`singletonPole_gt_six` and `forcedPole_ne_singletonTarget`.

Thus no false pole follows one transfer from `Z=1`.

## Formal Boundary

Lean checks the centered successive-pole identities, joint shell balances, incompatible
ordinary-reset singleton depths, equal/gapped distinguished-reset depths, exact suffix
exhaustion and factorization, and every rational interval comparison used above. The remaining
assembly from Neary role syntax to the displayed prefix trichotomy and first-two-digit code
bounds is audited directly from `nearyUpper`, `nearyLower`, and `nearyMarker`; it is not yet a
single end-to-end Lean declaration.

The arbitrary-depth obstruction begins only after two completed transfers. At that point the
source discrepancy is no longer a difference of two raw punctuated codes, so the suffix
exhaustion theorem cannot simply be iterated. A successful closure must show that the reciprocal
recurrence preserves an equally rigid normalized-suffix representation, or find a false pole.

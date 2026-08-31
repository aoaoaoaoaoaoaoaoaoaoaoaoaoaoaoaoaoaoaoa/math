# Transverse-Dilation Height-Recurrence Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `d3840e6` on `wave3-m34-ucb`

**Salvage record:** `D2-O05`

## Verdict

Strict primitive-height descent does not extend from the step-three shear
family `D2-D09` to one diagonal `S`-unit dilation and one transverse
unipotent shear. Consider

```text
D=[[5,0],[0,1]],        D(z)=5z,
U=[[-2,3],[-3,4]],      U(z)=(-2z+3)/(-3z+4),
p=9/4,                  q=3/5.
```

The subgroup `H=⟨D,U⟩≤PGL₂(ℚ)` is free on `D,U`, and `p` has trivial
stabilizer in `H`. The positive word `UD` is nonidentity and fixes `q`:

```text
q --D→ 3 --U→ q.
```

If some `h∈H` sent `p` to `q`, then `h⁻¹(UD)h` would be a nonidentity
element fixing `p`, a contradiction. Thus `q∉H·p`. The integral matrix

```text
g₀=[[-1,3],[-3,8]]
```

has determinant one and sends `[9:4]` exactly to `[3:5]`; consequently
`H∩g₀Stab(p)` is empty. The instance satisfies the unique-coset promise
with cardinality zero.

Chamber-directed inverse stripping nevertheless cycles:

```text
q --U⁻¹→ 3 --D⁻¹→ q,
height:       5 → 3 → 5.
```

This is an obstruction to strict primitive-height and terminating greedy
inverse reduction. It is not an undecidability theorem, a failure of every
Archimedean invariant, or evidence that this explicit orbit is difficult to
decide. Here the positive target stabilizer itself certifies nonreachability.

## Exact `S`-Arithmetic Scope

Take `S={5}`. The positive generators and transporter lie in
`PGL₂(ℤ[1/5])`:

```text
det(D)=5,       det(U)=1,       det(g₀)=1,
D⁻¹=diag(1/5,1).
```

To put the result in the standard `UCB₂(S)` coordinates, let

```text
C=[[9,2],[4,1]],        det(C)=1,        C·∞=p.
```

Then `H'=C⁻¹HC`, `g₀'=C⁻¹g₀C`, and

```text
H ∩ g₀ Stab(p) = ∅
    iff
H' ∩ g₀' B_S = ∅,
B_S=Stab(∞)∩PGL₂(ℤ[1/5]).
```

All conjugating matrices are integral with determinant one. Lean proves the
stronger rational statement that no represented word equals `g₀s` for any
`s∈GL₂(ℚ)` fixing `p`; the localization claim then follows by restriction.

## Ping-Pong Proof

Use the disjoint projective chambers

```text
X_D={z<1/2 or z>5/2}∪{∞},
X_U={1/2<z<2}.
```

For every nonzero integer `e`, `DᵉX_U⊆X_D`. If `e>0`, then
`5ᵉ≥5` and `5ᵉz>5/2`; if `e<0`, then `0<5ᵉ≤1/5` and
`5ᵉz<1/2`.

For the transverse factor, use the fixed-point chart

```text
w=z/(1-z).
```

The chamber `X_D` maps into `-5/3<w<1`, including `w(∞)=-1`, and
`Uᵉ` becomes `w↦w+3e`. For `e>0`, the translated coordinate is greater
than one; for `e<0`, it is less than minus two. Inverting the chart sends both
ranges into `(1/2,2)`, so `UᵉX_D⊆X_U`.

The source `p=9/4` lies outside both chambers. Every nonzero `D`-power sends it
to `X_D`, and every nonzero `U`-power sends it to `X_U`. Reduced-word induction
therefore puts every nonidentity word applied to `p` in the chamber of its
first factor. No nonidentity word fixes `p`, and the abstract free-product
representation is injective.

Lean checks the matrix powers, both chamber inclusions, the reduced-word
induction, trivial source stabilizer, and representation faithfulness.

## Positive Stabilizer And Empty Coset

Matrix multiplication acts right to left, so the abstract positive word

```text
targetCycleWord = U D
```

acts as displayed in the verdict. Its represented matrix has determinant
five and is not the identity. Every positive power `(UD)ⁿ` fixes `q`; no
inverse letter is needed to create the target recurrence.

The Lean nonorbit proof conjugates `UD` by a hypothetical source-to-target
word and invokes the checked trivial source stabilizer. It then proves the
coset statement through the exact transporter action. No finite quotient,
literature import, numerical search, or unformalized freeness claim enters the
argument.

## Height Recurrence

The chamber parser strips the factor named by the endpoint chamber. Since

```text
q=3/5 ∈ X_U,            3 ∈ X_D,
U⁻¹(q)=3,              D⁻¹(3)=3/5,
```

the parser never reaches the source or a smaller terminal state. The canonical
primitive pairs are `(3,5)` and `(3,1)`, both coprime, with maximum-coordinate
heights five and three. Thus no strict height function depending only on that
primitive Archimedean height can justify termination of this inverse parser.

`D2-D09` remains valid: its alternating equal-step shears force every syllable
to double height from the fixed source. `D2-O05` isolates the missing
hypothesis. A dilation and a transverse parabolic can support a positive
projective stabilizer, so inverse normal-form syntax can revisit the same
primitive point. A general algorithm must detect and quotient such recurrent
stabilizers, enrich the state beyond primitive height, or use a different
global invariant.

## Verification

The following checks pass in the isolated worktree:

```text
lake env lean MatrixMortality/TransverseDilationOrbit.lean
lake build MatrixMortality.TransverseDilationOrbit
lake build MatrixMortality
#lint- in MatrixMortality.TransverseDilationOrbit
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

Every publication-facing declaration is listed in `AxiomAudit.lean`; the
independently generated slice matches `verification/axioms.txt`, and every
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The full combined axiom executable cannot start in this private build because
its unrelated `Frankl.olean` target is absent. No project axiom, proof aperture,
warning suppression, reference PDF, or external literature premise was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `D,U` generate a free subgroup and `p` has trivial stabilizer | promotion | Lean-checked strict ping-pong |
| The positive word `UD` fixes `q` and is nonidentity | promotion | Lean-checked exact action and nonzero off-diagonal entry |
| `q∉H·p` and `H∩g₀Stab(p)=∅` | promotion | Lean-checked conjugated-stabilizer contradiction |
| The instance is an exact promised-empty `UCB₂({5})` coset after integral conjugation | promotion | explicit determinant-one coordinate change |
| Chamber-directed inverse stripping cycles with heights `5→3→5` | promotion | Lean-checked actions, chamber membership, coprimality, and heights |
| Every chamber-directed inverse step strictly descends primitive height | rejected | the inverse parser returns to the same primitive target |
| Every Archimedean or continued-fraction algorithm fails | rejected | only the primitive-height/greedy ratchet is refuted |
| General `UCB₂(S)` is decidable or undecidable | open | this explicit empty instance settles neither direction |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: direct generalization of the D2-D09 primitive-height ratchet to a
         diagonal S-unit dilation plus a transverse parabolic.
ADDED:   one exact promised-empty non-elementary UCB₂({5}) benchmark whose
         positive target stabilizer forces a 5→3→5 inverse cycle.
REMAINS: decide recurrent target-stabilizer components effectively, enrich
         inverse normal forms with cycle data, or bypass height descent.
```

## Artifacts

- [`TransverseDilationOrbit.lean`](../MatrixMortality/TransverseDilationOrbit.lean)
- [`D2-O05`](../SALVAGE.md#d2-o05-promised-empty-free-orbit-inverse-cycle)

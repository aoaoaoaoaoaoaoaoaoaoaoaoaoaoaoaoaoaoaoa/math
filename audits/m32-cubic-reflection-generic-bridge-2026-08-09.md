# M₃(2) Cubic Reflection and Generic-Bridge Audit

Date: 2026-08-09

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The earlier cubic audit left two apparent rank-(3,2) residues: isolated singular cuts in a
non-pure irreducible-cubic return family, and a pure one-singular triple whose two unit returns
differ projectively by an involution. The external attack supplied exact normal forms for both.

Independent reconstruction found a stronger synthesis. The pure normal form automatically
satisfies both nondegeneracy hypotheses of the existing generic reverse-edge compiler. It is
therefore part of GPI₂, not an additional involutive-ratio or Borel-coset frontier. Only the
non-pure reflection orbit remains as an independent cubic fork.

## Common-Left Reflection Form

For an irreducible cubic field `K=ℚ[A]`, rank-two interfaces give an injective linear map

```text
Φ : K → M₂(ℚ),     z ↦ V m_z U.
```

Its image `L` is a three-plane in `M₂(ℚ)`. The determinant polarization

```text
Δ(X,Y)=det(X+Y)−det X−det Y
```

is nondegenerate, so `L⊥` is a rational line. Any nonzero `Q∈L⊥` is invertible: if `Q` had rank
one, factoring `adj(Q)=abᵀ` would make the nonzero functional `bᵀV` vanish on
`K(Ua)=K`. Consequently

```text
Jₙ=Q⁻¹Mₙ,     tr(Jₙ)=0,     Jₙ²=−det(Jₙ)I.
```

Every unit `Jₙ` is a projective involution. Every singular `Jₙ` is a nonzero square-zero rank-one
map whose image equals its kernel. If `uₛ` spans that line, a bridge between singular waits
`s,t` vanishes exactly when

```text
(Jₙ₁Q)⋯(JₙₖQ) ⟨uₜ⟩ = ⟨Q⁻¹uₛ⟩.
```

This is a genuine sharpening of the non-pure residue: the controls form one effectively given
order-three recurrence of reflections. Their indices remain independently chosen, so finite
enumerability of the singular endpoints does not decide the bridge.

## Pure Normal Form

After cyclically placing the unique singular residue first, every realizable pure triple is,
up to simultaneous conjugacy and independent nonzero letter scaling,

```text
(P R, P, P Jμ),
R  = [[1,1],[0,0]],
Jμ = [[0,μ],[1,0]],
P ∈ GL₂(ℚ),   μ ∈ ℚ× ∖ ℚ×³.
```

The reconstruction uses the three determinant-polarization equations of the cubic trace tensor.
Conversely the displayed triple is realized by the rational companion action

```text
Aμ=[[0,0,μ],[1,0,0],[0,1,0]],
U =[[1,0],[0,1],[0,0]],
V =P[[1,1,0],[0,0,1]].
```

Thus the normal form is exact, not merely necessary. Its direct bridge language has row
`r=(1,1)`, controls `G=P`, `H=PJμ`, and column `Pe₁`.

## Formalizer Cut

For the existing reverse compiler, write

```text
alpha(H,r,c) = r · H⁻¹c,
beta(G,H,r,c) = r · H⁻¹G H⁻¹c.
```

In the pure normal form,

```text
(PJμ)⁻¹Pe₁       = μ⁻¹e₂,
(PJμ)⁻¹P(μ⁻¹e₂) = μ⁻¹e₁.
```

Therefore

```text
alpha(PJμ,r,Pe₁)=μ⁻¹,
beta(P,PJμ,r,Pe₁)=μ⁻¹.
```

Since `μ≠0`, both scalars are nonzero. Lean checks the exact equalities in

```text
CubicReturn.pureOneSingular_reverseEdgeScalars.
```

The fixed-language Borel-coset description remains a correct coordinate description, but it is
culled as a frontier node: the checked GPI₂ compiler already consumes precisely this instance.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| common-left reflection normal form | promotion | independently reconstructed over the cubic field |
| non-pure bridge becomes recurrence-of-reflections reachability | promotion | exact endpoint and word calculation |
| pure trace-tensor normal form | promotion | both classification directions reconstructed |
| pure bridge is fixed-language Borel-coset incidence | restatement | correct coordinates, but subsumed by GPI₂ |
| pure one-singular bridge is automatically generic | formalized | both compiler scalars are exactly `μ⁻¹` |
| non-pure reflection orbit is decidable | open | no bound or decision procedure for independently chosen unit indices |
| M₃(2) is decided | rejected | GPI₂ and the non-pure reflection orbit remain open, as does the split guard |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: pure involutive-ratio PI₂ as an independent cubic fork; the fixed-language Borel-coset node
REMAINS: GPI₂ itself; non-pure isolated-cut reachability under the cubic reflection recurrence; the split guard
EXACT CUBIC THROAT: decide the non-pure recurrence-of-reflections orbit or subsume it under a stronger projective decision theorem
```

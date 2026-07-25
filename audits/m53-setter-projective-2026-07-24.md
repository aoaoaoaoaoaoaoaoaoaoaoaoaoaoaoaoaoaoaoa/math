# `M₅(3)` Setter and Projective-Avoidance Audit

**Date:** 2026-07-24
**Target:** three `5 × 5` integer matrices
**Verdict:** candidate algebra accepted; projective avoidance open; free-parameter counterexample
rejected as stated

This audit reconstructs the reusable mathematics from a failed delimiter-fusion attack. Stable
records live in `SALVAGE.md`. Nothing here proves `M₅(3)` undecidable.

## Pure-Power Punctuation Obstruction

Let `G_b,G_c` be the paired four-state data matrices, let `T` be the paired
toggle, and lift them by

```text
Ĝ_x=diag(G_x,0),      T̂=diag(T,0).
```

For a nonempty tag body,

```text
im G_b=im G_c=:H=span(e_a,e_u,e_D),
ker Ĝ_b ∩ ker Ĝ_c=ℚe₅.
```

Suppose `S` realizes an exact isolated toggle in every data context:

```text
Ĝ_iSĜ_j=Ĝ_iT̂Ĝ_j,      i,j∈{b,c}.                 (1)
```

Since each `G_j` surjects onto `H`, equation (1) implies

```text
Sh=T̂h+φ(h)e₅,      h∈H
```

for some linear functional `φ`. In particular,

```text
Se_a=e_a+αe₅,      Se_u=e_u+γe₅.
```

If `(α,γ)≠(0,0)`, the nonzero vector `v=γe_a−αe_u` satisfies `Sv=v`. If
`α=γ=0`, both `e_a` and `e_u` are fixed.

Now let `P=CL` be the paired rank-one separator. If a pure delimiter run also
realized punctuation modulo every exterior data context, then for some `m≥1`
and `λ≠0`,

```text
Ĝ_iS^mĜ_j=λĜ_iP̂Ĝ_j,      i,j∈{b,c}.              (2)
```

The common-kernel calculation reduces (2) to equality of the four-dimensional
payloads on `H`. In the first case, apply it to `v`. If `γ=0`, then `Pv=0`
while `S^mv=v≠0`. If `γ≠0`, then `Pv=γC`, which has a nonzero lower
coordinate while `v∈span(e_a,e_u)`. In the second case, apply it to `e_u`;
one has `S^me_u=e_u` and `Pe_u=0`. Every case is contradictory.

Thus an exact isolated toggle cannot also realize the separator through a pure
power. Mixed delimiter-data words remain possible.

## Side-Normal Data

For each `x∈{b,c}`, write

```text
R_x = [[1,V_x^R,U_x],[0,B_x^R,0],[0,0,A_x]],
D_x = [[1,1,U_x],[0,3,0],[0,0,A_x]],
δ_x = (V_x^R−1,B_x^R−3,0)ᵀ.
```

Then `R_x−D_x=δ_xe_ℓᵀ`. Let

```text
C=(μ,−1,t)ᵀ,   L=(1,0,0),   μ=ternaryCode(10^β),   t=3^(β+1),
r=t/μ,          α=1+2r,      λ=α/μ.
```

The value `r` is fixed by the source boundary. It is not a free delimiter parameter in the
displayed construction.

Put

```text
f=(1,0,r)ᵀ,   p=(0,−1,0)ᵀ,   q=(0,0,2r(1−r))ᵀ,   B=[f p q].
```

Since `β>0`, one has `r>1`, so `B` is invertible. Define

```text
R̄_x=B⁻¹R_xB,   δ̄_x=B⁻¹δ_x,

A_x =
[[R̄_x, δ̄_x, 0],
 [0_(2×3), 0, 0]].
```

The physical delimiter is

```text
S =
[[1,0,0, 0, 0],
 [0,1,0,−1, λ],
 [0,0,1, 0,−1],
 [0,1,0,−1, λ],
 [0,0,1, 0,−1]].
```

Finally set

```text
C̃=(μ,1,0,1,0)ᵀ,   L̃=(1,0,0,0,0).
```

Direct multiplication gives

```text
rank S=3,   rank S²=2,   rank S³=1,   Sⁿ=S³ for n≥3,
S³=e₁L̃.
```

## Regular Semantics

In `B`-coordinates a side vector is `af+xp+yq`; its lower coordinate is `−x`. On a
root vector `(a,x,y,0,0)ᵀ`,

```text
S(a,x,y,0,0)ᵀ=(a,x,y,x,y)ᵀ.
```

The first marker therefore records `x=−ℓ`. Since every `A_x` clears both markers,

```text
A_x(a,x₁,x₂,0,0)ᵀ = R̄_x(a,x₁,x₂)ᵀ,
A_xS(a,x₁,x₂,0,0)ᵀ = D̄_x(a,x₁,x₂)ᵀ.
```

Moreover `B(μ,1,0)ᵀ=C`, so the marked terminal column makes the rightmost data letter an
erasure. A physical word with no `S²` subword therefore has a total suffix decoder:
no delimiter immediately to the right of a data letter selects its rule role, while one
delimiter selects its erasure role. The existing terminal-match theorem supplies the full
converse on this regular language.

## Internal Separator

For the distinguished letter `c`, `U_c=2` and `A_c=3`. Hence

```text
R_cf=D_cf=αf+q.
```

It follows that

```text
E := S²A_cS³ = λC̃L̃.
```

Thus, for every physical word `W`,

```text
EWE = λ² C̃(L̃WC̃)L̃,
EWE=0 ↔ L̃WC̃=0.
```

Every lawful source history has a regular physical encoding, so source halting implies
mortality of `{A_b,A_c,S}`. This proves only the forward reduction.

## Square-Run Transfer

Let `J` be the two-plane

```text
J={(a,x,0,x,0)ᵀ : a,x∈ℚ}=im S².
```

A regular block with side product

```text
M_z=[[1,V,U],[0,B,0],[0,0,A]]
```

followed on the left by `S²` induces on the coordinates `(a,x)` of `J` the matrix

```text
F_z =
[[1+rU,                 −V],
 [κ(A−1−rU),            κV]],

κ=(1+2r)/(2μ(1−r)).
```

Its determinant is

```text
det F_z = κVA ≠ 0.
```

Consequently every segment containing square runs but no `S³` remains nonzero. On the affine
chart `a≠0`, writing the projective coordinate as `x/a`, the induced Möbius map is

```text
Φ_z(x)=κ(A−1−rU+Vx)/(1+rU−Vx).
```

The tested head vanishes exactly at

```text
π_z=(1+rU)/V.
```

Maximal runs of at least three delimiters equal `S³=e₁L̃` and fracture an arbitrary product
into scalar bridges. The right reset line is `x=0`. The special segment `S²A_cS³` maps that
line to `x=1/μ`, the genuine source boundary. Since every `F_z` is invertible, exterior factors
cannot vanish; a whole product is zero exactly when one fractured projective orbit reaches
some pole `π_z`.

At `x=1/μ`,

```text
1+rU−V/μ=(μ+tU−V)/μ.
```

This is zero exactly for the original fixed-boundary terminal match. Therefore the three
matrices prove `M₅(3)` undecidable if and only if every orbit starting from `0` avoids every
pole except a terminal-match pole reached from `1/μ`.

The equivalence is an algebraic normal form. The avoidance property is open.

## Parameter Correction

The external report also treated `r` as a free rational parameter and claimed a malformed zero
at

```text
β=3,   body=bbcc,   r=8735/8978,   word=A_cS²A_c.
```

That claim does not follow from the displayed family.

First, source-boundary alignment requires

```text
B(μ,1,0)ᵀ=(μ,−1,μr)ᵀ=C,
```

and hence forces `r=t/μ`. With arbitrary `r`, the candidate represents a different terminal
column.

Second, direct symbolic multiplication of the displayed matrices gives

```text
L̃A_cS²A_cC̃
  =(2r+1)(17956r²−9246r−8709)/(134(r−1)),
```

not the reported linear factor. It is nonzero at `r=8735/8978` and also at the natural value
`r=81/67`. No checker or alternate free-parameter formulas accompanied the report. The claimed
counterexample and the proposed bad-parameter classification are therefore rejected pending a
complete corrected construction.

## Mechanical Check

An ephemeral SymPy reconstruction verified:

- the ranks and stabilization of `S`;
- `S²A_cS³=λC̃L̃`;
- `det F_z=κVA`;
- the displayed coefficient discrepancy for `β=3`, body `bbcc`.

It printed:

```text
mu=67, t=81, Vc=13578109, Bc=14348907
coefficient=(2*r + 1)*(17956*r**2 - 9246*r - 8709)/(134*(r - 1))
reported coefficient=3*(2*r + 1)*(8978*r - 8735)/(134*(r - 1))
candidate powers, separator identity, transfer determinant, and report discrepancy verified
```

The calculation is a transcription check. The preceding linear-algebra arguments support the
audited records.

## Promotion Boundary

Formalization may proceed through the candidate identities and the square-run normal form.
No undecidability wrapper is lawful until the projective avoidance property is proved for every
source instance and every admissible regular block sequence.

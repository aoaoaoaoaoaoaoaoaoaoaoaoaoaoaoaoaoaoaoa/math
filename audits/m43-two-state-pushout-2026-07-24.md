# `M₄(3)` Two-State Pushout Audit

**Date:** 2026-07-24
**Target:** three `4 × 4` integer matrices
**Verdict:** compiler formalized; source theorem absent

This audit contracts the reusable algebra from the failed `M₄(3)` attacks. It does not preserve
the external reports. Stable statements live in `SALVAGE.md`.

The compiler is formalized in
[`MatrixMortality/TwoStatePushout.lean`](../MatrixMortality/TwoStatePushout.lean). The exact
toggle-fusion obstruction is formalized, in strengthened common-anchor form, in
[`MatrixMortality/TwoStateObstructions.lean`](../MatrixMortality/TwoStateObstructions.lean).

## Accepted Compiler

For `q∈{R,D}` and `x∈{b,c}`, let

```text
M_{R,x} = [[1,V_x^R,U_x],[0,B_x^R,0],[0,0,A_x]],
M_{D,x} = [[1,V_x^D,U_x],[0,B_x^D,0],[0,0,A_x]].
```

Both maps agree on `E={(a,0,c)ᵀ}`. Under

```text
ι_R(a,b,c)=(a,b,c,0)ᵀ,
ι_D(a,b,c)=(a,0,c,b)ᵀ,
```

their pushout is four-dimensional. For a deterministic transition function `δ`, direct
column multiplication verifies the two transition identities in
[`M4-C01`](../SALVAGE.md#m4-c01-two-state-pushout-compiler).

Deleting row and column three in the determinant expansion leaves the private-coordinate
block. Hence

```text
det X_x = A_xB_x^RB_x^D(ε_{R,x}−ε_{D,x}).
```

If the destinations coincide, the common upper plane contributes rank two and the common
private destination contributes one further direction, so `rank X_x=3`.

For a terminal phase `q*`, define phases of `w=x₁…xₙ` from the right by

```text
qₙ=q*,       q_{i−1}=δ(q_i,x_i).
```

Induction on the word gives

```text
X_{x₁}…X_{xₙ}ι_{q*}(v)
  = ι_{q₀}(M_{q₁,x₁}…M_{qₙ,xₙ}v).
```

This covers every binary word; there is no code language.

Let `L=e₁ᵀ`, `C=ι_{q*}(μ,−1,t)ᵀ`, and `P=CL`, with `μ≠0`. Every `X_x` fixes
`e₁`. Fracturing an arbitrary product at all occurrences of `P` gives

```text
(X_{u₀}C)
  (∏_{j=1}^{m−1} LX_{u_j}C)
  (LX_{u_m}).
```

A product without `P` fixes `e₁`. The exterior row is nonzero. If the exterior column
vanishes, `LX_{u₀}C=0` and `u₀` is nonempty. Otherwise the outer product is nonzero and a
zero product over `ℤ` forces an internal scalar bridge to vanish. Empty bridges equal
`LC=μ`. This proves the mortality equivalence even when a reset letter has rank three.

## Accepted Obstructions

### Exact toggle fusion

The data images equal `H=span{e₁,e₃,e₄}`. Thus `SG_x=TG_x` for both data letters forces
`S|_H=T|_H`. On `E=span{e₁,e₃}`, `T` is the identity and every data control is
invertible. Every product retains an invertible restriction to `E`.

### Phase signature

In an exact `4=2+2` shared-channel realization, let `q₀` be the rule phase and `q₁,q₂`
consecutive deletion phases. If `q₁,q₂` are independent, they span the private quotient, so
two data controls agreeing there agree everywhere. If they are dependent, the cyclic
transition preserves their line and carries it back to `q₀`; agreement still propagates to
the rule phase. The Neary controls agree at deletion phases but have unequal rule scales.
This contradiction is kernel-checked in
[`MatrixMortality/PhaseSignature.lean`](../MatrixMortality/PhaseSignature.lean).

### Closed serialization

A finite complete-token serializer induces deletion-one substitution

```text
γw ↦ wτ(γ).
```

Its execution is breadth-first traversal of the finite substitution forest. A reachable
dependency cycle gives an infinite lineage. Without one, the reachable dependency graph is
finite and acyclic, so every tree has bounded depth and finitely many nodes. Emptying is
decidable by graph reachability.

### Exact internal/final codes

Distinct binary words with equal image make the binary morphism noninjective. The two-word
defect theorem then makes both letter images powers of one primitive word. All upper images
commute, contrary to the explicit macro upper words `u_bu_b` and `1u_b`.

## Reported, Not Accepted As Theorems

The odd-phase macro cut depends on a reachable-queue parity invariant not yet stated in Lean.
The deterministic two-state first-return classification is elementary, but its application to
every loop-family placement of the four Neary roles has not been independently reconstructed.
Both remain `reported` in `SALVAGE.md`.

The following bounded or incomplete findings are not promoted:

- failure of projectively rescaled reset-selector identities at `β=3`, body `bb`;
- failure of bounded mixed-word searches for cube-root punctuation;
- the claim that no unary selector can realize every macro role outside its stated exact
  factorization hypotheses.

## Exact Open Boundary

The compiler yields `M₄(3)` from either:

1. an undecidable binary two-state controlled scalar source; or
2. a mixed matrix macro whose incomplete fragments carry a nonlocal residue and whose full
   arbitrary-word grammar is sound.

Finite closed-token serialization cannot provide the first. Exact local phase realization
cannot provide the second. The surviving source state must remain open across nominal token
boundaries, or the matrix construction must preserve only the zero set through cancellation,
incidence, or a state-dependent gauge.

The exact finite closed-token criterion is now kernel-checked as
`closedSubstitutionHalts_iff_noReachableCycle` in
[`MatrixMortality/ClosedSubstitution.lean`](../MatrixMortality/ClosedSubstitution.lean).

## Mechanical Sanity Check

An ephemeral SymPy checker enumerated all four destination patterns and verified the two
pushout identities, determinant, rank-three/rank-four classification, and the displayed
rational cube root `S³=T`. It printed:

```text
pushout identities, ranks, determinant, and explicit cube root verified
```

The checker is a transcription test. The arguments above, not the finite symbolic execution,
support the audited labels.

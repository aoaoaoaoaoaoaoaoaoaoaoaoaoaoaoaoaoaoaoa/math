# Unique-Coset Profinite-Blindness Audit

**Date:** 2026-08-30

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `80e41b7` on `wave3-m34-ucb`

**Salvage record:** `G3-O28`

## Verdict

The residual non-elementary group-cover problem has a promised empty instance which no finite
quotient of its natural finite-index `S`-arithmetic ambient group can separate. This strengthens
the earlier congruence-blind orbit from projective ray agreement to equality of the entire target
matrix, then invokes Serre's exact congruence-subgroup theorem for `SL₂(ℤ[1/19])`.

This is an obstruction, not an undecidability theorem. `UCB₂(S)`, `M₃(4)`, and `GPCP(3)` remain
open.

## Rational Instance

Put

```text
A=[[1,3],[0,1]],       B=[[1,0],[3,1]],
p=[1:1],               q=[7:10],
g₀=[[19,−12],[27,−17]].
```

Direct calculation gives

```text
det(g₀)=1,             g₀[1,1]ᵀ=[7,10]ᵀ.                 (1)
```

The ping-pong chambers from `R32-O22` are

```text
U={∞}∪{t:|t|>1},       L={t:|t|<2/3}.
```

For every nonzero integer `e`, `Aᵉ(L)⊆U` and `Bᵉ(U)⊆L`. Both `p=1` and
`q=7/10` lie outside `U∪L`. Every nonempty reduced word sends `p` into its first
factor's chamber, so

```text
H=⟨A,B⟩≅F₂,           H∩Stab(p)={1},
q∉Hp,                  H∩g₀Stab(p)=∅.                    (2)
```

Lean proves the new nonreachability in `profiniteTargetPoint_not_reachable`, the literal coset
exclusion in `shearRepresentation_ne_profiniteTarget_mul_stabilizer`, and the source-stabilizer
claim in `sourcePoint_stabilizer_trivial`. Thus (2) is a valid cardinality-zero instance of the
uniqueness promise.

## Whole-Matrix Congruence Bridge

Write `U(x)=[[1,x],[0,1]]` and `L(x)=[[1,0],[x,1]]`. In every commutative ring, if
`19r=1`, then

```text
L(27r) U(3) L(6) U(−3r) L(−114) U(−12r)=g₀.             (3)
```

Every shift in (3) is a multiple of three. With `A=U(3)` and `B=L(3)`, the left side is
the literal signed word

```text
w_r=B^(9r) A B² A^(−r) B^(−38) A^(−4r).                 (4)
```

For every positive integer `N` coprime to nineteen, choose an integral representative `r_N` of
`19⁻¹ mod N`. Equations (3)–(4) give

```text
w_(r_N)=g₀ mod N.                                       (5)
```

Lean checks (3), the spelling (4), the modular inverse, and the quantified equality (5) in
`profiniteBridgeMatrix_eq_target`, `profiniteBridgeWord_product`,
`profiniteInverse_relation`, and `exists_profiniteBridgeWord_modular_eq`. Replacing signed
exponents by nonnegative residues also gives a positive `{A,B}` word with the same matrix modulo
`N`.

Unlike `R32-O22`, (5) is not merely equality of projective rays up to a residue-ring unit. It
places the complete matrix `g₀` in the congruence closure of `H` away from nineteen.

## Exact Congruence-Subgroup Upgrade

Let

```text
R=ℤ[1/19],             G=SL₂(R).
```

Serre defines an `S`-congruence subgroup to be one containing a principal kernel

```text
Γ(𝔮)=ker(SL₂(R)→SL₂(R/𝔮)).
```

For `K=ℚ` and `S={∞,19}`, Corollary 3 to Theorem 2 states that every `S`-arithmetic
subgroup is an `S`-congruence subgroup. This is the literal congruence-subgroup property: every
finite-index subgroup contains some `Γ(𝔮)`. It is not the weaker assertion that the congruence
kernel is merely finite or central.

To put the instance in standard Borel coordinates, let

```text
C=[[1,0],[1,1]],        C∞=p.
```

Conjugation gives

```text
C⁻¹AC=[[4,3],[−3,−2]],
C⁻¹BC=[[1,0],[3,1]],
C⁻¹g₀C=[[7,−12],[3,−5]].                                 (6)
```

Write `H'=C⁻¹HC` and `g₀'=C⁻¹g₀C`.

All three matrices lie in the finite-index subgroup

```text
Λ=Γ₀(3;R)={M∈SL₂(R): M₂₁∈3R},                            (7)
```

and the determinant-one upper Borel `B_S¹=Stab(∞)∩G` lies in `Λ`. The subgroup in (7) is the
preimage of the upper Borel under reduction modulo three, hence has finite index in `G`.

Let `φ:Λ→F` be any homomorphism to a finite group and put `L=ker φ`. Then `L` has finite index
in `Λ`, and `[G:L]=[G:Λ][Λ:L]` is finite. Thus `L` is an `S`-arithmetic subgroup of `G`, so
Serre's Corollary 3 supplies a nonzero ideal `𝔮` with the literal containment
`Γ(𝔮)⊆L`. Every nonzero ideal of `R` is `NR` for an integer `N>0` coprime to nineteen, after
deleting the nineteen-unit part of a generator. Hence `Γ(N)⊆ker φ` for such an `N`.
Conjugating (5) gives

```text
C⁻¹w_(r_N)C = C⁻¹g₀C mod N,
```

and therefore

```text
φ(C⁻¹g₀C)∈φ(C⁻¹HC).                                      (8)
```

Thus `C⁻¹g₀C` belongs to the profinite closure of `C⁻¹HC` inside `Λ`.

For the exact projective convention, let `π:SL₂(R)→PGL₂(R)` be the canonical map and put
`B_S=Stab(∞)∩PGL₂(R)`. The Lean-checked projective action gives

```text
π(C⁻¹HC) ∩ π(C⁻¹g₀C)B_S = ∅.                              (9)
```

Put `Λ̄=π(Λ)`. The kernel of `π` on `SL₂(R)` is `{±I}`. If `ψ:Λ̄→F` is a homomorphism to a
finite group, applying (8) to `ψ∘π|Λ` gives `ψ(π(g₀'))∈ψ(π(H'))`. The same conclusion holds for
every finite quotient of the full `PGL₂(R)`, by restriction to `Λ̄`. Thus passage through `PSL₂`
or quotienting by the center creates no residual case. The equality behind (8) is equality of
complete matrices modulo `N`, which is stronger than equality up to `±I`.

Since `π(H')` and `π(g₀')` lie in `Λ̄`, the exact Borel-coset condition (9) only uses
`B_S∩Λ̄`. The finite-quotient conclusion concerns quotients of `Λ`, its projective image, and
the full `PGL₂(R)`. It does not concern a finite quotient of a smaller abstract subgroup which
does not extend to one of these ambient groups.

## Consequence And Scope

Equations (8)–(9) rule out every decision scheme whose negative certificate is eventual
separation in a finite group quotient of the natural `S`-arithmetic ambient group. This includes
all congruence quotients and, by the exact congruence-subgroup property, all noncongruence finite
quotients of `Λ` as well.

The result does not exclude:

- syntax-sensitive automata which do not factor through the ambient group;
- Archimedean ping-pong, height descent, or unbounded local data;
- automatic or relatively hyperbolic algorithms on a certified thin subgroup;
- a global decision algorithm for `UCB₂(S)`;
- an undecidability reduction.

It also does not assert that the whole orbit is locally dense. Only the one displayed target
matrix lies in the ambient profinite closure.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `q∉Hp` and `H∩Stab(p)={1}` | promotion | Lean-checked ping-pong |
| `g₀` equals a shear word modulo every `N` coprime to nineteen | promotion | Lean-checked full-matrix identity |
| `g₀` lies in the ambient profinite closure of `H` | promotion | checked congruences plus Serre's exact theorem |
| Every finite ambient quotient separates a promised UCB no-instance | rejected | explicit counterexample |
| The uniqueness promise supplies a finite-quotient length bound | rejected | the counterexample already has trivial source stabilizer |
| `UCB₂(S)` is decidable or undecidable | open | no global algorithm or source reduction |

## Master Delta

```text
MASTER VERDICT: M₃(4) and GPCP(3) remain open.
REMOVED: every finite ambient-group quotient certificate for the non-elementary unique-coset
         residue, including noncongruence quotients of the natural S-arithmetic ambient group.
SHARPENED: the old all-modulus ray hit is now whole-matrix profinite closure on a valid UCB₂({19})
           no-instance.
REMAINS: exploit syntax, Archimedean/height structure, or an infinite automatic normal form;
         alternatively construct an undecidability compiler.
```

## Artifacts

- [`CongruenceBlindOrbit.lean`](../MatrixMortality/CongruenceBlindOrbit.lean)
- [Serre's congruence-subgroup theorem](../references/serre-1970-congruence-sl2.md)

# Free-Group Discrepancy Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a779558-35c4-83ea-b5ef-6de18ca61148)

Primary source: [Carvalho 2026](../references/carvalho-2026-free-group-pcp.md), arXiv v2 preprint

## Verdict

The report does not produce a positive-monoid compiler and does not prove `M₃(4)`. It decisively
changes the free-cancellation lane's objective. Carvalho's complete closed-path subgroup has rank
`3m+1`, but the subgroup of accepting loops is trivial when the cyclic tag system does not halt
and infinite cyclic when it halts. The large rank carries synchronization; it is not an accepting
witness lower bound.

Three positive letters already generate the binary free group as a monoid. The obstruction is
instead spelling: a positive quotient necessarily has nonempty identity words, while ordinary
GPCP must reject every malformed nonempty spelling in a no-instance. Lean checks the three-letter
surjection and the exact boundary-square collapse. A survivor must inspect the unreduced positive
word or irreversibly destroy inverse continuations; evaluating the group element first is fatal
under the stated completeness hypothesis.

## Closed-Path Group

For a cyclic tag system with appendants `u₀,…,u_(m−1)`, forget the transducer outputs. The numbered
core has `m` vertices, two cyclic edges labelled `0,1` from each state to its successor, and loops
labelled `H,p` at every state. Thus it has `4m` geometric edges and

```text
rank K₀ = 4m−m+1 = 3m+1.
```

The entry `#` edge adds one vertex and one edge, so it does not change rank. With `z=0^m`, a
Schreier basis at numbered state zero is

```text
z,
cᵢ=0^i 1 0^(−i−1),
hᵢ=0^i H 0^(−i),
pᵢ=0^i p 0^(−i)                 (0≤i<m).
```

The final `c_(m−1)` differs from the raw chord generator by the elementary Nielsen move which
multiplies it by `z⁻¹`. Conjugating this basis by `#` gives the closed-path subgroup at the initial
state. This verifies `K_C≅F_(3m+1)`; even `m=1` has rank four.

The transducer output homomorphism on this basis is

```text
ψ(z)=H^m,
ψ(cᵢ)=H^i uᵢ H^(−i),
ψ(hᵢ)=H,
ψ(pᵢ)=H^i p H^(−i).
```

It extends to an endomorphism of the literal ambient input group exactly when all appendants are
equal. Indeed, the images of `H,p,0^m` force `H,p,H` on the three literal generators by unique
roots, and the `cᵢ` equations then force one common value `uᵢH` for the remaining generator. Thus
literal state elimination loses precisely the varying program table.

## Fixed-Subgroup Classification

Carvalho proves that the deterministic first-letter trajectory has no repeated pair in a
nonhalting instance, and that every arbitrary reduced stabilizing loop forces a repeated pair.
The latter proof separates a loop into a positive trajectory prefix followed by the inverse of a
second positive prefix.

If the machine halts, let `τ` be the first trajectory prefix reaching a marker-only discrepancy
`D∈{H,p}⁺`. The word `D` contains exactly one `p`, so its cyclic rotations have minimal period
`|D|`. The marker count excludes all earlier repetitions. Every stabilizing prefix difference
therefore reduces to

```text
τ D^k τ⁻¹,       k∈ℤ.
```

After restoring the entry edge, put `g_C=#τDτ⁻¹#⁻¹`. The complete fixed subgroup is

```text
Fix(T̃_C) = {1}             if C does not halt,
Fix(T̃_C) = ⟨g_C⟩ ≅ ℤ      if C halts.
```

The unique `p` gives exponent sum one, so `D` and `g_C` are not proper powers. Carvalho's
Theorem 4.1 identifies the source free group with the complete closed-path subgroup and carries
its equalizer isomorphically onto this fixed subgroup. Hence the constructed free-group PCP
instances have equalizer rank promised to lie in `{0,1}`. This corollary is not stated in the
preprint, and its external novelty has not been assessed.

A computable finite menu of prospective cyclic generators cannot exist. If a nonzero power of a
supplied loop `q` is fixed, unique roots imply that `q` itself is fixed; checking the finite menu
would decide cyclic-tag halting. The cyclic generator is existentially small but cannot be chosen
uniformly in advance.

## Three Positive Letters

Let positive letters `x,y,z` evaluate in `F(x,y)` as

```text
x ↦ x,
y ↦ y,
z ↦ y⁻¹x⁻¹.
```

Then

```text
x⁻¹=yz,       y⁻¹=zx,       z⁻¹=xy,
xyz=yzx=zxy=1.
```

Lean proves by free-group induction that every element of `F₂` has a positive spelling over these
three letters, and checks all three nonempty identity words. Thus group-theoretic positivity is
not the missing resource.

The report additionally gives the terminating rewrite rules

```text
xyz→ε,       yzx→ε,       zxy→ε.
```

Its six critical overlaps join, giving a confluent regular normal-form language with seven live
proper-suffix states. This finite rewriting calculation is audited but not formalized; the live
problem is not confluence itself, but coupling that spelling state to Carvalho's program-dependent
virtual endomorphism with only three undifferentiated source letters.

## Quotient-Blind Boundary Collapse

Let a positive evaluation `π:S*→G` surject onto a group, let `α,β:G→L` be homomorphisms, and let
fixed boundaries accept by

```text
ℓ α(π(w)) r = ℓ′ β(π(w)) r′.
```

If some group element `g` and `g²` are both accepted, cancellation forces

```text
ℓr=ℓ′r′.
```

Surjectivity of the positive evaluation supplies a positive spelling of the inverse of any
letter, hence a nonempty positive word evaluating to `1`. The boundary equality accepts that
word. Lean proves both statements over arbitrary groups and combines them into an explicit
nonempty identity witness.

Applied to Carvalho, completeness for every accepting fixed loop includes both `g_C` and
`g_C²`. A no-instance must reject every nonempty positive word. Therefore no total compiler with
these properties can decide halting by first quotienting to a group element and then applying
fixed homomorphic boundaries.

The hypotheses are essential. A reduction need only preserve existence and may select one
halting-dependent spelling without representing every fixed loop. A boundary test may depend on
the unreduced positive spelling. A singular matrix action may destroy illegal inverse histories
before group completion. None of these is excluded.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The closed-path subgroup has rank `3m+1` with the displayed basis | promotion | audited graph and Schreier computation |
| The transducer output has the displayed basis formulas | promotion | audited edge multiplication |
| The fixed subgroup is promised trivial or cyclic | promotion | audited sharpening of Carvalho Proposition 3.2, Lemma 3.5, and Theorem 3.6 |
| Carvalho's equalizer has promised rank zero or one | promotion | audited corollary of Theorem 4.1; external novelty unassessed |
| Three positive letters surject onto `F₂` | promotion | Lean theorem `triangleEvaluate_surjective` |
| Accepting `g,g²` through quotient-blind fixed boundaries forces a nonempty identity witness | promotion | Lean theorem `exists_nonempty_identity_witness` |
| Every positive free-cancellation compiler is impossible | rejected | existential-only, spelling-sensitive, and singular one-way compilers remain open |
| `M₃(4)` follows | rejected | no positive three-control verifier or matrix realization is supplied |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: rank-three generation of the complete closed-path subgroup; literal ambient
         state-elimination; a computable finite menu of accepting generators; Nielsen or
         Schreier compression followed by quotient-blind all-loop-complete boundaries.
ADDED: accepting loops are cyclic; three positive letters already realize free cancellation;
       the precise missing object is a spelling-sensitive one-way normal-form verifier.
REMAINS: compile that verifier and the program-dependent virtual endomorphism into three source
         letters, or realize the same mechanism through singular positive matrix dynamics.
DISTANCE: free cancellation solves deletion but not malformed-word rejection. The lane remains
          genuinely independent of the paired and square-root races.
```

## Artifact

[`PositiveFreeCancellation.lean`](../MatrixMortality/PositiveFreeCancellation.lean)

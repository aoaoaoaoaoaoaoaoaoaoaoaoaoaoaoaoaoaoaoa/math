# M₃(2) Shortcut-Collatz Incidence Audit

Date: 2026-08-10

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

Normalized GPI₂ is the exact hard core of the rank-`(2,2)` profile. The attack sought a decision
procedure and instead found a fixed-projectivity arithmetic benchmark: pointwise shortcut-Collatz
reachability reduces exactly to normalized GPI₂. The converse quantifies over every binary word;
it does not assume an intended instruction language.

## Exact Predecessor Language

Write one shortcut-Collatz step on integers as

```text
x → y  iff  (x even and x=2y) or (x odd and 3x+1=2y).
```

Let `ReachesOne` be the least set containing `1` and closed under the two integral inverse
branches. Lean proves that this inductive language is exactly the reflexive-transitive closure
of the displayed forward relation. This rules out a change of problem hidden in the inverse
encoding.

The two rational inverse branches are

```text
A(z)=2z,                  A=[[2, 0],[0, 1]],
B(z)=(2z−1)/3,            B=[[2,−1],[0, 3]].
```

For a word `w` applied projectively to the source `(1,1)ᵀ`, Lean computes

```text
M_w (1,1)ᵀ = s_w (z_w,1)ᵀ,
```

where `z_w` is the rational predecessor state and `s_w` is the product of the homogeneous
branch scales. Against the target row `(1,−n)`, incidence is therefore exactly

```text
(1,−n) M_w (1,1)ᵀ = s_w(z_w−n).
```

Every `s_w` is nonzero.

## Denominator Poison

Lean proves the all-word dichotomy

```text
z_w is an integer in ReachesOne  or  v₃(z_w)<0.
```

An illegal application of `B` to an integer has 3-adic valuation `−1`. At negative valuation,
`A` preserves negativity and `B` strictly lowers the valuation: the integral translation cannot
cancel the lower-valuation term. A malformed word can therefore never return to an integer.
Conversely, induction on `ReachesOne` constructs the corresponding predecessor word. Hence

```text
∃w, (1,−n) M_w (1,1)ᵀ=0  ↔  ReachesOne(n).
```

Combined with the forward-relation theorem, the right side is conventional finite
shortcut-Collatz reachability from `n` to `1`.

## Unit Normalization

For a nonzero integer target `n`, put

```text
λₙ=1/2−n,                 μₙ=−3n,
Hₙ=λₙA,                   Gₙ=(λₙ²/μₙ)B.
```

Both matrices are units. Direct inverse-action calculations give

```text
α=(1,−n) Hₙ⁻¹ (1,1)ᵀ=1,
β=(1,−n) Hₙ⁻¹ Gₙ Hₙ⁻¹ (1,1)ᵀ=1.
```

Each normalized letter is a nonzero scalar multiple of its raw letter, so the product acquires
only a nonzero word-dependent scalar. Lean proves preservation of the complete zero language and
the final reduction

```text
∃w, incidence(Gₙ,Hₙ,(1,−n),(1,1)ᵀ,w)=0  ↔  ReachesOne(n).
```

The report stated the result for `n≥2`. Formalization removes that accidental restriction: the
theorem holds for every nonzero integer target. For positive Collatz inputs, `n=1` is the trivial
base case and every nontrivial input lies in the normalized family.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| normalized relative-generator and zero-corner charts | restatement | scalar normalization and the absence of a hidden projective restriction were already owned by `R32-S35` |
| complete elementary-group decision census | open | not reconstructed from primary sources and does not decide the non-elementary residue |
| fixed-projectivity shortcut-Collatz embedding | promotion | formalized with exact forward/inverse equivalence and every-word converse |
| denominator persistence | promotion | strengthened to a 3-adic invariant over arbitrary rational continuations |
| critical-shell nonregularity | salvage | the broader queue-centralizer obstruction `R32-O19` already kills the finite raw-word controller lane |
| normalized GPI₂ is decidable or undecidable | rejected | neither conclusion follows from the embedding |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: the possibility that normalized GPI₂ has only tame finite-state projective dynamics
EXPOSED: exact fixed-projectivity shortcut-Collatz reachability inside the hard rank-(2,2) core
REMAINS: decide that intrinsic arithmetic dynamics or prove it universal by a stronger reduction
```

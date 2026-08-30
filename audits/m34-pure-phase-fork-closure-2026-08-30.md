# Pure-Phase Fork Closure Audit

**Date:** 2026-08-30
**Author:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `e8326c76259457c4ceb695809981cf483f99cc10`
**Status:** promoted audited reduction to the published one-dimensional GVAS decision theorem,
with a Lean-checked arithmetic core

## Verdict

Complete pure-phase forks are decidable. Let `P` and `Q` be disjoint finite alphabets. Permit any
finite family of forward productions and one return production

```text
αᵢX ⟶ Xβᵢ,    αᵢ∈P⁺, βᵢ∈Q⁺,
cX  ⟶ Xd,      c∈Q⁺,  d∈P⁺.
```

Reachability between arbitrary `P`-only endpoints is decidable. The result therefore covers the
three-production fork with two competing `P→Q` productions and one `Q→P` return. Disjointness and
nonemptiness make every displayed production head-separated.

The proof reduces completed phase cycles to the transitive closure of an effective semilinear
additive relation on `ℕ`. A new closure theorem decides that relation by compiling it to a
one-dimensional grammar vector addition system. Bizière and Czerwiński's published reachability
theorem applies literally to the resulting grammar.

This does not decide every head-separated fork. It excludes the topology only when every complete
return erases the boundary word to one power `dⁿ`. A mixed word or neutral payload that survives
between cycles remains outside the theorem.

## Complete Boundaries

For a trace word `u=i₁⋯iₖ`, write

```text
α(u)=αᵢ₁⋯αᵢₖ,    β(u)=βᵢ₁⋯βᵢₖ.
```

Starting from `dⁿ`, a forward step is the only possible step while the word has a nonempty
`P`-prefix. After a forward trace prefix `v`, the word has the form

```text
P-residual · β(v) ∈ P*Q*.
```

The first return cannot fire before the `P`-residual is empty. In any successful path to another
`P`-only boundary, the first forward block therefore ends after a trace `u` satisfying
`α(u)=dⁿ`, at the word `β(u)∈Q*`. Forward rules are then disabled. After `j` returns the word has
the form

```text
Q-residual · dʲ ∈ Q*P*.
```

It reaches another `P`-only boundary exactly when `β(u)=cᵐ`; the resulting boundary is `dᵐ`.
Consequently, for

```text
R(n,m)  ↔  ∃u, α(u)=dⁿ ∧ β(u)=cᵐ,
```

every nonempty successful path from `dⁿ` to `dᵐ` has a first complete boundary and decomposes
there. Induction gives

```text
dⁿ ⟶* dᵐ  ↔  (n,m)∈R*.
```

The reverse implication concatenates each witnessed forward trace with the prescribed number of
returns. The empty word is isolated except for reflexivity because every consumed word is
nonempty.

## Effective One-Cycle Relation

The trace language

```text
L = α⁻¹(d*) ∩ β⁻¹(c*)
```

is effectively regular: inverse morphic images and intersections preserve regularity. Its Parikh
image is effectively semilinear. Intersecting that image with the length equations

```text
|d|n = Σᵢ |αᵢ| #ᵢ(u),    |c|m = Σᵢ |βᵢ| #ᵢ(u)
```

and projecting produces an effective semilinear description of `R`. If `u` witnesses `(n,m)` and
`v` witnesses `(n′,m′)`, then `uv` witnesses `(n+n′,m+m′)`. Hence `R` is an additive submonoid of
`ℕ²`.

No finite-generation inference is used. A semilinear additive submonoid need not be finitely
generated: `{(0,0)} ∪ {(x,y):x>0}` is one counterexample. Nor need `R*` be semilinear. For
`R={(n,2n):n∈ℕ}`, the orbit of `1` under `R*` is `{2ᵏ:k∈ℕ}`.

## Additive Semilinear Closure

Let `R⊆ℕ²` be any effective semilinear additive relation. Membership in `R*` is decidable.

Existence of a positive-drift pair `y>x` or a negative-drift pair `y<x` is Presburger-decidable.
If every pair is nondecreasing, reject `m<n`; otherwise any path from `n` to `m` remains in the
finite interval `[n,m]`, so finite graph search using decidable `R` membership settles
reachability. The nonincreasing case is symmetric. If neither strict sign exists, only equal
endpoints can be connected.

Suppose both signs occur. Choose

```text
p=(a,b)∈R,  δ₊=b−a>0,
q=(c,e)∈R,  δ₋=c−e>0.
```

Additivity gives

```text
δ₋p + δ₊q = (h,h) ∈ R,
h = δ₋a + δ₊c > 0.
```

Represent every natural number uniquely as `r+hx`, where `0≤r<h`. For residues `r,s`, define

```text
Sᵣₛ = {(x,y):(r+hx,s+hy)∈R}.
```

Each `Sᵣₛ` is effectively semilinear by affine Presburger preimage. The diagonal pair `(h,h)` and
additivity imply

```text
(x,y)∈Sᵣₛ  ⟹  (x+z,y+z)∈Sᵣₛ
```

for every `z∈ℕ`.

## Exact GVAS Macro

Fix one linear component of `Sᵣₛ`,

```text
C = (A₀,B₀) + ⟨(A₁,B₁), …, (Aₖ,Bₖ)⟩.
```

Give it private nonterminals `C₁,…,Cₖ₊₁` and productions

```text
Cⱼ   → [−Aⱼ] Cⱼ [+Bⱼ]  |  Cⱼ₊₁       (1≤j≤k),
Cₖ₊₁ → [−A₀][+B₀].
```

Here `[z]` is the one-dimensional GVAS terminal `z∈ℤ`. Choosing multiplicities `t₁,…,tₖ`
produces the yield

```text
(−A₁)^t₁ … (−Aₖ)^tₖ (−A₀) (+B₀) (+Bₖ)^tₖ … (+B₁)^t₁.
```

All decrements precede all increments. From counter `x`, the yield is executable exactly when
`x≥A`, where `A=A₀+ΣtⱼAⱼ`, and it ends at `x−A+B`. Thus this component realizes its diagonal
saturation

```text
{(A+z,B+z):(A,B)∈C, z∈ℕ}.
```

A macro nonterminal `Mᵣₛ` chooses once among disjoint, component-private nonterminal families.
It cannot change component after that choice. Recursion records each selected period before the
fixed base and unwinds it only in the increment phase; syntactically, no production resumes period
selection after an increment or enters the next residue macro early. In pushdown language, the
period choice decrements `Aⱼ` and pushes a tagged marker; the base decrements `A₀`, adds `B₀`, and
tagged markers then unwind in reverse order, each adding its `Bⱼ`.

Zero coordinates cause no exception. If `Aⱼ=0`, selection only defers `+Bⱼ`; if `Bⱼ=0`, it only
decrements. A `(0,0)` period is deleted. Zero base coordinates are omitted, and a `(0,0)` base
yields `ε`.

Because `Sᵣₛ` itself is diagonally closed, the union of the component macros realizes exactly
`Sᵣₛ`: soundness shifts the chosen component pair by the unused initial counter; completeness
chooses the desired pair itself and leaves no unused counter.

For a fixed target residue `t`, add path nonterminals

```text
Pₜ → ε,
Pᵣ → Mᵣₛ Pₛ    for all r,s<h.
```

Complete yields of `Pᵣ` are exactly finite concatenations of residue-compatible macros ending at
`t`. If `n=r+hx` and `m=t+hy`, then

```text
n R* m  ↔  x Pᵣ-reaches y.
```

This is literally a one-dimensional GVAS: a finite context-free grammar with integer terminals,
one nonnegative counter, and no zero test, reset, or second counter. Theorem 1 of Bizière and
Czerwiński decides its source-to-target reachability. Their grammar permits arbitrary finite
right-hand sides and `ε`; their stated normalization pads short rules with zero terminals without
changing reachability.

## Arbitrary Pure Endpoints

Let `s,t∈P*`. Reflexivity handles `s=t`. Any nonempty successful path must first exhaust `s` by a
forward trace `u`, satisfy `β(u)=cⁿ`, and reach `dⁿ`. There are finitely many such `u` because every
`αᵢ` is nonempty and `α(u)=s`. Every later `P`-only boundary is a power of `d`. Therefore a
nonreflexive path to `t` requires `t=dᵐ`, and the remaining question is `(n,m)∈R*`. Finite
enumeration of the first traces followed by the closure decision settles all `P`-only endpoints.

## Canonical Fork

For

```text
ppX ⟶ Xq,    pX ⟶ Xqq,    qX ⟶ Xp,
```

let `x` and `y` count the first and second forward productions in one complete phase. Then

```text
n=2x+y,    m=x+2y.
```

Conversely, any nonnegative solution gives a lawful phase: the forward rules consume a pure
`p`-prefix in any order, and `m` returns restore `pᵐ`. Solving for the counts gives

```text
x=(2n−m)/3,    y=(2m−n)/3.
```

Hence one-cycle reachability is equivalent to

```text
n/2 ≤ m ≤ 2n    and    m≡2n (mod 3).
```

This relation is symmetric and preserves divisibility by `3`. For descent,

```text
n even:       n ⟶ n/2,
n odd, n>3:   n ⟶ (n+3)/2.
```

Every positive multiple of `3` therefore reaches `3`, and every positive nonmultiple reaches
`1`. Symmetry supplies the reverse paths. The exact closure is

```text
pⁿ ⟶* pᵐ  ↔
  (n=m=0) ∨ (n>0 ∧ m>0 ∧ (3∣n ↔ 3∣m)).
```

## Scope

The decision theorem permits arbitrary finite forward branching and arbitrary multi-letter words
inside each pure phase. It uses the stronger boundary fact that the sole return production makes
every completed boundary a power of one fixed word `d`.

It does not cover:

- a neutral or balanced payload that survives a complete return;
- mixed-phase boundary words not reducible to finitely many residues and one counter;
- empty consumed words;
- outputs split across several recurrent phase channels;
- a quotient that records only charge while hiding an unbounded boundary word.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Complete paths decompose at `P`-only boundaries | audited | direct disjoint-alphabet phase invariant |
| The one-cycle relation is effective semilinear and additive | audited | regular inverse images, effective Parikh image, trace concatenation |
| Opposite drifts force a positive diagonal in every additive relation | formalized | `IsAdditiveRelation.exists_positive_diagonal_of_mixed` |
| Every effective semilinear additive relation has decidable closure reachability | audited | exact residue-to-1-GVAS reduction plus Bizière–Czerwiński Theorem 1 |
| Arbitrary `P`-only endpoint reachability is decidable | audited | finite first phase followed by closure decision |
| The canonical fork arithmetic and descent steps are exact | formalized | `forkSweep_iff_linear`, `forkSweep_bounds_mod`, `forkSweep_three_dvd_iff`, `forkSweep_symm`, `forkSweep_double_to_self`, `forkSweep_odd_descent` |
| The canonical fork has exactly two positive pure-power components | audited | formalized one-step laws plus descent induction |
| `R*` is semilinear or `R` is finitely generated | rejected | explicit counterexamples |
| Every head-separated fork is decidable | open | surviving boundary words lie outside the pure-phase hypothesis |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every complete pure-phase fork with a sole fixed-word return, including the canonical
         pp/p/q fork on all pure endpoints.
REMAINS: a head-separated fork whose completed cycle retains an unbounded mixed word, an
         empty-consume pump, or genuinely split recurrent transport.
```

## Source

- [`biziere-czerwinski-2025-one-dimensional-pvas.md`](../references/biziere-czerwinski-2025-one-dimensional-pvas.md)

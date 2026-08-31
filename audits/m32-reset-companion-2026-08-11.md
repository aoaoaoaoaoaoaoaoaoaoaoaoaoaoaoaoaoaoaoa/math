# M₃(2) Reset-Companion Audit

Date: 2026-08-11

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The split-decision lane needs a computable bound on a reset-started first-hit terminal history.
Endpoint-only charging is already false: a legal periodic orbit can hide unbounded reverse mass
on a transverse eigenline. The report replaces that dead potential with a second lawful orbit
through the same waits, anchored at the terminal/reset boundary where the projective cross is
nonzero.

It does not prove a terminal bound. Its exact gain is to transmute actual reverse content into
companion forward content. The terminal-only amortization formulation originally recorded here
was corrected on 2026-08-30: it is goal-equivalent rather than an intermediate decision theorem.

## Same-Address Companion

Write the primitive endpoint transfer at `q=pᵃ` as

```text
B(q) = [[A−L+Dqˢ, −L(A−L)(q−1)], [1, −L(q−1)]].
```

For an actual reduction

```text
B(qᵢ)vᵢ=qᵢˢhᵢvᵢ₊₁,     hᵢkᵢ=DL(qᵢ−1),
```

the checked complementary-content law gives the reverse transport by `adj(B(qᵢ))`.
Suppose a first-hit execution begins at `vᴿ=(R,1)`, where `R=A+D−L`, and ends at the
primitive terminal pair `(0,ε)`. Pull `vᴿ` backward through the same inverse-address branches.
Every p-adic unit target has one source in the exact sphere for that wait, so the checked
inverse-address grammar and canonical primitive integral lift produce a unique projective
companion

```text
v̂₀ → v̂₁ → ⋯ → v̂ₙ=vᴿ.
```

No new dynamical register is present: the companion is a deterministic pullback of the reset
through the supplied address. For `Wᵢ=[vᵢ,v̂ᵢ]`, taking determinants of the two transfers gives

```text
qᵢˢ ĥᵢ Wᵢ₊₁ = −kᵢ Wᵢ.                         (1)
```

This is also a specialization of the checked exterior-product and cumulative reset-pullback
identities. Formalization therefore does not duplicate their API.

Put `Sᵢ=∑ⱼ₌ᵢ aⱼ` and `δᵢ=Wᵢ/p^(sSᵢ)`. Since `Wₙ=−εR` and every factor in
(1) other than the displayed base power is a p-unit,

```text
δᵢ∈ℤ,   p∤δᵢ,   δₙ=−εR,   ĥᵢδᵢ₊₁=−kᵢδᵢ.
```

Writing `H,K,Ĥ,K̂` for the four content products yields

```text
δ₀ = (−1)^(N+1) ε R Ĥ/K
   = (−1)^(N+1) ε R H/K̂.                       (2)
```

Thus every actual reverse factor outside fixed reset support reappears in companion forward
content. This survives the transverse-reservoir obstruction because a terminal/reset boundary
has cross `±R`; a reset cycle has boundary cross zero.

## One Angular Deficit

Let `M` be the endpoint product and `Mvᴿ=(0,X)`. It has the forced form

```text
M=[[Y,−RY],[c,X−Rc]],     d=Y−Rc,
adj(M)vᴿ=(R(X+d),d).
```

Primitive normalization of this last vector gives

```text
|K̂|=gcd(|RX|,|d|)=gcd(|RH|,|d|),
|δ₀|=|RH|/|K̂|.                                  (3)
```

The second equality uses `p∤d`, obtained from the rank-one reduction of every positive
endpoint transfer modulo `p`. Equation (3) is the reset-sensitive replacement for the rejected
endpoint potential. Prime by prime, (1) gives the exact bilateral ledger

```text
vℓ(δᵢ)−vℓ(δᵢ₊₁)
  =vℓ(hᵢ)+vℓ(ĥᵢ)−vℓ(DL(qᵢ−1)).              (4)
```

A layer assigned to one trajectory is neutral, to both trajectories raises inventory, and to
neither lowers it. Existing moving-prime and recurrent-boundary theorems then show that every
layer outside `pDLR` contributing to the residual `H/K̂` must lose its exact-order support on
both chronological sides. The old diffuse reverse reservoir has become precisely the sparse,
doubly order-broken genealogy already isolated by the counter lane.

## Parametric Failure Of Descent

The tempting inequality `|H|≤|K̂|` is false even for one first-hit return. Lean checks a
stronger parametric family in `ReturnGuard.Examples.resetCompanion_counterfamily`. For `n>0`, put

```text
c=24n+1,  R=24n+2,
Ĥ=(12n+1)(108n+5),  L=2Ĥ,  A=L+1,
(p,s,D)=(3,2,c).
```

Then the two primitive reductions are

```text
(R,1) --h=−cR--> (0,1),
(Ĥ,−2) --ĥ=Ĥ--> (R,1),
```

with complementary contents `k=−(9c+1)` and `k̂=4c`. Lean checks both reductions, both
complementary products, and

```text
[(R,1),(Ĥ,−2)] = −9(12n+1)²,
2cR=(4c)(12n+1),
4c<cR.
```

Hence `|H|/|K̂|=R/4=(12n+1)/2` is unbounded. This kills monotone shadow descent,
coefficient-independent contraction, and contraction at every nonmaximal Smith step. The loss
is supported on the fixed tuple through `2R`, so it does not kill a coefficient-effective
amortized theorem.

## Bilateral Shadow Quantifier Wall

For a first-hit word `w`, define

```text
Θ(w)=|Hₓ|/|K̂ₓ|=|δ₀|/|R|.
```

At depth two let `m(w)` count actual Smith steps with nonmaximal moving reverse coordinate.
Parity and maximal-step isolation give `length(w)≤2m(w)` in the only live even-reset stratum.
The originally proposed proposition was:

```text
∃ computable C≥1 and 0<ρ<1,
∀ reset-started first-hit terminal w,  Θ(w)≤Cρ^m(w).     (BSA)
```

By endpoint-word uniqueness, a fixed guard has at most one positive terminal word. Pointwise BSA
is therefore automatic: take `ρ=1/2`, use any positive `C` in the immortal case, and after the
unique terminal word is known enlarge `C` to dominate its single value. Conversely, a total
coefficient algorithm producing constants strong enough to use `δ₀≠0` bounds `m(w)`, hence the
terminal length, and decides the guard. A decider supplies such constants by first deciding and,
in the mortal case, simulating to the unique terminal word. BSA is thus the same decision-oracle
quantifier wall already recorded in `R32-O11`.

Sparse births, microscopic packet size, logarithmic recovery, and local `3/4` Smith savings still
fail to control nested bilateral packet intervals. They become relevant only if assembled into
an explicit coefficient formula proved on a nonterminal class with independent content.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| same-address reset companion exists uniquely | promotion | audited composition of checked inverse-address and integral-lift theorems |
| exterior recurrence and content transmutation | promotion | exact; subsumed by checked exterior and complementary-content laws |
| endpoint angular-gcd normal form | promotion | audited exact matrix calculation |
| bilateral multiplicity ledger | promotion | exact valuation of the exterior recurrence |
| final-boundary and two-sided order capture | restatement | existing moving-prime and recurrent-boundary calculus |
| monotone companion-shadow descent | rejected | unbounded Lean-checked one-step counterfamily |
| pointwise bilateral shadow amortization | rejected as frontier movement | automatic from endpoint-word uniqueness |
| effective bilateral constants | goal-equivalent | a total coefficient algorithm is already a guard decider |
| computable terminal bound or `M₃(2)` decision | open | requires an explicit non-oracular recurrence estimate or a counterorbit |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: endpoint-only reverse charging; monotone companion descent; per-nonmaximal-step contraction
QUANTIFIER WALL: terminal-only BSA is pointwise vacuous and effectively goal-equivalent
DECISION THROAT: prove an explicit coefficient estimate on a broader nonterminal class
COUNTER DUAL: build a reset-incidence orbit whose doubly broken bilateral packets repay every Smith loss aperiodically
```

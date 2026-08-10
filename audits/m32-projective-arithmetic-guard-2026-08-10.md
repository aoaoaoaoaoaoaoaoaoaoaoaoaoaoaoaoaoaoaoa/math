# M₃(2) Projective Arithmetic Guard Audit

Date: 2026-08-10

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

Normalized GPI₂ is the sole hard rank-(2,2) stratum. The attack sought an undecidability
compiler through an injective Möbius word store with a finite tag or queue controller. The
compiler fails for structural reasons, but the reconstruction exposes a different exact route:
projective incidence can enforce legality of arithmetic branches by an irreversible p-adic
denominator fault.

## Guarded Affine Compiler

Fix a prime `p` and two rational affine branches

```text
Fᵢ(z)=(aᵢz+bᵢ)/p,       aᵢ,bᵢ∈ℤ,  p∤aᵢ,
Aᵢ=[[aᵢ,bᵢ],[0,p]].
```

On the p-integral shell, branch `i` is legal on the unique residue
`sᵢ=−aᵢ⁻¹bᵢ mod p`. Assume `s₀≠s₁`, and let the source `x` and target `t` be p-integral. For
every operational word `w=i₁⋯iₙ`, with matrix product and affine composition in matching order,

```text
A_w (x,1)ᵀ = pⁿ(F_w(x),1)ᵀ,
(1,−t) A_w (x,1)ᵀ = pⁿ(F_w(x)−t).
```

If the first illegal letter is applied to a p-integral state, its numerator is a p-adic unit,
so the new state has valuation `−1`. At every state of negative valuation, `aᵢz` has smaller
valuation than the integral translation `bᵢ`; cancellation is impossible and the next valuation
is `v_p(z)−1`. A malformed word therefore cannot hit a p-integral target. This proves the
all-word converse without freeness, unique matrix products, or an intended-language
restriction.

When `p=2`, the two distinct residues exhaust the residue field. Every integral state has one
legal branch, so projective incidence is exactly point reachability in one deterministic
parity-selected map.

For raw `H₀=A₁`, `G₀=A₀`, row `r₀=(1,−t)`, and column `c=(x,1)ᵀ`, put

```text
u=F₁⁻¹(x),       v=F₁⁻¹(F₀(u)),
α=(u−t)/p,       β=(v−t)/p.
```

These are exactly `r₀H₀⁻¹c` and `r₀H₀⁻¹G₀H₀⁻¹c`. If `u≠t` and `v≠t`, then

```text
H=H₀,       G=(α/β)G₀,       r=α⁻¹r₀
```

has both genericity scalars equal to one and the same zero language. This is the first exact
normalized GPI₂ compiler whose malformed-word converse is supplied by arithmetic legality
rather than a finite controller.

## Queue Centralizer

Let `ρ:Σ*→PGL₂(ℚ)` be a monoid homomorphism. A finite controller may use a chart `S_q` and base
point `x_q` at each state:

```text
E(q,w)=S_q ρ(w)x_q.
```

Assume the orbit `{ρ(v)x_q:v∈Σ*}` contains at least three points. A projectivity implementing
one tail-uniform queue rule

```text
(q,uv) ↦ (q′,vp)
```

for every tail `v` exists exactly when some
`Z∈C_PGL₂(ℚ)(ρ(Σ))` satisfies `Zx_q=ρ(p)x_q′`; necessarily

```text
T=S_q′ Z ρ(u)⁻¹ S_q⁻¹.
```

Indeed, setting `Z=S_q′⁻¹TS_qρ(u)` turns the update equation into

```text
Zρ(v)x_q=ρ(v)ρ(p)x_q′.
```

Comparing this identity at `v` and at `av` shows that `Zρ(a)` and `ρ(a)Z` agree on the whole
orbit. Three-point rigidity makes them equal. The converse is direct substitution.

The report omitted the three-point hypothesis from the theorem statement although it used it
in the proof. The intended injective stores have infinite orbits, so the repaired theorem
retains the claimed application.

## Trivial Centralizer And Finite Controllers

Suppose `w↦ρ(w)x` is injective for a free monoid on at least two letters. If a nonidentity
projectivity `Z` centralized `ρ(Σ)`, the generated group would lie in the centralizer of one
Möbius transformation. Over the algebraic closure that centralizer is abelian, or an
index-two extension of an abelian group in the involutive case. Every finitely generated
subgroup therefore has polynomial growth. Injective positive words supply exponentially many
distinct elements in linear word balls, a contradiction. Hence the common centralizer is
trivial.

For a controller edge with appendant `p`, the queue equation now forces

```text
x_q=ρ(p)x_q′.
```

Around a controller cycle, store injectivity forces the concatenation of all appendants to be
empty, hence every appendant on the cycle is empty. No nonempty-append edge belongs to a cycle;
the total data ever appended is bounded. If every transition deletes a nonempty prefix, every
run has a computable length bound. Such a controller cannot implement a recurrent queue or tag
machine.

This obstruction quantifies over arbitrary projective transition macros and finite controller
charts. It does not merely reject one fixed positive code. It also explains the missing
coordinate in radix serialization: deleting a prefix and appending a suffix updates the code,
its length register, and an affine constant, requiring three homogeneous coordinates.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| scalar normalization preserves every word zero | restatement | already formalized by `R32-S35` |
| p-adic malformed branches can never recover | promotion | exact valuation argument for every word |
| parity-selected affine reachability reduces to normalized GPI₂ | promotion | exact when the two genericity incidences are nonzero |
| queue-rule classification as originally stated | rejected | missing three-point orbit hypothesis |
| repaired queue centralizer theorem | promotion | direct three-point-rigidity proof |
| injective binary projective stores have trivial centralizer | promotion | exponential versus virtually abelian growth |
| finite-controller homomorphic queue store is universal | rejected | every controller cycle has empty appendants |
| projectively unimodular incidence is decidable | restatement | already recorded as `D2-D01`; not used in this audit |
| normalized GPI₂ is decided or proved undecidable | rejected | the intrinsic arithmetic residue remains open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: injective homomorphic Möbius/continued-fraction store plus finite queue or tag controller
EXPOSED: exact all-word p-adic legality and deterministic binary arithmetic inside normalized GPI₂
REMAINS: decide or prove universal an intrinsically nonhomomorphic arithmetic projective dynamics
```

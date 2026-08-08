# M₃(2) Fixed-Support Toric Obstruction Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The rank-`(3,2)` guard remains open at one reset-started angular carry funded by factors of
`pᵃ−1`. This attack asked whether those factors can implement an orthodox finite-control
counter machine: finitely many auxiliary primes carry counters in their exponents, rational
tail charts read those exponents, and waits depend affinely on them.

The report does not decide the guard. Independent reconstruction proves that this stationary
architecture cannot execute a repeatable computation.

## Exact Class

For auxiliary primes `ℓ₁,…,ℓ_d ≠ p`, a control state `q` has

```text
a_q(n)=α_q+u_q·n,
t_q(n)=φ_q(ℓ₁^n¹,…,ℓ_d^nᵈ),
R_a(t)=p^a+p^(sa)/t,
```

where `φ_q` is a nonconstant rational function defined and p-adically invertible on a
cofinal orthant. An edge translates the counter vector by one fixed integer vector and must
agree with the guard transition throughout that orthant.

The exact ready-tail map is

```text
G_{a,b}(t)=p^(sb)/(C+δp^(sa)−p^b+δ(p^a−1)t),
δ=r−C.
```

This class includes the usual fixed-prime FRACTRAN or Minsky representation. It does not
include a single input-specific history whose prime support changes without a finite chart.

## Reconstruction

### Wait Slopes

Introduce independent variables

```text
X_j=ℓ_j^nⱼ,   Y_j=p^nⱼ.
```

The grid `(ℓ_j^n,p^n)` is Zariski dense: after clearing negative exponents, a polynomial
identity restricts to a linear combination of distinct positive exponential sequences, whose
Vandermonde matrix is nonsingular. The product grid follows one coordinate at a time.

The edge equation is therefore an identity in a Laurent polynomial ring over `ℚ(X)`. Its
`Y`-support contains exponents `0,u,su,v,sv`. Separating the cases `u,v≠0`, `u=0`, and
`v=0` shows that a nonconstant source chart forces

```text
u=v=0.
```

Thus no counter exponent can enter either endpoint wait affinely.

### Monomial Charts

With fixed positive waits, every edge has

```text
ψ(X)(K+Hφ(X))=p^(sb),
K=C+δp^(sa)−p^b,   H=δ(p^a−1).
```

Both `K` and `H` are p-units. If the source and target charts are Laurent monomials and either
is nonconstant, the left side contains two distinct nonzero monomials or one nonconstant
monomial; it cannot equal a nonzero constant. Along one affine one-counter ray the defect has
at most six distinct positive exponential bases. Rolle induction gives at most five distinct
zeros unless the defect is identically zero, which the preceding rigidity excludes.

### Rational Cycles

For fixed waits the tail map is represented by

```text
N_{a,b}=[[0,p^(sb)],[δ(p^a−1),C+δp^(sa)−p^b]].
```

Every such matrix reduces modulo `p` to the same rank-one matrix `N₀`, with
`N₀²=C N₀`. A nonempty cycle product `N` therefore has unit trace and determinant
valuation

```text
T=s∑a_i>0.
```

Its projective eigenvalue quotient has p-adic valuation `±T`. A repeatable toric cycle would,
after diagonalizing this projective map, give

```text
f(ℓ₁^c¹X₁,…,ℓ_d^cᵈX_d)=ρf(X),   v_p(ρ)=±T.
```

The multivariate Gauss valuation is unchanged by scaling variables by p-units, forcing
`v_p(ρ)=0`, a contradiction. This includes zero net counter translation.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| canonical ready-tail formula | restatement | follows from the checked guard dynamics |
| affine counter-dependent waits collapse | promotion | reconstructed from Zariski density and Laurent support |
| Laurent-monomial instruction obstruction | promotion | correct for edges whose source and target are Laurent monomials |
| at most five exact samples on one affine monomial ray | promotion | reconstructed by the Chebyshev-system/Rolle argument |
| arbitrary rational repeatable toric cycle is impossible | promotion | reconstructed from the fixed mod-p flag and Gauss valuation |
| no fixed-support guard compiler of any kind exists | rejected as overbroad | the theorem requires separated rational charts and affine waits |
| guard universality or decidability follows | rejected | moving-support, history-specific execution is outside the class |

No new Lean ontology was retained. The checked single-chart rail theorem already owns the
polynomial machinery; duplicating a multivariate rational-function and Gauss-valuation library
would not tighten the surviving enemy beyond this bounded audit.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: finite-control fixed-prime exponent storage with rational separated tails and affine waits; every repeatable rational toric control cycle
REMAINS: a coefficient-effective bound for the actual history-dependent angular continuant, or one exact reset-started aperiodic orbit using continually moving cyclotomic support
DISTANCE: stationary prime registers are unavailable; any counter-orbit must create and remember unbounded support not rationally recoverable from finitely many fixed-prime exponents
```

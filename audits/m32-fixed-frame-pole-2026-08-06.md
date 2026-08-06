# M₃(2) Fixed-Frame Pole Audit

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. The
displayed split-spectrum rank-`(3,2)` guard is only one candidate subfamily. Its remaining enemy
is global amortization of mandatory nonmaximal Smith steps in an even-resultant,
universal-boundary-passing execution with unbounded reduced denominators, or an exact infinite
execution showing how those losses are repaid.

The submitted attack did not decide the guard. It proposed a fixed-frame pole contraction as the
next theorem and supplied exact coordinates for the shear which obstructs the checked local
contraction.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| dual transport determines the full first row of a terminal suffix | correct, culled | a two-coordinate determinant identity; the terminal specialization follows immediately from checked endpoint transport |
| every terminal product has one lower-left shear beyond its forward and reverse diagonal products | restatement | follows from the checked first coefficient and terminal action by solving the other two entries |
| orbit-adapted triangularization expresses the terminal shear as a mixed-radix extension sum | correct, culled | an exact change of basis, but its digits depend on chosen complements and no estimate on the canonical sum was proved |
| every legal prefix pole approaches reset at exact cumulative base-prime depth | correct, audited | modulo the base prime, all positive-wait transfers equal one rank-one matrix; this yields the natural height corridor but no strict saving |
| Smith reconstruction converts decoder loss into a fixed-frame shear of order `q²` | correct, audited | directly reconstructed; it explains why local `3/4` factors do not multiply globally |
| terminal-only fixed-frame contraction with coefficient-dependent existential constants is a sharper arithmetic theorem | rejected | the deterministic guard has at most one first-hit terminal execution, making pointwise existence automatic |
| uniformly computable contraction constants decide the guard | correct conditional | this is already a coefficient-computable terminal bound, and conversely a guard decider computes such constants |
| no hidden coordinate remains | rejected | upper triangularization names the unbounded extension coefficient but does not prove that another invariant cannot be needed to control it |
| the displayed guard or `M₃(2)` is decided | rejected | neither a terminal bound nor an infinite counter-orbit was obtained |

## Exact Algebra

Put `B=A−L`, `R=A+D−L`, `qᵢ=p^aᵢ`, `sᵢ=qᵢ²hᵢ`, and let one primitive endpoint step satisfy

```text
Eᵢxᵢ=sᵢxᵢ₊₁,    det(Eᵢ)=−sᵢkᵢ.
```

For `x=(r,t)ᵀ`, define the annihilator row `λ(x)=(t,−r)`. Direct expansion gives

```text
λ(Mx)M=det(M)λ(x),
λ(xᵢ₊₁)Eᵢ=−kᵢλ(xᵢ).
```

Thus a suffix ending at `(0,1)ᵀ` has first row

```text
(−1)^(N−i)(∏ⱼ₌ᵢ^(N−1)kⱼ)(tᵢ,−rᵢ).
```

At reset `x₀=(R,1)ᵀ`, write `S=∏sᵢ`, `K=∏kᵢ`, and `ε=(−1)^N`. The existing terminal action
then forces

```text
M_N=[[εK,−εRK],[c,S−Rc]]
```

for one integer `c`. Its affine pole is `π_N=R−S/c`. This is a normal form for an already
known `2 × 2` product, not a bound on `c`.

Choosing integral determinant-one completions of the endpoint rays triangularizes each step:

```text
Uᵢ₊₁⁻¹EᵢUᵢ=[[sᵢ,γᵢ],[0,−kᵢ]].
```

Multiplication gives a mixed-radix formula for the global off-diagonal entry; with canonical
terminal completions it reads

```text
−c/S = ∑ᵢ (−1)^i Kᵢγᵢ/Sᵢ₊₁.
```

Intermediate complement changes alter adjacent `γᵢ` by a coboundary. This proves that `c` owns
the total extension, but gives no cancellation, sign, or height control for the sum.

The local obstruction is explicit. For `uv=q−1`, the Smith decoder and reconstruction satisfy

```text
C(q,u,v)=[[v,q²],[1,(q+1)u]],

[[R,−(A−L)v],[1,−v]] C(q,u,v)
  = [[Dv,A−L+Dq²],[0,1]].
```

The entry `A−L+Dq²` has the same natural `q²` scale removed before applying the local Smith
contraction. Inherited height can therefore move into the extension coefficient. The identity
locates the known obstruction; it does not amortize it.

## Prefix Poles

Let `(c_n,d_n)` be the lower row of the prefix product `M_n`. Every positive wait has `q≡0 mod
p`, and

```text
E(q) ≡ [[B,BL],[1,L]] = (B,1)ᵀ(1,L) mod p.
```

Since `(1,L)(B,1)ᵀ=A`, multiplication yields

```text
c_n≡A^(n−1) mod p.
```

The lawful coefficient hypotheses make `A` a base-prime unit, so `c_n` is a `p`-adic unit and
the prefix pole `π_n=−d_n/c_n` is finite. From `M_n(R,1)ᵀ=S_n(r_n,t_n)ᵀ`,

```text
π_n−R=−S_nt_n/c_n,
v_p(π_n−R)=T_n=2∑ᵢ<n aᵢ.
```

Writing the pole in lowest terms therefore gives

```text
p^T_n/(1+|R|) ≤ H(π_n) ≤ C_E^n p^T_n
```

for an explicit coefficient constant `C_E`. The lower exponent is optimal for unrestricted
rational approximants, so Northcott or a bare product-formula argument at this exponent cannot
separate legal poles. A useful bound must extract a strict saving from the recurrence itself.

## Quantifier Failure

For a fixed lawful coefficient tuple, readiness selects at most one next wait. Hence there is at
most one legal first-hit terminal word from reset. Let its data, when it exists, be `(H,T,m)`.
For `ρ=1/2`, choose

```text
C=max(1,H·2^m/p^T).
```

Then `H≤Cp^Tρ^m` by construction. If no terminal word exists, the same statement is vacuous and
`C=1` works. The pointwise existential statement therefore holds without using the endpoint
recurrence at all.

The word “computable” repairs the statement only when it denotes one total algorithm taking
`(p,A,D,L)` to rational `C,ρ`, together with a proof that the returned values work. Such an
algorithm decides the guard: combine

```text
p^T/(1+|R|) ≤ H ≤ Cp^Tρ^m
```

and compute the first integer beyond which `C(1+|R|)ρ^m<1`; maximal isolation then gives
`N≤2m`. Conversely, if the guard is decidable, decide the law, simulate to the terminal word in
the mortal case, and use the displayed construction; output arbitrary constants in the immortal
case. Uniform effective pole contraction and guard decision thus have the same effective
content.

No new Lean declaration survives. The correct identities either follow from the checked
endpoint calculus or merely name the still-unbounded shear; installing them would enlarge the
API without cutting the master obstruction.

## Wound

```text
MASTER VERDICT: still open
REMOVED: terminal-only existential pole contraction as an intermediate theorem; bare height approximation at the natural p-adic exponent
REMAINS: an explicit coefficient-computable global estimate controlling the fixed-frame shear over complete executions, or an exact infinite unbounded-denominator counter-orbit
DISTANCE: derive a total coefficient algorithm or terminal-length function from the recurrence itself; naming its output C and ρ is not a proof
```

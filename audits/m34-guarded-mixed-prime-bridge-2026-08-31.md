# M₃(4) Guarded Mixed-Prime Bridge Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `cdab0c6` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeBridge.lean`](../MatrixMortality/GuardedMixedPrimeBridge.lean)

## Verdict

The direct mixed-prime specialization of `G3-C08` is now exact. Every block code from the three
paired controls to words in the two affine benchmark generators produces an integral
parity-preserving terminal core, but its gate is precisely fixed rational endpoint reachability
for the concatenated code word. Source-indexed exactness is therefore equivalent to a uniform
family of normalized-mantissa endpoint equations. The twelve target-depth classes of `D2-S08`
do not discharge this equation: they concern unrestricted guarded shell schedules, not an
arbitrary macro image, and they retain the exact rational mantissa.

The fixed `bcbc` fork also kills every length-one route. Exact suffix gating forces the three
induced core matrices to be pairwise distinct; for endpoint gates, their affine actions are
pairwise distinct as well. A letterwise code into two raw benchmark letters necessarily
identifies a pair. Genuine macros remain open.

## Homogeneous Benchmark

Use the affine maps and homogeneous integral matrices

```text
D(z)=(2/3)z,       D̂=[2 0],
                       [0 3]

T(z)=(3/5)z+1,     T̂=[3 5].
                       [0 5]
```

For a raw benchmark word `v` and a homogeneous state `(x,y)`, Lean proves

```text
(M_v(x,y))₂ = (∏ bottomScale(v))y,
ratio(M_v(x,y)) = wordAction(v,x/y),
bottomScale(D)=3,
bottomScale(T)=5.
```

The ratio identity assumes `y≠0`; the first identity proves that this premise persists. If `y`
is odd, every lower coordinate in the orbit is odd. Thus this benchmark satisfies the full
orbit-wide parity premise of the guarded lift for every macro code, without an unbounded search.

## Block-Code Endpoint Equation

Let

```text
κ : PairedControl → {D,T}*,
κ*(x₁⋯xₙ)=κ(x₁)⋯κ(xₙ),
A_x=M_(κ(x)).
```

Lean proves `A_w=M_(κ*(w))` in the matrix multiplication order used by the paired coefficient.
For source `a/b` and target `c/d`, set

```text
q=(a,b),       g=(d,−c).
```

If `b,d≠0`, then for every suffix `w`,

```text
gA_wq=0  ⇔  wordAction(κ*(w),a/b)=c/d.
```

If `b` is odd and the deletion width is positive, composition with `G3-C08` gives

```text
(∀u, liftedCoefficient(u)=0 ↔ pairedCoefficient(beta,body,u)=0)
⇔
(∀w, wordAction(κ*(w),a/b)=c/d
      ↔ pairedCoefficient(beta,body,cw)=0).
```

The formal theorem also quantifies over source-indexed functions for `κ,a,b,c,d`. A concrete
computable choice of those functions is therefore a uniform `M₃(4)` compiler exactly when it
satisfies the displayed endpoint family. The theorem does not assert computability merely from
having function parameters.

## D2-S08 Boundary

`D2-S08` writes a real-trap target as

```text
U(depth,μ)=1/5+(3/10)(2/3)^depth μ,       2/3<μ≤1,
```

and reduces guarded nonempty target depth to the twelve representatives `0,1,2,…,11`. Its exact
scope preserves `μ`; it neither identifies distinct mantissas nor decides their reverse orbit.
The endpoint equation above retains the complete rational value `c/d`, hence its normalized
mantissa. Encoding only a depth representative loses data required by the formal gate equality.

There are also two prior scope gaps. `G3-S06` recognizes raw affine endpoint equality and imposes
no intermediate `5`-unit guards. Its accepted raw words form the regular image `κ*`, whereas
`D2-S08` quantifies over unrestricted guarded shell schedules; the target/wait shift can leave a
chosen macro image. Applying the twelve-class theorem to a proposed compiler therefore requires
separate proofs that its macro image realizes guarded-shell semantics and is closed under the
needed shifts. Neither property follows from the homogeneous endpoint construction.

This is a reduction to the joint `M₂(3)` seam, not a proof that the full `M₂(3)` problem reduces
back to `M₃(4)`, and not a decision result. A successful mixed-prime compiler must construct the
exact endpoint language or add an invariant deciding its mantissa address.

## `bcbc` Macro Tax

Write the accepted `bcbc` terminal control as `c w₀`. Three explicit controls `c w_bc`,
`c w_bt`, and `c w_ct` are certified nonterminal. Their suffix products have the following
property for an arbitrary two-state core:

```text
A_b=A_c  ⇒ A_(w₀)q=A_(w_bc)q,
A_b=A_t  ⇒ A_(w₀)q=A_(w_bt)q,
A_c=A_t  ⇒ A_(w₀)q=A_(w_ct)q.
```

An exact gate accepts the left state and rejects each corresponding right state. Therefore

```text
A_b≠A_c,       A_b≠A_t,       A_c≠A_t.
```

This conclusion is independent of integrality, parity, invertibility, the endpoint form, and
the mixed-prime benchmark. Specializing it to a letterwise code into `{D,T}` yields a
three-objects-to-two-objects collision and a contradiction for every column and gate row.

For block-coded endpoint gates, Lean also proves the projective strengthening: the three macro
words induce pairwise distinct affine action functions. The mixed-prime kernel contains distinct
words inducing the same affine map, so merely choosing three syntactically distinct macros is
insufficient.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Benchmark products realize the raw affine word in homogeneous coordinates | promotion | Lean induction and field identity |
| Odd source denominator gives the complete guarded parity invariant | promotion | Lean product formula |
| A benchmark gate is exactly fixed rational endpoint reachability | promotion | Lean all-word equivalence |
| The equivalence holds uniformly for source-indexed function parameters | promotion | Lean quantified iff theorem |
| `D2-S08` reduces the gate to twelve finite states | rejected | different word domain and exact mantissa retained |
| Exact `bcbc` suffix gating permits two equal core generators or two equal endpoint macro actions | rejected | four certified finite witnesses |
| A letterwise mixed-prime code can instantiate `G3-C08` | rejected | pairwise-distinct theorem plus pigeonhole |
| A genuine mixed-prime macro family exists | open | no code or endpoints constructed |
| The mixed-prime specialization settles `M₃(4)` | rejected | endpoint family remains unresolved |

## Formal Validation

The owner module and root import compile warning-free under the repository toolchain. The focused
default namespace linter reports no failures, and Lean LSP reports no diagnostics. The worktree's
whole-environment linter remains blocked by baseline documentation and unused-argument findings
outside this module. Publication-facing declarations are listed in
[`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom sets contain only `propext`,
`Classical.choice`, and `Quot.sound`. No proof aperture, project axiom, unsafe declaration, linter
suppression, or external certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
POSITIVE BRIDGE: every mixed-prime macro code gives automatic parity and exact endpoint semantics.
UNIFORM GATE: exactness is equivalent to a source-family of fixed rational endpoint equations.
D2-S08 CUT: guard and shift closure are absent; even with them, exact mantissa remains.
B C B C TAX: induced control matrices, and endpoint affine actions, must be pairwise distinct.
NO-GO: every letterwise three-control-to-two-letter benchmark code fails.
LIVE ESCAPE: genuine macros with three distinct affine maps and an all-word endpoint converse.
```

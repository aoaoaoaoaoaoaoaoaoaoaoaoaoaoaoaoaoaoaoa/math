# M₃(2) Fixed-Geodesic and Endpoint-Completeness Audit

Date: 2026-08-07

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. This
ratchet concerns the split-spectrum rank-`(3,2)` guard, specifically its reset-started,
even-reset-defect, unbounded-denominator stratum. The preceding frontier treated reset ancestry as
a family of moving pulled-back rays. The submitted attack claimed that the radial direction at
the distinguished prime is fixed, that the endpoint equation admits no malformed witnesses,
and that only an angular carry remains.

Independent reconstruction proves the first two claims and strengthens the fixed-ray statement
to an exact congruence-kernel theorem. It does not decide the guard or `M₃(2)`.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| every positive endpoint terminal word is the lawful reset-to-terminal execution | promotion | formalized as an equivalence with inverse address one |
| the positive endpoint zero language is singleton-or-empty | promotion | formalized by injectivity of the positive inverse-address code |
| every positive endpoint product has one mod-p flag | promotion | formalized as an exact matrix formula; nonzero in the normalized p-unit presentation |
| every endpoint determinant has full p-weight `s∑w` | promotion | formalized when `D` and `L` are p-units |
| every actual reset prefix lies on one fixed Bruhat–Tits ray | strengthened | formalized without tree infrastructure as the exact kernel modulo `p^(s∑w)` |
| positive-depth primitive pullback loses no p-power | correct, derived | follows from the checked pullback law and primitive endpoint bases; no duplicate API retained |
| the alternating upper/lower-Borel factorization isolates one shear | restatement, culled | the algebra is correct, but it is a coordinate expansion with no theorem consuming a new definition |
| a lawful fixed-wait parabolic odometer cannot start at reset | correct, subsumed | fixed-macro pumping already excludes the broader repeated rational macro lane |
| the displayed guard has a first-hit three-return mortal schedule | strengthened | Lean proves `[1,1,1]` is the unique positive terminal word, not merely one replayed execution |
| endpoint completeness or fixed radial ancestry decides the guard | rejected | neither controls the angular carry funded by auxiliary factors of `p^a−1` |
| the attack decides `M₃(2)` | rejected | the guard remains open, followed by two exceptional rank-`(2,2)` compiler positions |

## Complete Endpoint Language

Let `τ` be the terminal residual and `I_w(τ)` the positive inverse address in forward word
order. Lean proves

```text
EndpointTerminalWord(w) ↔ I_w(τ)=1.
```

Every positive inverse branch is a genuine right inverse on its branch sphere. Conversely, an
endpoint zero over `ℤ` casts to a terminal ray over `ℚ`; invertibility of every positive endpoint
factor and injectivity of the terminal gauge force its inverse address to be reset. Hence poles,
incorrect waits, and malformed intermediate states cannot create an endpoint zero.

The positive branch spheres are disjoint. A decoded step cannot leave the terminal residual,
so induction on the first branch proves

```text
EndpointTerminalWord(u) ∧ EndpointTerminalWord(v) → u=v.
```

Combining completeness with the existing inverse-address mortality theorem gives

```text
physical mortality
  ↔ ∃ nonempty positive w, EndpointTerminalWord(w).
```

This equivalence removes the former distinction between terminal endpoint products and lawful
physical witnesses. It supplies no bound on the unique word when one exists.

## Fixed Distinguished-Prime Direction

For a nonempty positive word `w`, direct reduction of every endpoint factor modulo `p` and the
idempotence law for the resulting rank-one flag give

```text
M_w mod p = A^(|w|−1) · [[A−L,(A−L)L],[1,L]].
```

In a normalized integral presentation `A` is a p-unit, so the lower-left entry is a unit and the
image and kernel flags do not depend on the waits. If `D` and `L` are p-units, Lean also proves

```text
vₚ(det M_w)=Ω(w),    Ω(w)=s∑w.
```

Now let a cumulative execution from the reset pair satisfy

```text
M_w P₀ = p^Ω Pᶜ_w,    P₀=(A+D−L,1).
```

Reduction modulo `p^Ω` kills `P₀`. The lower-left entry of `M_w` remains a unit modulo `p^Ω`, so
the second row solves every kernel vector uniquely as a scalar multiple of `P₀`. Lean therefore
proves the stronger exact statement

```text
ker(M_w mod p^Ω) = (ℤ/p^Ωℤ) · P₀.
```

This is the congruence-lattice content of the claimed fixed Bruhat–Tits geodesic. Prefix weight
changes its depth, never its radial direction. The moving quantity in the checked pullback

```text
Δ(P₀,adj(M_w)V)=p^ΩΔ(Pᶜ_w,V)
```

is therefore the angular reference `V`, not reset ancestry at `p`.

For a primitive target reference of positive transverse depth `δ`, an endpoint-adapted
unimodular basis makes the pulled-back coordinates

```text
(unit − b·p^δ, p^(Ω+δ)·unit).
```

The first coordinate is a p-unit, so primitive normalization removes no p-power and the
transverse depth is exactly `Ω+δ`. This independently verified consequence closes a possible
distinguished-prime saving but adds no theorem beyond the stronger kernel and pullback laws.

## Three Returns

For

```text
(p,s,A,D,L)=(3,2,122753,−17,39232),
reset=7671/2452,
```

Lean verifies the endpoint product for `[1,1,1]`, checks the guard parameter laws, invokes
endpoint uniqueness, and obtains

```text
PositiveAddress(w) →
  (EndpointTerminalWord(w) ↔ w=[1,1,1]).
```

The associated rational rank-`(3,2)` pair is mortal. The example is a first-hit witness because
no other positive terminal word exists, and it refutes every universal terminal-length bound of
one or two returns.

## Culling

No Borel-factor, angular-register, Bruhat–Tits lattice, or parabolic-tail definition was added.
The alternating factorization is correct but does not yet constrain the global shear. The
fixed-wait parabolic no-go is strictly weaker for this campaign than the checked arbitrary
fixed-macro pumping theorem. Positive-depth saturation is an immediate exact valuation
consequence of the checked pullback identity in primitive bases. Retaining any of these as a
parallel API would enlarge the formal surface without advancing a consuming master theorem.

The surviving code consists of the complete endpoint equivalence and uniqueness, the fixed
mod-p product formula, the exact determinant weight, the exact reset kernel modulo the full
schedule power, and the unique three-return witness.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GUARD VERDICT: the even-reset-defect reset-started unbounded-denominator guard remains open
REMOVED: malformed endpoint witnesses; moving radial reset ancestry at p; hidden p-adic primitive-normalization savings; every universal two-return terminal bound
REMAINS: one angular, all-place carry driven by the moving auxiliary factors of p^a−1, with unbounded denominator growth
DISTANCE: derive a coefficient-effective auxiliary-place bound on that angular cocycle and hence a finite terminal search, or construct one exact aperiodic reset orbit with unbounded denominators; after guard decision, resolve the two exceptional rank-(2,2) compiler positions
```

## Artifact

The endpoint theorems and exact reset kernel are in
[`ReturnGuardEndpointCompleteness.lean`](../MatrixMortality/ReturnGuardEndpointCompleteness.lean).
The unique witness and mortality theorem are in
[`ReturnGuardExamples.lean`](../MatrixMortality/ReturnGuardExamples.lean).

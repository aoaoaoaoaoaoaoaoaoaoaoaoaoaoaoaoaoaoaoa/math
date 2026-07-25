# Dimension-Two Affine Peeling Audit

**Date:** 2026-07-25
**Target:** the affine residue of `M₂(3)`
**Verdict:** four general results audited; benchmark shell reduction audited
with one scope correction; full `M₂(3)` remains open

This audit independently reconstructs the reusable mathematics from a failed
decision-procedure attack. Stable statements live in `SALVAGE.md`. The affine
results do not touch the non-elementary `PGL₂(ℚ)` residue.

## Affine Normalization and Path Form

After a common rational projective fixed point is sent to infinity, the two
generators are affine. If one multiplier is not one, translate its finite fixed
point to zero. The maps then have the form

```text
F(z)=az,      G(z)=bz+d.
```

If `d=0`, both maps preserve `{0,∞}` and belong to the invariant-pair stratum.
If `d≠0`, scaling the coordinate by `d⁻¹` gives `G(z)=bz+1`. If both
multipliers are one, regular-control reachability is a semilinear translation
problem. Source or target points at infinity are trivial because every affine
map fixes infinity; the remaining analysis concerns finite rational endpoints.

Apply an operational word from left to right and write it uniquely as

```text
w=F^m₀ G F^m₁ G ⋯ G F^mₙ,      mᵢ≥0.
```

Set

```text
M=Σᵢmᵢ,      sⱼ=Σᵢ₌ⱼⁿmᵢ.
```

Induction on the number `n` of translated letters gives

```text
w(x)=a^M b^n x + Σⱼ₌₁ⁿ a^sⱼ b^(n−j),
M≥s₁≥⋯≥sₙ≥0.
```

Conversely,

```text
m₀=M−s₁,      mⱼ=sⱼ−sⱼ₊₁,      mₙ=sₙ
```

recovers the blocks. The exponent pairs are therefore constrained to one
monotone path; they are not independent `S`-unit variables.

## Rational-Base Carry Automaton

Let `a=p/q∈ℚ×`, with `gcd(p,q)=1`, `q>0`, and `|p|≠q`. For a finite
digit set `Δ⊂ℤ`, put

```text
P(X)=ΣₖdₖX^k,      dₖ∈Δ.
```

Since `qX−p` is primitive,

```text
P(p/q)=0  ↔  P(X)=(qX−p)E(X) for some E∈ℤ[X].
```

Writing `E(X)=ΣeₖX^k`, with `e₋₁=e_K=0`, coefficient comparison yields

```text
dₖ=qeₖ₋₁−peₖ.
```

Let `D=max{|d|:d∈Δ}`. If `|p|>|q|`, scan low to high:

```text
eₖ=(qeₖ₋₁−dₖ)/p,      |eₖ|≤D/(|p|−|q|).
```

If `|p|<|q|`, scan high to low:

```text
eₖ₋₁=(dₖ+peₖ)/q,      |eₖ|≤D/(|q|−|p|).
```

The bounded integer carry is the automaton state; divisibility determines
transitions, and both boundary carries are zero. This decides zero evaluation
for arbitrary finite strings. Negative rational bases require no change.

## Fixed Translated-Letter Count

Fix `n`. The endpoint equation is

```text
a^M b^n x + Σⱼ₌₁ⁿ a^sⱼ b^(n−j) − y = 0.
```

After clearing denominators, this is a rational-base digit equation. Its
markers are:

```text
−Cy at exponent 0,
Cb^(n−j) at exponent sⱼ,
Cb^n x at exponent M.
```

Only `n+2` markers occur. Their weak order is fixed, coincident markers add,
and arbitrary zero gaps represent the unbounded `F`-runs. An NFA records which
markers have appeared and emits the resulting finite digit alphabet. Its
intersection with the carry automaton is effective.

For a regular control language, scan exponents upward while feeding the
reversed block sequence

```text
F^mₙ G ⋯ G F^m₀
```

to a DFA for the reversed language. The product remains finite. When `a=1`,
block lengths are semantically irrelevant; when `a=−1`, only their parities
matter. The case `n=0` is ordinary one-generator orbit reachability.

Thus fixed-`G`-count reachability is decidable even though every `F`-run is
unbounded.

## Private-Prime Peeling

Suppose

```text
v_p(a)=0,      β=v_p(b)<0.
```

For a word with `n≥1` translated letters, the endpoint and translation terms
have valuations

```text
v_p(E)=v_p(x)+nβ,
v_p(Tⱼ)=(n−j)β.
```

The first translation term `T₁` is the unique least-valued translation term,
and

```text
v_p(E)−v_p(T₁)=v_p(x)+β.
```

If this difference is negative, `E` is the unique minimum and

```text
n=(v_p(y)−v_p(x))/β.
```

If it is positive, `T₁` is the unique minimum and

```text
n=1+v_p(y)/β.
```

A nonintegral or nonpositive answer is impossible. When `y=0`, the unique
minimum excludes every `n≥1`; `x=0` is handled by omitting `E`. Once `n` is
fixed, the preceding automaton decides the instance. The `n=0` case is
separate.

If `v_p(b)>0`, reverse the word and use `u=−bz`. The inverse generators become

```text
u↦a⁻¹u,      u↦b⁻¹u+1.
```

The negative-valuation theorem then applies outside the target shell
`v_p(y)=0`. Reversal preserves regular control.

## Bounded Valuation Orthants

Let finitely many rational affine maps

```text
fᵢ(z)=aᵢz+bᵢ
```

preserve a common bounded rational interval `I`. Suppose that for every prime
`p`, the weights

```text
h_p(aᵢ)=−v_p(aᵢ)
```

all have one weak sign. Put

```text
H_p=maxᵢ h_p(bᵢ),
B_p=max(0,h_p(x),h_p(y),H_p).
```

If every slope weight is nonpositive, then

```text
h_p(fᵢ(z))≤max(h_p(z),H_p),
```

so `B_p` is an inductive bound. If every slope weight is nonnegative and
`h_p(z)>H_p`, the linear and translation terms have different valuations and

```text
h_p(fᵢ(z))=h_p(z)+h_p(aᵢ)≥h_p(z).
```

Hence a successful path cannot ever exceed `B_p`, since it could not return
to the target weight.

Let `S` contain the finitely many denominator primes of the input. Every
reachable state lies in `ℤ[S⁻¹]`; addition and multiplication introduce no new
denominator primes. Along a successful path, the reduced denominator therefore
divides

```text
D=∏_{p∈S} p^B_p.
```

Only finitely many rationals in the bounded interval `I` have denominator
dividing `D`. Reachability is ordinary graph search on this finite set, or on
its product with a regular-control automaton.

The existence of a common invariant rational interval is itself an effective
rational linear-feasibility question. This theorem is an independently proved
nondeterministic, regular-control extension of the denominator-weight
mechanism in Bournez–Kurganskyy–Potapov, Theorem 9.

## Benchmark Normalization

The benchmark currently displayed in `FRONTIER.md` is

```text
A(z)=(2/3)z+1,      B(z)=(3/5)z+1.
```

The rational conjugacy

```text
h(z)=15−5z
```

turns it into

```text
F(z)=(2/3)z,      G(z)=(3/5)z+1.
```

At `p=5`, the private-prime theorem decides every normalized source `x` with
`v₅(x)≠1`. In the original coordinate this is

```text
v₅(3−x_original)≠0.
```

For a complementary test, use

```text
u=3−(6/5)z.
```

Then `G` becomes `u↦(3/5)u` and `F` becomes
`u↦(2/3)u+1`. Reversed private-prime peeling at `p=2` decides the instance
when

```text
v₂(3−(6/5)y)≠0.
```

In the original coordinate this is `v₂(6y_original−15)≠0`. The only endpoint
shell left by these two tests is therefore

```text
v₅(3−x_original)=0,
v₂(6y_original−15)=0.
```

This is a generic endpoint result for the benchmark, not a solution of the
pair for all endpoints.

## Critical-Shell Dynamics

In normalized coordinates write a critical source as

```text
z=5u,      v₅(u)=0.
```

One block `F^mG` sends it to

```text
1+3u(2/3)^m.
```

The result remains in the shell `v₅(z)=1` exactly when

```text
T_m(u)=(1+3u(2/3)^m)/5
```

is again a `5`-adic unit. Since `2/3≡−1 mod 5`, the first guard digit is

```text
u≡2 mod 5  →  m odd,
u≡3 mod 5  →  m even,
u≡1 or 4   →  no critical continuation.
```

The numerator must additionally be nonzero modulo `25` after division.
Higher transitions inspect successively deeper powers of `5`; the needed
residue of `m` grows with the carry depth.

Once a path leaves `v₅=1`, it cannot return. An exit of valuation zero is sent
by every later `G` to valuation `−1`, after which each `G` lowers the
valuation by one. An exit of valuation at least two is first sent to valuation
zero. Every fixed exit therefore has a decidable suffix by private-prime
peeling.

There is nevertheless a quantifier seam: an arbitrary critical prefix can
produce infinitely many possible exits. The guarded maps `T_m` exactly
describe the maximal shell-preserving prefix, but deciding each exit suffix
separately does not decide their infinite union. A finite carry nucleus, or
another effective representation of reachable critical states and accepting
exits, is still required.

## Literature Boundary

Bournez–Kurganskyy–Potapov supply the `p`-adic denominator-growth mechanism
for deterministic piecewise-affine maps. They do not prove the private-prime
or fixed-count theorems above.

Dong–Shafrir show that unrestricted module `S`-unit equations with three or
more modulus primes lead to open linear-exponential Diophantine systems. No
reduction identifies the benchmark with that general problem. Its monotone
path constraint and one-prime shell must not be discarded.

## Mechanical Check

An ephemeral exact-rational checker verified:

- the monotone path formula against direct affine execution;
- both orientations of the carry recurrence, including negative bases;
- private-prime valuations on bounded words;
- both benchmark conjugacies;
- the first critical-shell parity table.

It printed:

```text
normal form, carry automata, private-prime valuations, conjugacies, and shell parity verified
```

This is a transcription check. The proofs above establish the audited scope.

## Promotion Boundary

The five stable records may be cited as audited but unformalized. No full
affine decidability theorem follows. The next proof target is an effective
representation of the critical-shell reachability relation, including
accepting exits; the non-elementary projective residue remains independent.

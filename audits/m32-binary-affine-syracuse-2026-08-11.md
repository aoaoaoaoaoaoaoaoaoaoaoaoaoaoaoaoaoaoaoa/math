# M₃(2) Binary-Affine Syracuse Audit

Date: 2026-08-11

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The normalized GPI₂ universality lane has an exact all-word compiler for two affine branches
with one legal residue each. At denominator two this is a deterministic parity-selected map.
The requested attack sought a universal integer configuration encoding inside that compiler.

No such encoding was obtained. Instead the report collapses the compiler to a signed generalized
Syracuse family, decides two large slope strata, and gives algebraic reasons why the standard
radix-tag, direct FRACTRAN, and finite affine-chart simulations cannot inhabit the remaining
class. The only live universality mechanism is nonhomomorphic carry propagation.

## Exact Binary Map

Write the two legal branches as

```text
Fᵢ(z)=(aᵢz+bᵢ)/2,       a₀,a₁ odd,
b₀ even,                    a₁+b₁ even.
```

On integers the uniquely legal orbit is exactly

```text
T(2m)=a₀m+c₀,       c₀=b₀/2,
T(2m+1)=a₁m+c₁,    c₁=(a₁+b₁)/2.            (1)
```

Conversely every pair of odd slopes and integer offsets in (1) gives such branches via
`b₀=2c₀` and `b₁=2c₁−a₁`. This is a one-state least-significant-bit transducer, not a
hidden finite controller.

An odd common denominator adds no register. For `z=m/q`, with `q` odd, the numerator follows

```text
m ↦ (aᵢm+bᵢq)/2
```

on its unique parity class. Source and target can therefore be cleared by the same `q`; rational
2-integral reachability is instancewise equivalent to integer reachability. The existing
p-adic poisoning theorem already excludes every illegal word, so this arithmetic orbit is the
complete word language seen by the compiler.

## Decidable Slope Strata

Let `Bᵢ=bᵢq` and `C=max(|B₀|,|B₁|)` after denominator clearing.

If both `|aᵢ|=1`, then

```text
|T(m)|≤(|m|+C)/2.
```

Outside `[−C,C]` absolute value strictly falls, and that interval is forward invariant. Exact
simulation therefore reaches the target, enters the finite interval and repeats, or has already
passed through every possible outside state on its monotone descent.

If both `|aᵢ|≥3`, put `λ=min |aᵢ|`. Then

```text
|T(m)|≥(λ|m|−C)/2.
```

Absolute value strictly rises beyond `C/(λ−2)`. Simulate inside a finite interval containing
the source, target, and that threshold; after the first exit the orbit can never return to the
target.

Thus only the mixed stratum survives:

```text
{|a₀|,|a₁|}={1,λ},       odd λ≥3.                    (2)
```

These are elementary effective decision arguments. They are retained as audited mathematics,
not as a new Lean orbit library: the result only prunes one proposed universality compiler, and
the surviving mixed family is the actual master-facing object.

## Signed Syracuse Normal Form

Exchange parity classes if necessary. If the even unit branch has slope `+1`, translation by
its even offset gives

```text
T₊(y)= y/2                 if y is even,
       (ay+B)/2            if y is odd,                  (3)
```

with odd `a,B`. If its slope is `−1`, the affine change `y=3z−b₀` gives the same odd
branch and even rule `−y/2`. Accelerating through the unit steps sends an odd state to

```text
S₊(y)=(ay+B)/2^v₂(ay+B),
S₋(y)=(−1)^(v₂(ay+B)−1)(ay+B)/2^v₂(ay+B).         (4)
```

Ordinary shortcut Collatz is `a=3,B=1`. The universality question assigned to the affine
compiler has therefore become point reachability for one fixed signed generalized `ax+B`
Syracuse map, with `a,B` part of the effective instance. It has not become a known universal
many-residue Collatz system.

For the positive form, a length-`n` history with odd steps at
`0≤j₁<⋯<jₖ<n` obeys

```text
2ⁿTⁿ(x)=aᵏx+B∑ᵣ₌₁ᵏ a^(k−r)2^jᵣ.                       (5)
```

The exponents in (5) are not freely chosen: they must be the unique parity itinerary of `x`
modulo `2ⁿ`. The prospective memory is therefore carry propagation in one fixed multiply-add
operation, not a free word.

## Scoped Compiler Obstructions

A macro of length `n` has affine multiplier

```text
a₀^N₀ a₁^N₁ / 2ⁿ.                                      (6)
```

Its numerator is odd and depends only on letter counts. This yields three exact obstructions.

1. A least-significant-first radix tag update must delete a bit and append a variable-length
   word, giving a power-of-two multiplier on the residual queue. Equation (6) cannot supply it
   except in a non-appending unit degeneration. Adding a periodic 2-adic background still forces
   coefficient one on the arbitrary residual queue, hence `a=1`.

2. Direct FRACTRAN prime-valuation registers require instruction-dependent division by odd
   program primes. Every odd-prime valuation of the linear numerator in (6) is nonnegative;
   decrements would have to arise from data-dependent additive cancellation, not the register
   multiplier.

3. For finitely many affine phase charts `Eₛ(q)=λₛq+μₛ`, chart ratios telescope around
   every controller cycle. Its machine-coordinate multiplier is again (6), so finite affine
   microcoding cannot hide the missing queue or counter operation.

These statements reject the named direct encodings, not universality of (4). The literature
comparisons in the report are treated only as reported search evidence; no external theorem is
used in the algebraic reduction or in the repository's formal claims.

## Carry Seam

Let `η=−B/a∈ℤ₂`. For odd `n`,

```text
S₊(n)=a(n−η)/2^v₂(n−η).                            (7)
```

Read least-significant bits of `n` against the fixed eventually periodic 2-adic word `η`,
delete their maximal common prefix, then multiply the remaining odd tail by `a`. Coefficients
such as `a=2ᴾ−1` can install a periodic background program; multiplication carries are the only
unbounded data-dependent mechanism left. No invariant family of integer configuration codes,
and no exact halting converse for one, was produced.

## Genericity

The exceptional-source seam is not part of the remaining problem. For each ordering of the two
branches, the two nonzero normalization scalars fail on an explicit set of at most two source
rays. Their intersection is the checked `commonBadSources`. Deterministically follow the unique
arithmetic orbit while it remains in that finite set. Within three visits it hits the target,
repeats, or exits; the first two cases map to fixed generic YES/NO instances, and after exit one
ordering is generic. Existing normalization then makes `α=β=1` without changing the complete
zero language.

The final two-plane pushout is already checked. A future undecidability proof for (4) therefore
composes directly to two rank-two `3×3` matrices; genericity and matrix assembly require no new
state and no new compiler.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| parity-affine compiler equals the integer map (1) | promotion | exact elementary normalization |
| odd rational denominators add a register | rejected | common-denominator numerator conjugacy |
| both-unit and both-expansive slope strata | promotion | effective finite-box decision arguments |
| mixed stratum is signed generalized Syracuse | promotion | exact affine conjugacy and acceleration |
| many-residue Collatz universality settles the binary class | rejected | wrong simulation direction; retained only as literature-search evidence |
| direct radix tag, FRACTRAN, or affine-controller encoding | rejected in the stated forms | multiplier and telescoping obstructions |
| exceptional genericity blocks a many-one reduction | rejected | bounded common-bad-set preprocessing |
| carry-based invariant universal encoding | open | no code family or converse obtained |
| GPI₂ or `M₃(2)` undecidability | open | no undecidable source reaches (4) |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: unit/unit and expansive/expansive affine slopes; odd-denominator memory; orthodox radix, tag, FRACTRAN, and finite affine-chart encodings
EXACT UNIVERSALITY THROAT: carry-driven point reachability for one signed generalized ax+B Syracuse map
NEXT CONSTRUCTIVE MOVE: exhibit an invariant configuration-code family under (7), or abandon the binary-affine compiler
```

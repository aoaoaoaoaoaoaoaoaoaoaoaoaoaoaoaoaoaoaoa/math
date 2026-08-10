# M₄(3) zero-framed reset-scanner decision audit

**Date:** 10 August 2026

**Status:** exact decision reconstructed; `Bₙ` retired; not Lean-formalized

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide the reset-scanner node of the promised overlap-queue trunk

## Verdict

The report survives hostile reconstruction. Let `zr` replace every nonempty zero-run by one
zero. If `U₀` is not all-zero, write it uniquely as `U₀=0ʳ1V` at its first `1` and put
`C=zr(VW0)`. For every positive frame length, without either compiler promise, the scanner
accepts exactly when

```text
U₀∈0*
or
(U₁∈0* and
  if W contains 1 then C=10
  else C∈(101|11)*10).
```

This is a linear-time decision. It removes `Bₙ`; it does not decide the periodic-conjugate
scanner or `M₄(3)`.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`5cb071fa338f46b484f21764d2df4ba4d2bc0227`. Its transient final report has SHA-256 digest
`47cde5645c67fb2974d8a88884d2937992e9cad353f3d11f733a501880fcb713`.

## Exact Return Semantics

At a rule boundary with queue `xQ`, the rule step enters erase state with queue `QUₓ`. Erase
steps delete its initial zero-run. If the whole queue is all-zero, the scanner accepts. Otherwise
the first `1` is consumed and the next rule boundary is the unread suffix followed by
`W0ⁿ⁺¹`.

The initial queue is `0ⁿ`. Hence `U₀∈0*` accepts immediately. Otherwise the first complete return
reaches `VW0ⁿ⁺¹`. No later `0`-rule step can accept because it appends the nonunary `U₀`.
A `1`-rule step accepts exactly from `10*`, and only when `U₁∈0*`.

Every rule boundary ends in zero. Encode its zero-run reduction by

```text
a ↦ 01,     b ↦ 1,     reduced queue = h(token word)0.
```

If `S` encodes `C`, and `Q` encodes `zr(0U₁W0)`, direct FIFO cancellation gives the complete
boundary dynamics

```text
ε ↦ S,
aX ↦ XaS,
bcX ↦ XQ,
b ↦ accept.
```

The displayed suffix `X` has the physical left-to-right order. No reversal or pristine-block
assumption enters.

## Quotient Classification

Assume `U₁∈0*`. If `W` contains `1`, then `Q` begins in `a`. Both nonterminal appendants are
nonempty and begin in `a`; no transition produces singleton `b`. Acceptance therefore occurs
exactly when `S=b`, equivalently `C=10`.

If `W∈0*`, then `Q=ε`. The token monoid partitions into

```text
H=(bΣ)*b,
E=(bΣ)*,
A={words having a in an odd position}.
```

Pair deletion sends `H` to `b` and `E` to `ε`, after which `S` is restored. Class `A` is
invariant: deleting a leading pair preserves odd positions, while `aX↦XaS` preserves either the
inserted `a` or an odd-position `a` from the fixed `S∈A`. Thus only `H` accepts. Under `h`,
`H` becomes `(101|11)*10`.

## Adversarial Checks

The reconstruction explicitly covers:

- empty `U₀,U₁,W` and first `1` at either end of `U₀`;
- a first `1` created inside an appendant rather than inherited from the queue;
- all-zero intermediate queues and the exceptional token words `ε` and `b`;
- arbitrary zero-run lengths and all positive `n`;
- malformed queues, because the token equations hold at every rule boundary;
- exact FIFO orientation.

A separate bounded exact simulator found no counterexample among every resolved instance with
`n≤3`, `|U₀|≤4`, and `|U₁|,|W|≤3`. Growth-cutoff instances were treated as unresolved, not
evidence.

## Promotion Boundary

Promoted:

- the unconditional classification and linear decision;
- the exact two-token quotient;
- retirement of `Bₙ`.

Not promoted:

- scanner-specific Lean infrastructure whose sole consumer would be this retired lane;
- the report's constant-auxiliary-space implementation claim, which is immaterial to the master;
- raw simulator code or transcript.

Open:

- periodic-conjugate scanner `C`;
- the original and retuned parabolic matrix lanes;
- `M₄(3)`.

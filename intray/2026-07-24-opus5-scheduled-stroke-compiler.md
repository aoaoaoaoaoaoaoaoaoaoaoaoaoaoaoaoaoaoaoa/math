# Scheduled Stroke Compiler

**Source:** Claude Opus 5 consultation, 2026-07-24.

**Status:** promoted through the width-three rank theorem. The consultation's main textual
report was overwritten by a late background-job notification; the matrices, decoder, finite
checks, and final certificate report survived. The reconstruction is formalized in
`ScheduledBinary.lean` and `ScheduledBinaryRank.lean`.

## Construction

The terminal-match soundness theorem already forces every zero witness into strokes

```text
R(head), D(wake₀), …, D(wake_{β−2}).
```

After reversal, every stroke has the fixed schedule

```text
D, …, D, R.
```

The proposed binary compiler therefore lets each input bit select only `b` or `c`; its
position modulo `β` selects deletion or rule semantics.

Use coordinates

```text
(a, u, ℓ₀, …, ℓ_{β−1}).
```

For `x∈{b,c}`, let `Uₓ,Aₓ` be the common upper-channel append data,
`Vᴰ=1,Bᴰ=3` the common deletion lower-channel data, and `Vₓᴿ,Bₓᴿ` the rule
lower-channel data. Define `Sₓ` by the nonzero entries

```text
Sₓ[a,a]                 = 1,
Sₓ[u,a]                 = Uₓ,
Sₓ[u,u]                 = Aₓ,
Sₓ[ℓⱼ,a]                = Vᴰ                 for j<β−1,
Sₓ[ℓⱼ,ℓⱼ₊₁]            = Bᴰ                 for j<β−1,
Sₓ[ℓ_{β−1},a]           = Vₓᴿ,
Sₓ[ℓ_{β−1},ℓ₀]         = Bₓᴿ.
```

With `μ=σ(10^β)`, `t=3^(β+1)`,

```text
L = (μ,t,−1,0,…,0),      C = e_a.
```

For a binary word `z=z₀…zₙ₋₁`, assign `zⱼ` the role `D(zⱼ)` when
`j mod β<β−1` and `R(zⱼ)` otherwise, then reverse the resulting role word.
The proposed identity is

```text
L S_z C = sideCoefficient(τβ(z)).
```

The identity is now proved over every commutative ring for every binary word:

```text
scheduledCoefficient_eq_sideCoefficient
```

## Consequence and Seam

The decoder is total. `decodeScheduled_historyCode` proves surjectivity onto every tile
history. If its coefficient is zero, the existing
`tileHistory_of_terminal_match` theorem forces the decoded role word to be a complete tile
history. Hence the input length is divisible by `β`; incomplete clock cycles cannot create
zeros. Conversely, reversing any tile history gives a scheduled binary encoding. These
claims are formalized by

```text
scheduledCoefficient_zero_length_dvd
scheduledBinary_zero_iff_terminal_match
scheduledBinary_zero_iff_tagHaltsFrom
```

At `β=3`, the matrices have dimension five. Undecidability of the restricted source at
fixed deletion width three would therefore imply

```text
Z₅(2), M₅(3), R₆(2).
```

The present Neary compiler instead uses `β=10·period`. The fixed-width audit found no
binary deletion-width-three universality theorem; the adjacent class remains unresolved in
the located literature. Without a new fixed-width source or a zero-set-only compression of
the phase clock, the construction has variable dimension `β+2` and gives no fixed table
point. See
[`scheduled-binary-fixed-width-2026-07-24.md`](../audits/scheduled-binary-fixed-width-2026-07-24.md).

## Rank Claim

At `β=3`, a symbolic `5×5` Hankel minor is nonsingular for every nonempty tag body.
`scheduledWidthThree_exact_state_lower_bound` therefore proves that every exact rational
representation has at least five states, while
`scheduledWidthThree_native_state_card` supplies the matching upper bound. The generic
claim that the rank is `β+2` remains computational; it has not been promoted to a theorem.
Neither statement constrains a different series with the same zero set.

The consultation also reported a candidate exact-rank-six certificate for the existing
six-state paired binary series:

```text
prefixes = suffixes = {ε,0,1,00,01,000}.
```

The corresponding minors were nonzero in five tested instances. This is computational
evidence only. Even a uniform proof would exclude exact five-state realization, not the
five-state same-zero route.

## Promotion Obligations

1. **Complete:** formalize the scheduled decoder and coefficient identity for every binary
   word.
2. **Complete:** prove surjectivity onto tile histories and the malformed-word converse.
3. **Complete at the decisive width:** prove exact rank five for `β=3` and nonempty body.
   The generic `β+2` claim remains unformalized.
4. **Complete:** no fixed-width-three source theorem was located; the seam remains live.
5. **Escalated:** assemble an expert-review package for constant-state delimiter fusion and
   its arbitrary-word converse.

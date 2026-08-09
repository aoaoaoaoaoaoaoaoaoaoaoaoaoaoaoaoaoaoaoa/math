# M₄(3) deletion-scanner audit

**Date:** 8 August 2026

**Status:** scanner trichotomy independently audited; principal Lag kernel and direct morphic
obstruction formalized; universality and decidability both open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** classify the promised overlap queues left by the forced pure-deletion theorem and
contract the source attack to exact kernels

## Verdict

The report survives, with a strict evidence boundary. Around a forced deleting self-loop, the
four controller roles admit an exhaustive transition split. All non-scanning tables are
decidable by a finite orbit, a two-letter dependency graph, or a direct entry test. The
framed-return promise kills one apparent scanner and forces unary zero frames in two others.
The residual source consists of three kernels:

1. a zero-framed binary context-2 Lag scanner;
2. a zero-framed reset scanner;
3. a periodic-conjugate scanner.

This trichotomy has been independently reconstructed but not encoded as one Lean theorem. Its
principal kernel has been encoded at exact strength. Lean proves that the Lag system starts at
`1 0ⁿ`, accepts exactly at the singleton `0`, isolates every reachable singleton, and forbids
`1 0ⁿ⁺¹`. Under those promises its acceptance is exactly mortality of three integer `4 × 4`
matrices.

No kernel is known universal or decidable. The result narrows the source enemy; it does not
settle `M₄(3)`.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`55d633deb47faf334d31debb517dbd8e77c74dec`. Its transient final report has SHA-256 digest
`9b8ededb7e46866f9f35bc7084fa30ceacd38e39b0c840eed152957312086393`.

## Local Word Audit

Writing `A = 0 :: s`, the positive frame cocycle has exactly four forms:

```text
erase → erase:  produce = cancel
rule  → erase:  cancel = A ++ produce
erase → rule:   produce = cancel ++ A
rule  → rule:   A ++ produce = cancel ++ A
```

For the final equation, equal lengths and prefix cancellation give either two empty words or

```text
cancel = u ++ v
produce = v ++ u
A = (u ++ v)^r ++ u
```

for a nonempty period `u ++ v`. This is the only local conjugacy phenomenon.

The charged potential `|Q|` in `rule` and `|Q|+1` in `erase` leaves pure deletion as the only
possible decreasing self-loop. When `|s|=1` and there is no pure deletion, every accepting step
has zero potential change. Before the terminal step only the two singleton rule configurations
can occur, so acceptance is a finite orbit rather than an exceptional universal stratum.

Fixing a deleting role and splitting the remaining three transitions produces the forward
scanners `F0`, `F1` and backward scanners `B0`, `B1`, plus absorbing or unreachable cases.
The last-return argument uses the compulsory suffix `A` and the promise forbidding `(rule,A)`.
It eliminates `F0`; it forces `F1` and `B0` to have `s=0ⁿ`; and it leaves `B1` with the exact
periodic self-loop above. No transition table lies outside this split.

## Checked Lag Kernel

For `n>0` and binary words `U,V,W`, the surviving `Lₙ` table is

```text
                head 0                     head 1
rule     (erase, U)                  (rule,  [])
erase    (erase, V)                  (rule,  W ++ 0ⁿ⁺¹)
```

Prefix the queue by the phase bit, with `erase=0` and `rule=1`. One queue step becomes

```text
q :: x :: Z  ↦  x :: (Z ++ λ(q,x)),
```

so the four context-2 Lag appendants are exactly

```text
λ(00)=V,    λ(01)=W ++ 0ⁿ⁺¹,    λ(10)=U,    λ(11)=[].
```

`OverlapLag.ofQueueTrace` and `OverlapLag.toQueueTrace` prove both directions for the exact
chronological trace, not merely reachable intended computations. The two source promises become
singleton isolation and avoidance of `1 0ⁿ⁺¹`. `OverlapLag.cocycle` supplies the frame law, and
`OverlapLag.mortality_iff_accepts` composes the result with the arbitrary-word queue compiler.

## Direct-Coding Obstruction

If a source initial word is `J ++ [b]`, no monoid morphism `h` can simultaneously set

```text
h(b) = 0 :: spell h (J ++ [b]).
```

Taking lengths would give

```text
|h(b)| = 1 + |spell h J| + |h(b)|.
```

Lean proves the stronger alphabet-generic statement as
`OverlapLag.terminal_image_ne_frame`. A successful reduction into any residual scanner must
therefore use overlap or history, not identify Neary's common terminal with the return frame by
a fixed letter morphism.

## Promotion Boundary

Formalized:

- the exact binary context-2 Lag transition;
- both directions of trace translation;
- exact translation of singleton isolation and the longer framed-return prohibition;
- the Lag-to-three-matrix mortality equivalence;
- the generic direct-morphism impossibility.

Audited but not Lean-formalized:

- the exhaustive deletion-scanner trichotomy;
- decidability of every non-scanning transition table;
- elimination of `F0` and reduction to `Lₙ`, `Bₙ`, and the conjugate scanner.

Open:

- universality or decidability of any of the three kernels;
- an overlapping or history-based Neary simulation;
- `M₄(3)`.

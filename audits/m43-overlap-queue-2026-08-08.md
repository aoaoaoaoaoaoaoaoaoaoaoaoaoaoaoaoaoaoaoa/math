# M₄(3) positive overlap-queue audit

**Date:** 8 August 2026

**Status:** exact source-to-matrix compiler formalized; the required undecidable source remains
open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** reconstruct the proposed positive cancellation source, prove its arbitrary-word
converse, and decide whether it changes the `M₄(3)` frontier

## Verdict

The compiler survives. A promised binary two-state overlap queue now compiles exactly to three
integer `4 × 4` matrices. The proof uses no inverse alphabet, block-language promise, preferred
cyclic cut, or nominally well-formed matrix word. Its causality lemma handles every positive
physical word.

The source does not yet exist. A stronger formalizer theorem exposes the obstruction behind the
reported parity-frame collapse: every accepted initial queue of length greater than one must use
a state-preserving role whose production and cancellation outputs are both empty. Any universal
construction must therefore implement genuine open-front deletion with one of only four
state-letter roles.

The net result is a strict ratchet, not `M₄(3)`: the open-tail idea has become one exact source
problem with one forced local mechanism.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`4d2254811976b81b4390fc7e40c9c3e43dcaf6dd`. Its transient report has SHA-256 digest
`6cdc7e59940bfb14914d40aac1ef9b572bd68727c3e3693b8195d6af4e183599`.

## Checked Model

For controller state `q`, head letter `x`, and residual queue `R`, one step is

```text
(q, x :: R) ↦ (δ(q,x), R ++ produce(q,x)).
```

For a nonempty initial queue `s`, the frames are

```text
frame(rule)=false :: s,       frame(erase)=[],
```

and the local cocycle is

```text
frame(q) ++ produce(q,x) = cancel(q,x) ++ frame(δ(q,x)).
```

Acceptance means that some exact chronological head word drives `(rule,s)` to `(erase,[])`.
The two promised isolation conditions say that every reachable empty queue is accepting and
that `(rule,s)` never reaches `(rule,false :: s)`.

Lean checks:

- exact queue history along every trace;
- telescoping of the four local cocycle equations along every controller word;
- positive causality for an arbitrary nominal head word;
- reversal from forward queue cancellation to the suffix-controlled scalar coefficient;
- exact mortality equivalence for the fixed family of two data matrices and one separator.

The core theorem is `OverlapQueue.mortality_iff_accepts`.

## Arbitrary-Word Audit

Suppose an arbitrary word `u` satisfies the positive history equality

```text
s ++ emitted(produce,u) = u ++ R.
```

At each position, either the genuine residual queue is already empty or its first symbol is
forced to equal the next symbol of `u`, because both are prefixes of the same positive word.
Thus a genuine prefix already empties the queue, or all of `u` is a genuine trace ending in
`R`. This is the missing converse that closed-block source sketches routinely elide.

The cocycle then leaves only two terminal frames. The two semantic promises turn either case
into a genuine acceptance and exclude the single framed-return false positive. Conversely, an
accepting trace gives a nonempty coefficient-zero word. The existing fixed-anchor compiler owns
all remaining arbitrary matrix words.

## Pure-Deletion Obstruction

Define the charged potential by

```text
Φ(rule,R)=|R|,       Φ(erase,R)=|R|+1.
```

If every state-preserving role has nonempty production, the cocycle and a case split on the two
states show that `Φ` cannot decrease at a queue step. An accepted queue of initial length greater
than one would require `Φ` to fall from more than one to one. Therefore some state-preserving
role has empty production. Comparing lengths in its cocycle forces its cancellation output to
be empty as well. Lean checks this as `OverlapQueue.pure_deletion_of_accepts_large`.

The external report also analyzed a natural parity-framed specialization and found that its
accepting computations collapse to one step. That construction has no durable role after the
general necessity theorem and was culled rather than encoded.

## Promotion Boundary

Formalized:

- the queue semantics, cocycle, and semantic promises;
- the exact three-matrix mortality compiler;
- arbitrary-word soundness;
- the forced pure-deletion self-loop for long accepting inputs.

Not proved:

- undecidability of the promised overlap-queue model;
- a universal family satisfying the two semantic promises;
- decidability of all binary two-state machines with the forced deleting self-loop;
- `M₄(3)`.

The live acceptance test is binary: construct the promised undecidable source and instantiate
the compiler, or classify the remaining four-role normal form effectively.

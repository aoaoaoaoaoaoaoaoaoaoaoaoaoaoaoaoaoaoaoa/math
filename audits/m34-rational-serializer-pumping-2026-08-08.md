# Rational Serializer Pumping Audit

**Date:** 2026-08-08  
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `3b688a1d18eb3aa3335cf5390e003dd2e5711045` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a77e24a-6a8c-83ea-9995-b3d27666910e

## Verdict

Finite-control exact serialization is closed, even when spelling is state-dependent,
nondeterministic, nonfactorial, and carries unbounded target lag. An asynchronous finite
transducer encoding arbitrarily large powers of four explicit Neary blocks pumps to a stationary
physical return. Three `b`-head test blocks force all three physical letters to have lower images
in `b*`; a fourth `c`-head block requires a lower image containing `c`.

This strictly strengthens the former stationary common-residual obstruction. It does not kill a
solution-sensitive final-equality recoding or a nonrational spelling relation with unbounded
memory. Those cases merge into the global word-residual leaf.

## Checked Block Semantics

Lean proves the block equation directly on every exact stroke history:

```text
upper(tileHistory H) · marker = lower(tileHistory H)
↔ consumed(H) · b = c · produced(H).
```

The theorem is bidirectional and includes arbitrary null-history extensions; it assumes neither
terminal-word uniqueness nor first-short-queue execution. This is the report's equation
`σ(W)b=cτ(W)` in the repository's canonical stroke vocabulary.

Lean also proves the final arithmetic throat used after the three-pulse case split: for
`β≥2`, `k>0`, and a natural per-letter lower contribution `e`, the equation
`eβk=k` is impossible.

## Audited Pumping Theorem

Fix even `β≥4` and a body `q` containing `c`. Consider any alphabet `Γ` with at most three
letters, morphisms `g,h`, finitely many endpoint modes, and asynchronous rational relations from
semantic block words to positive physical words. Fixed left and right context is allowed on both
target sides, as are erasure, nondeterminism, wrong-entry modes, and physical letters crossing
block boundaries.

Assume arbitrarily large powers are encodable for the four blocks with consumed words

```text
b^β,       bc^(β−1),       (bc)^(β/2),       cb^(β−1),
```

whose produced words are respectively `b,b,b,qb`. Pumping one accepting transducer path exposes
a loop consuming `B^k` and emitting `y`. Exact transport for every pump count forces `g(y)` and
`h(y)` to be powers of cyclic rotations of the corresponding semantic words. This conclusion
uses a central-factor argument in the bi-infinite periodic word and does not assume a code
boundary.

For the first three blocks, every letter in the pumped cycles has lower image in `b*`. A complete
factor audit shows that at least three such physical letters are necessary:

- the pure-`b` pulse supplies a nonempty pure-`b` upper tile;
- the long-`c` pulse supplies a second tile containing `c`;
- if either tile contains a doubled letter, the alternating pulse rejects it;
- the sole remaining tiles are `b` and `c`, where the checked equation `eβk=k` is impossible.

With `|Γ|≤3`, all physical letters therefore have lower image in `b*`. Pumping the fourth block
requires a cyclic power of `qb`, which contains `c`, a contradiction.

The full finite-transducer pumping and word-factor case audit are independently checked paper
mathematics. They are not presented as Lean declarations; the block equivalence and arithmetic
throat are kernel-checked seams.

## Bounded Residues

For an arbitrary GPCP instance, suppose a computable bound `K` is supplied for the prefix
discrepancy of every accepting word. Free-prefix reduction then has finitely many live states
`0,+s,−s` with `|s|≤K`, plus dead and overflow states. Final boundaries give an exact finite
acceptance test, and a bit enforces the nonempty-word convention. Product with any finite decoder
or regular side condition remains finite.

Thus a computable ternary reduction from the universal Neary family cannot provide a computable
bound on every accepting prefix residual. This decidability theorem is audited rather than
formalized as an extracted decision procedure.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Exact terminal matching is the block equation `consumed·b=c·produced` | promotion | Lean equivalence |
| A positive morphism cannot satisfy the final fractional contribution equation | promotion | Lean arithmetic theorem |
| Finite-control rational exact serialization over three letters is impossible | promotion | independently audited pumping and factor proof |
| Unbounded target lag evades finite-control pumping | rejected | lag is unrestricted in the theorem |
| A computable accepting-prefix residual bound permits decision | promotion | independently audited finite graph construction |
| Every state-dependent or open-residue recoding is impossible | rejected | nonrational and final-equality-only recodings survive |
| `GPCP(3)` or `M₃(4)` follows | rejected | the solution-sensitive global leaf remains open |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: total rational exact serialization, including state-dependent spelling, nonfactorial
         overlap, arbitrary fixed contexts, erasure, and unbounded side lag; every computably
         bounded accepting-prefix residual.
MERGED: the former stateful/open-residue leaf into global solvability-only recoding.
REMAINS: a solution-sensitive or nonrational three-letter construction whose successful paths
         carry an unbounded, non-effectively bounded word residual and preserve final equality
         without exact side transport.
```

## Artifact

- [`TernaryClosedBlockNoGo.lean`](../MatrixMortality/TernaryClosedBlockNoGo.lean)

# Width-Three Adjacent-Cycle Audit

## Statement

Let

```text
q = b^p c c b^s,    p+s=2k.
```

For every `k>0`, the width-three restricted tag system with productions `b↦b` and `c↦qb`
has the periodic queues

```text
L_k = b^(3k-1) c c b^(s+1),
U_k = b^(3k)   c c b^(s+1).
```

Each returns to itself after exactly `k+1` tag steps and therefore never halts. The upper cycle
exists also at `k=0`, although that degenerate body is irrelevant to the required length
envelope.

## Exact Traversals

For `L_k`, the first `k-1` steps delete three leading `b` letters and append one `b`, reaching
`b² c c b^(s+k)`. One `b` step deletes the first `c`, giving `c b^(s+k+1)`. The final `c`
step deletes two `b` letters and appends `b^p c c b^(s+1)`. Since `p+s=2k`, the result is
`L_k`.

For `U_k`, the first `k` leading-`b` steps reach `cc b^(s+k+1)`. One `c` step consumes the
adjacent pair and its following `b`, then appends the body. The same equation `p+s=2k` returns
`U_k`.

Lean records the traversals with exact `Relation.ReachesIn` step counts. Nontermination follows
from the repository's general theorem that a perpetually progressing invariant excludes finite
tag halting; the singleton invariant is closed by each positive self-return.

## Source Consequence

The one-`c` defect descent does not extend by merely allowing a second `c`. At one `c`, every
surviving firing divides a nonzero integral defect by three. Adjacent pairs instead admit two
balanced reproduction cycles at every nontrivial even body length. Thus the one-`c`
shrinking-defect mechanism is sharp for unrestricted queue dynamics.

These cycles do not decide the production-coupled initial queue and do not prove that the
two-`c` stratum is universal. In particular, this does not close the coupled two-`c` source
boundary left open by `MM-D01`. The next question is whether the coupled initial queue for every
adjacent body either halts or enters one of these two cycles. That finite normal form remains
unproved at this ratchet.

## Verification

The declarations are in
[`WidthThreeAdjacentBody.lean`](../MatrixMortality/WidthThreeAdjacentBody.lean):

- `lowerCycleQueue_reachesIn`;
- `upperCycleQueue_reachesIn`;
- `lowerCycleQueue_not_halts`;
- `upperCycleQueue_not_halts`.

No external theorem or computational result enters the proofs.

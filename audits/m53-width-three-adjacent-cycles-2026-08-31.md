# Width-Three Adjacent-Body Audit

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

For the production-coupled initial queue `q.drop 2 · b`, every `k>0` orbit either halts or
reaches `L_k`. Its halting predicate is therefore constructively decidable. The degenerate
body `q=cc` drops directly to the halting queue `b`.

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

## Coupled Normal Form

After the coupled prefix is discharged, every live two-`c` queue has the canonical form

```text
D(i) = b^i c c b^(s+1).
```

Deleting triples of leading `b` letters only transfers one `b` to the right. A macro traversal
therefore has three cases:

```text
i ≡ 0 mod 3:  D(i) →* D(p+s+floor(i/3)),
i ≡ 1 mod 3:  D(i) →* a unary b-queue,
i ≡ 2 mod 3:  D(i) →* D(p+s+floor(i/3)).
```

Under `p+s=2k`, the live macro map is `i↦2k+floor(i/3)`. Every coupled start normalizes with
`i≤2k-1`. If `i<3k-1` and its residue is zero or two, the new index is strictly larger than
`i` and at most `3k-1`. Well-founded recursion on `3k-1-i` consequently returns either a
halting derivation or an exact path to `L_k`. The classifier lives in `Type`, so its two proof
branches yield an executable `Decidable` instance rather than a classical excluded-middle
statement.

## Source Consequence

The one-`c` defect descent does not extend by merely allowing a second `c`. At one `c`, every
surviving firing divides a nonzero integral defect by three. Adjacent pairs instead admit two
balanced reproduction cycles at every nontrivial even body length. Thus the one-`c`
shrinking-defect mechanism is sharp for unrestricted queue dynamics.

The coupled classification closes the adjacent-two-`c` subfamily left open by `MM-D01`. It does
not decide bodies with two separated `c` letters or with at least three `c` letters, and it does
not prove universality of either remaining stratum. The upper cycle belongs to unrestricted
queue dynamics; the coupled normal form requires only the lower cycle.

## Verification

The declarations are in
[`WidthThreeAdjacentBody.lean`](../MatrixMortality/WidthThreeAdjacentBody.lean):

- `lowerCycleQueue_reachesIn`;
- `upperCycleQueue_reachesIn`;
- `lowerCycleQueue_not_halts`;
- `upperCycleQueue_not_halts`;
- `adjacentBody_coupled_normal_form`;
- `adjacentBodyCoupledHaltsDecidable`.

The proofs use only exact list decompositions, Presburger arithmetic, well-founded recursion,
and the repository's verified tag-execution semantics. No external theorem or computational
result enters them.

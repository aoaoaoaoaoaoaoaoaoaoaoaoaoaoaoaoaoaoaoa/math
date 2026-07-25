# Scheduled Binary Fixed-Width Audit

Search cutoff: 2026-07-24.

## Question

The scheduled binary compiler has dimension `β+2`. At deletion width three it
would have five states and would give

```text
Z₅(2), M₅(3), R₆(2)
```

if halting were undecidable for the restricted source

```text
alphabet {b,c},
b ↦ b,
c ↦ body · b,
prescribed suffix input.
```

The audit asks whether the required theorem is already known with `β=3`.

## Verdict

No such theorem was located. The present source theorem does not fix `β`:
Neary's Lemma 9 constructs `β=10p`, where `p` is the simulated cyclic-tag
program period. The formal compiler mirrors this dependence as

```text
deletionWidth period = 10 * period.
```

Classical fixed-width universality does not repair the seam. Cocke and Minsky
fix deletion width at two, but their alphabet contains a family of symbols for
each simulated Turing-machine state. It is not binary.

The nearest binary class boundary remains unresolved in the located literature.
De Mol proves decidability at binary deletion width two and identifies binary
deletion width three as an adjacent open class. Her later study treats Post's
specific width-three system as unresolved. Kurilenko subsequently proves
unbounded growth for that system, but neither universality nor a halting or
reachability decision theorem.

Accordingly, the scheduled compiler is a fixed-width conditional reduction,
not a new fixed cell of the mortality table.

## Search

The search covered exact phrases and notation variants for binary tag systems,
3-tag systems, `TS(2,3)`, fixed deletion number three, `b→b`, `c→u`, and
restricted prescribed-input halting. It inspected Neary's published proof and
Table 2, the primary binary-width boundary papers, later work on Post's system,
and forward citations indexed by OpenAlex. No 2022–2026 paper resolving the
class or the narrower Neary family was found.

Notation is unstable: some sources write `TS(μ,v)`, others `TS(v,μ)`. This
audit therefore does not use `TS(2,3)` without expansion.

## Sources

- [Neary 2015](../references/neary-2015-five-pair-pcp.md): binary universality
  with `β=10p`.
- [Cocke and Minsky 1963/1964](../references/cocke-minsky-1963-tag-universality-memo.md):
  deletion-width-two universality with a growing alphabet.
- [De Mol 2010](../references/de-mol-2010-binary-two-tag-decidability.md):
  binary deletion-width-two decidability and the adjacent boundary.
- [De Mol 2011](../references/de-mol-2011-simple-tag-systems.md): status and
  experiments for simple binary width-three systems.
- [Kurilenko 2022](../references/kurilenko-2022-post-tag-growth.md): unbounded
  growth in Post's fixed system without a universality theorem.

## Consequence

The live route is no longer source substitution by citation. It requires
either:

1. a new fixed-width-three universality construction;
2. a zero-set-only compression of the variable clock; or
3. a constant-state delimiter or punctuation mechanism whose malformed
   placements are rejected by the terminal-match normal form.

The third route is the bounded expert-review target.

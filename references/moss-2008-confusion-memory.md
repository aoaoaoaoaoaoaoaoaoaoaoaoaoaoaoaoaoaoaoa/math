# Moss (2008): Confusion of Memory

**Citation.** Lawrence S. Moss, “Confusion of Memory,” *Information Processing Letters*
107(3–4), pp. 114–119, 2008.

- Work identity: https://doi.org/10.1016/j.ipl.2008.02.002
- Canonical source: https://logic.indiana.edu/_archive/web/moss/queue.pdf
- Local artifact: `moss-2008-confusion-memory.pdf`
- Version and status: author-posted manuscript dated 9 December 2010; the journal article was
  published in 2008
- Retrieved: 2026-08-04
- SHA-256: `48b9132ece7d4aff061c97818cc82c03797c8ad74bc49d405a5fbd690d98fd60`
- Access and retention: publicly distributed from the author’s Indiana University publication
  archive; no separate license statement was located in the artifact
- Synopsis basis: full-text inspection of the nine-page author manuscript

## Synopsis

Moss studies deterministic machines with one unbounded FIFO queue over the binary alphabet
`{1, #}` and no delimiter separating input from workspace. The paper presents the finite
control as a program whose instructions enqueue either symbol, jump forward or backward, or
inspect and dequeue the front symbol with separate empty, `1`, and `#` branches.

Theorem 1 states that halting from the empty queue is Σ₁-complete. Its proof sketch first
simulates a unary Turing machine by a six-register machine, then represents the several binary
registers in one queue using paired symbol codes, a third pair as a block separator, and
circular copying. The construction establishes universality with a binary queue alphabet, but
does not bound the number of program locations and does not require every instruction to
dequeue a symbol.

Proposition 2 proves that this model cannot compute the unary length map on arbitrary input.
The same argument excludes reversal, duplication, and prefixing the unary length. Proposition
3 constructs a self-replicating program from the empty queue while excluding stronger uniform
self-replication maps. Later results place languages recognized by queue programs outside the
control hierarchy.

## Source Assessment

The retained manuscript postdates the journal publication and has minor typographical defects,
including a malformed sentence in the proof of Theorem 1. The universality proof is explicitly
a sketch and attributes its underlying tag-system idea to Minsky. No contradiction with the
stated theorem was found, but the source does not give the transition-level construction needed
to audit a small finite-control bound.

## Project Use

The source confirms that a binary FIFO alphabet alone is compatible with universal halting.
It does not supply the two-state one-tag source required by the `M₄(3)` pushout compiler:
program control is unbounded, enqueue and dequeue are separate instruction forms, and the
empty-queue branch has no direct counterpart in a total transition `Q × Γ → Q × Γ*`.

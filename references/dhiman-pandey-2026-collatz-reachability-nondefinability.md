# Dhiman and Pandey (2026): Non-Definability of Reachability in Büchi Arithmetic

**Citation.** Madhav Dhiman and Rohan Pandey, “Non-Definability of Reachability in
Büchi Arithmetic for a Family of Generalized Collatz Maps,” arXiv:2602.06066v2,
26 June 2026, 11 pages.

- Work identity: arXiv:2602.06066; DOI: 10.48550/arXiv.2602.06066
- Canonical source: https://arxiv.org/abs/2602.06066
- Local artifact: `dhiman-pandey-2026-collatz-reachability-nondefinability.pdf`
- Version and status: arXiv v2 preprint, not peer reviewed
- Retrieved: 2026-08-30
- SHA-256: `e33e8ceb20dc9dba425dcb17b9513c486bec2ed90823531bb54575312de920bc`
- Access and retention: CC BY 4.0
- Synopsis basis: full-text semantic inspection through the paper MCP, followed by a
  scope interrogation against the retained v2 artifact

## Synopsis

For odd integers `q≥3` and `d≥1` with `q+d` a power of two, the paper studies the
unparameterized reachability relation `R(x,z)` of the generalized Collatz map `T_{q,d}`.
It proves that `R` is not first-order definable in Büchi arithmetic
`⟨ℕ,+,V_q⟩`; equivalently, no finite automaton recognizes the standard synchronous
base-`q` encoding of the full binary relation.

The proof assumes such a definition and constructs a definable reachable-floor relation.
Because the orbit of one is then a pure halving cycle, a further formula isolates exactly
the powers of two: powers of two reach one with only even nonterminal floors, while a
non-power exposes its odd part as an odd floor greater than one. Cobham's theorem forbids
this set in base `q`, since two and odd `q` are multiplicatively independent. The family
includes the classical `T_{3,1}` map.

The result concerns representation by a finite automaton, not computability. It does not
exclude a decision algorithm, a fixed-target unary slice, an annotated or redundant
encoding without a finite-state projection to the canonical encoding, an asynchronous
transducer, or a pushdown or counter model. Parameters outside `q+d=2^s` remain open in
the paper because their terminal cycles can contain odd values greater than one.

## Source Assessment

The source is a recent unrefereed preprint. The argument's conclusion and its stated
limitations are internally explicit; no independent proof audit has been completed here.
No correction, withdrawal, or superseding version was found as of retrieval.

## Project Use

The theorem excludes a canonical synchronous base-`q` finite-automaton presentation of
the full Collatz reachability relation. It does not close `GPI₂`, forbid fixed-target or
annotated carry algorithms, or imply undecidability.

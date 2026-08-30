# Carelli (2026): Loop Termination and Generalized Collatz Sequences

**Citation.** Mishel Carelli, “Loop Termination and Generalized Collatz
Sequences,” in *53rd International Colloquium on Automata, Languages, and
Programming (ICALP 2026)*, LIPIcs 374, Article 175, pp. 175:1–175:21, 2026.

- Work identity: DOI [10.4230/LIPIcs.ICALP.2026.175](https://doi.org/10.4230/LIPIcs.ICALP.2026.175); related full version [arXiv:2605.15094](https://arxiv.org/abs/2605.15094)
- Canonical source: <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.175>
- Local artifact: `carelli-2026-loop-termination-generalized-collatz.pdf`
- Version and status: peer-reviewed ICALP 2026 proceedings version
- Retrieved: 2026-08-30
- SHA-256: `5935af239385edfa171ec4a24b096e7af5d7b222dbea20459e929a5ba93dcfe4`
- Access and retention: Creative Commons Attribution 4.0
- Synopsis basis: complete inspection of the 21-page proceedings article

## Synopsis

The paper studies termination of one-variable integer single-path
linear-constraint loops. It splits an infinite trace into a cyclic trace or a
self-avoiding trace. Every such loop with a cycle has a cycle of length at most
two, making cycle existence decidable by bounded integer linear programming.

For generalized Collatz maps

```text
T(x)=(mᵢx−rᵢ)/d  when x≡i mod d,
```

Proposition 17 proves that every unbounded orbit visits at least two residue
classes modulo `d`. The paper then defines a weak subclass with one common
multiplier and consecutive residue offsets. Its Reachability Conjecture says
that every unbounded orbit reaches one distinguished residue class. Proposition
17 proves this conjecture when `d=2`, because visiting two classes exhausts the
residues. Theorem 20 gives a polynomial-time termination algorithm for
one-variable integer linear-constraint loops conditional on the conjecture in
all moduli. Conversely, a termination algorithm would decide individual open
instances of that conjecture. The paper leaves every modulus above two open and
exhibits `T(x)=⌊4x/3⌋` as a concrete modulus-three instance.

## Source Assessment

The proceedings article is peer reviewed and openly licensed. The modulus-two
result concerns residue visitation for the common-multiplier weak subclass. It
does not decide point-to-point reachability, and it does not cover a binary
mixed-slope Syracuse map whose two branches have slopes `1` and `a`.

## Project Use

This is the current external boundary adjacent to the normalized-GPI₂ affine
compiler. It rules out citing the weak common-multiplier residue conjecture as
an obstacle at modulus two, while confirming that its theorem supplies neither
a decision algorithm nor an undecidability compiler for the project's mixed
signed `ax+B` point-reachability throat.

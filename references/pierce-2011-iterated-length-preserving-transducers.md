# Pierce (2011): Decision Problems on Iterated Length-Preserving Transducers

**Citation.** Alan Pierce, *Decision Problems on Iterated Length-Preserving
Transducers*, senior thesis, School of Computer Science, Carnegie Mellon University,
29 April 2011. Advisor: Klaus Sutner.

- Work identity: Carnegie Mellon University senior thesis; no DOI or report number
- Canonical source: https://www.cs.cmu.edu/afs/cs/user/mjs/ftp/thesis-program/2011/theses/pierce.pdf
- Local artifact: `pierce-2011-iterated-length-preserving-transducers.pdf`
- Version and status: final 27-page undergraduate thesis dated 29 April 2011; unpublished
- Retrieved: 2026-08-04
- SHA-256: `90b2f65bad54276293be17da5d36ce7cce99468b1fb57970dabc6a0063453875`
- Access and retention: publicly distributed by Carnegie Mellon University from its computer
  science thesis archive; no separate license statement was located in the artifact
- Synopsis basis: full-text inspection

## Synopsis

Pierce studies decision problems for reflexive-transitive closures of rational and
length-preserving transductions. The transducer classes include arbitrary, alphabetic,
sequential, reset, reversible, and binary toggle machines. The questions concern single-word
reachability, rationality or regularity of an iterated relation or image, and whether the image
of a specified language avoids a specified regular bad set.

The reset construction is the closest to a local rule. A reset transducer's state after reading a
letter depends only on that letter, so one sweep is an adjacent-pair replacement
`yᵢ = ρ(xᵢ₋₁, xᵢ)`, with a distinguished start predecessor. Theorem 18 makes the safety problem
`a* τ* ⊆ (Σ − {b})*` RE-hard by simulating one Turing-machine step in four sweeps. It uses a
large alphabet whose disjoint components encode the sweep phase, tape symbols, machine states,
and bounded neighborhoods. Thus the result proves universality of iterated local replacement,
but does not impose a binary alphabet or a two-state bound on the reset construction.

Theorems 22 and 24 instead build a reversible transducer and compile that particular machine to
a binary toggle transducer, whose transition at every bit is either the identity or the bit swap.
The binary compilation expands finite control into decision trees and fixed-length bitwise
writers. Its RE-hard safety problem starts from a constant block language rather than a regular
language. It therefore establishes that binary letter-to-letter iteration can carry universal
computation when finite control is unrestricted, not that a binary two-state transducer is
universal.

The thesis also proves RE-hardness of rationality and regular-image questions for broader
length-preserving or alphabetic transducers. Its conclusion leaves open how far the transducer
classes can be restricted before Turing-machine simulation disappears.

## Source Assessment

This is an unpublished undergraduate thesis rather than a peer-reviewed publication. The main
constructions are given transition by transition, but the reset theorem labels its preliminary
description a proof idea before supplying the explicit four-phase construction, and several
arguments use phrases such as “it can be easily checked.” No later correction or formal
verification was located. The exact decision problems differ materially from equality or
halting for one-tag systems, so universality does not transfer without an additional reduction.

## Project Use

The source isolates a useful boundary for `M₄(3)`: adjacent-pair reset dynamics and binary
toggle dynamics can each support universal iterated computation, but Pierce spends respectively
alphabet size and control-state count. Neither construction supplies the binary, two-state,
variable-output, dequeue-every-step source consumed by the two-state pushout compiler.

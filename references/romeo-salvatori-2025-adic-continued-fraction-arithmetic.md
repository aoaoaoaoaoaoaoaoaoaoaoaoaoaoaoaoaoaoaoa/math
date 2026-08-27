# Romeo and Salvatori (2025): P-Adic Continued Fraction Arithmetic

**Citation.** Giuliano Romeo and Tommaso Salvatori, “P-Adic Continued Fraction
Arithmetic,” arXiv:2512.11069v1 [math.NT], 11 December 2025.

- Work identity: arXiv:2512.11069
- Canonical source: https://arxiv.org/abs/2512.11069
- Local artifact: `romeo-salvatori-2025-adic-continued-fraction-arithmetic.pdf`
- Version and status: arXiv v1, 11 December 2025; preprint
- Retrieved: 2026-08-06
- SHA-256: `97594d848dd37797289ad6a07bcc2cfa128336050f7c901f2e2911fc448ac576`
- Access and retention: author-distributed arXiv preprint; no explicit artifact license was located
- Synopsis basis: full-text inspection of the transformation algorithms, termination conditions, and exceptional cases

## Synopsis

The preprint gives algorithms for computing p-adic continued fractions after Möbius and
bilinear transformations of their inputs. Rather than first reconstructing the represented
p-adic number, the algorithms consume enough input partial quotients to certify output digits,
tracking the transformation through matrices.

For a fixed Möbius transformation, finite input consumption is proved outside explicit
obstructions involving zero numerator or denominator and ambiguity in the output valuation.
Unbounded valuations among the input partial quotients force progress in broad cases. The paper
also exhibits bounded-valuation input patterns for which arbitrarily long lookahead can be
necessary, so a fixed fractional-linear change of coordinates is not automatically a
finite-state transducer.

The bilinear algorithms carry analogous domain and valuation qualifications. The work is about
computing transformed expansions, not a general termination theorem for rational orbits.

## Source Assessment

This is a recent one-version preprint. No journal publication, external correction, or
source-level defect was identified; its claims should be treated as prepublication results.

## Project Use

Gives both a mechanism and a warning for removing the guard's fixed Möbius gauges. Unbounded
digit valuations may make the transformation finite-state; bounded valuations require a
separate argument rather than an appeal to coordinate invariance.

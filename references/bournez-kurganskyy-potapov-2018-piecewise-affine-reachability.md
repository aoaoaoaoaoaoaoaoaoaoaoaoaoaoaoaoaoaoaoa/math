# Bournez, Kurganskyy, and Potapov (2018)

**Citation.** Olivier Bournez, Oleksiy Kurganskyy, and Igor Potapov,
“Reachability Problems for One-Dimensional Piecewise Affine Maps,”
*International Journal of Foundations of Computer Science* **29**(4):529–549,
2018.

- DOI: https://doi.org/10.1142/S0129054118410046
- Canonical source: https://livrepository.liverpool.ac.uk/id/eprint/3023232
- Local PDF: `bournez-kurganskyy-potapov-2018-piecewise-affine-reachability.pdf`
  (author accepted manuscript, 21 April 2018)
- Retrieved: 2026-07-25
- SHA-256: `0c7148f4eaa91b34ecdac2bb62f99acab9023f6b6fcb8cc580da54704d6cbccf`

## Results used

Section 4 introduces additive `p`-adic weights `−v_p`. Theorem 9 proves
point-to-point reachability decidable for a rational piecewise-affine map on
finitely many bounded intervals when, at every prime, all branch slopes have
weights of one weak sign. Above the translation weights, a positive slope
weight cannot decrease the current denominator weight; negative slope weights
cannot raise it beyond the translation bound. Bounded intervals then contain
only finitely many rationals with bounded denominators.

The dimension-two campaign imports that mechanism, not the theorem verbatim.
Record `D2-D07` independently extends the finite-state argument from one
deterministic piecewise map to a nondeterministic finite family preserving a
common bounded rational interval, and then takes a product with a regular
control automaton.

## Audit notes

The paper is peer reviewed. The local file is the openly deposited author
accepted manuscript from the University of Liverpool repository; no explicit
permissive license was located on the record.

Theorem 9 does not state the private-prime endpoint theorem, the rational-base
carry automaton, or the regular-control extension. Those are project
derivations and require their own proofs. The paper's deterministic orbit
argument cannot by itself be cited for nondeterministic reachability.

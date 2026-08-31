# Serre (1970): The congruence subgroup problem for `SL₂`

**Citation.** Jean-Pierre Serre, “Le problème des groupes de congruence pour `SL₂`,”
*Annals of Mathematics*, Second Series 92(3) (1970), 489–527.

- Work identity: DOI [`10.2307/1970630`](https://doi.org/10.2307/1970630)
- Canonical source: [Annals of Mathematics](https://annals.math.princeton.edu/1970/92-3/p06)
- Author-hosted source inspected: [Collège de France PDF](https://www.college-de-france.fr/media/jean-pierre-serre/UPL8543926451197744553_Serre_Pb._Congruence_SL2.pdf)
- Local artifact: none; the operator excluded reference PDFs from Git
- Version and status: peer-reviewed publication
- Retrieved: 2026-08-30
- Inspected artifact SHA-256: `2a079cca247de1b4765a4c5cb0d70ef1351ee192115fa34a9cd41c3fa1ec5e37`
- Access and retention: official author-hosted scan inspected transiently; not retained
- Synopsis basis: full-text inspection of the published paper

## Synopsis

Let `K` be a global field, let `S` be a finite nonempty set of places containing the
Archimedean places, put `A=O_S`, and write `Γ=SL₂(A)`. Section 1.2 defines an
`S`-congruence subgroup as a subgroup containing one principal kernel

```text
Γ(𝔮)=ker(SL₂(A) → SL₂(A/𝔮))
```

for a nonzero ideal `𝔮`. The paper compares the profinite topology on `Γ` with this
congruence topology.

When `S` has at least two places, Theorem 2 computes the congruence kernel. If `S` is
not totally imaginary, the kernel is trivial. Corollary 3 on page 499 gives the operational
form: every `S`-arithmetic subgroup of `SL₂(K)` is an `S`-congruence subgroup. In
particular, for `K=ℚ` and `A=ℤ[1/p]`, every finite-index subgroup of `SL₂(A)` contains a
principal congruence kernel. Concretely, if `K₀≤SL₂(A)` has finite index and `φ:K₀→F` has
finite image, then `ker φ` is itself finite-index in `SL₂(A)`. Corollary 3 therefore gives an
ideal `𝔮` with `Γ(𝔮)⊆ker φ`, so this particular `φ` factors through reduction modulo `𝔮`.

When `S` has one place, the congruence kernel is infinite in the rational and imaginary
quadratic cases. The paper therefore separates the affirmative `S`-unit case from the
classical failure for `SL₂(ℤ)`.

## Source Assessment

The paper proves literal containment of a principal congruence subgroup in every finite-index
subgroup for `ℤ[1/p]`. The result is stronger than a merely finite or central congruence kernel;
that distinction is essential when transferring congruence density to all finite quotients.

## Project Use

For `p=19`, the theorem upgrades the Lean-checked full-matrix congruence witnesses in
`CongruenceBlindOrbit.lean` to profinite closure inside the finite-index `S`-arithmetic ambient
group `Γ₀(3;ℤ[1/19])`.

# Evertse and Győry (2013): Effective Results for Unit Equations over Finitely Generated Integral Domains

**Citation.** Jan-Hendrik Evertse and Kálmán Győry, “Effective results for unit equations
over finitely generated integral domains,” *Mathematical Proceedings of the Cambridge
Philosophical Society* 154, no. 2 (2013), 351–380.

- Work identity: DOI [10.1017/S0305004112000606](https://doi.org/10.1017/S0305004112000606)
- Canonical source: [Cambridge University Press](https://doi.org/10.1017/S0305004112000606)
- Inspected source: [author-hosted publisher PDF](https://pub.math.leidenuniv.nl/~evertsejh/13-uniteq.pdf)
- Local artifact: none; redistribution permission for the copyrighted publisher PDF was not established
- Version and status: peer-reviewed publication; first published online 2012-11-23; March 2013 issue
- Retrieved: 2026-08-08
- SHA-256: no local artifact; inspected PDF bytes were `d0ea6d3f74d6f17d6c2634724974db7886d23b2ad92179c445ada9140f0bb215`
- Access and retention: author-hosted access; Cambridge Philosophical Society copyright and no express redistribution license located, so metadata only
- Synopsis basis: full-text inspection of the 31-page author-hosted publisher PDF

## Synopsis

Let `A ⊇ ℤ` be an integral domain finitely generated as a `ℤ`-algebra, and let
`a,b,c ∈ A` be nonzero. The paper makes effective Lang’s finiteness theorem for the unit
equation

```text
aε+bη=c,   ε,η ∈ A×.
```

Theorem 1.1 gives an explicit computable bound on the polynomial-representative sizes of every
solution from a presentation `A=ℤ[X₁,…,X_r]/I` and degree-height bounds for the presentation
and coefficients. Corollary 1.2 combines that bound with effective ideal membership to enumerate
all solutions. The result specializes to effective two-variable `S`-unit equations over number
fields but also permits finitely generated characteristic-zero domains with transcendental
elements.

Theorem 1.3 gives an explicit computable exponent bound for

```text
aγ₁^(v₁)⋯γ_s^(v_s)+bγ₁^(w₁)⋯γ_s^(w_s)=c
```

when the nonzero `γ_i` are multiplicatively independent elements of the fraction field. It
therefore makes the solutions of this exponential equation effectively enumerable as well.

The proof combines effective number-field and function-field unit-equation bounds with effective
specialization, ideal-membership and linear-equation algorithms over polynomial rings. It does
not assume an algorithm for generators of the full unit group of an arbitrary finitely generated
domain; the paper notes that no such general algorithm was known.

## Source Assessment

No correction, retraction, or superseding version was identified in the inspected publication.
The retained record is metadata-only because the available author-hosted object is a copyrighted
publisher PDF without an express redistribution license. Exact theorem use should be checked
against the canonical publication or the inspected author-hosted copy.

## Project Use

Corollary 1.2 supplies the effective two-variable `S`-unit enumeration used to decide equality
of two semisimple cyclic `PGL₂(ℚ)` orbits in the rank-(2,2) edge-graph audit. Theorem 1.3
also supports the subsequent cyclic-power filtering step.

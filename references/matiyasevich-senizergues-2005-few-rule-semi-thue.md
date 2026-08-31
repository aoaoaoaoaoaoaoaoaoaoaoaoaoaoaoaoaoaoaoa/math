# Matiyasevich and Sénizergues (2005)

**Citation.** Yuri Matiyasevich and Géraud Sénizergues, “Decision problems for
semi-Thue systems with a few rules,” *Theoretical Computer Science* **330**(1),
145–169, 2005.

- DOI: https://doi.org/10.1016/j.tcs.2004.09.016
- Conference DOI: https://doi.org/10.1109/LICS.1996.561469
- Local PDF: none; the inspected retrieval artifact remains outside the repository
- Inspected artifact SHA-256:
  `ea23da231d634b8b4a9c9c522884b7e744cfc5b3369f67bb49ec31482334023d`
- Retrieval audits: 2026-07-24 metadata; 2026-08-30 full text

## Results used

The paper proves undecidability of accessibility, common-descendant, termination, and
uniform termination for semi-Thue systems with three rules. Nicolas combines the
accessibility result with his explicit `k ↦ k+2` reduction to obtain undecidability of
`GPCP(5)`.

This does not approach `GPCP(3)` through the same compiler: that route would require an
undecidable one-rule accessibility source or a new reduction that removes the two transport
letters.

The final system `S₅` uses `u₁=xx̄`, `u₂=x²x̄²`, and exactly the three rules

```text
ρ(L)y → ρ(M)y,
u₂³ ρ(dⁿcdⁿ)y u₁² → u₂³ ρ(bⁿ)y u₂²,
xx̄ → ε.
```

They are arbitrary-substring rules. Formal derivations retain both surrounding contexts, and
the rule name does not determine the redex position. Writing
`B=⋃_{z∈A₄} Desc_D(ψ(z))`, the stable domain is the directed language
`Desc_D(Im τ₄)=B*y`, strictly smaller than the complete decoder domain `(yD₁*)*y`; it is not a
quotient by `xx̄=1`. In Proposition 3.5, one `D` step can move the greatest-lower-bound decoder
along a nontrivial `S̄₄` path; the cancellation rule therefore carries simulated order state
rather than inert housekeeping.

## Access note

No repository copy is retained. The 2026-08-30 audit inspected the complete journal article
through the configured paper-retrieval service and recorded the exact artifact digest above.
The earlier quantitative dependency is also stated and proved through the locally preserved
Nicolas paper.

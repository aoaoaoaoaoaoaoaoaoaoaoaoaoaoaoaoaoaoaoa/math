# Carvalho (2026)

**Citation.** André Carvalho, “The Post Correspondence Problem for free groups is
undecidable,” arXiv:2607.13951v2 [math.GR], 21 July 2026.

- Canonical source: https://arxiv.org/abs/2607.13951
- Local PDF: `carvalho-2026-free-group-pcp.pdf`
- Retrieved: 2026-07-24
- SHA-256: `5f4329da780475a1a268d3e8860beb045213cef021ca7523e93dc804fa8faa74`

## Results used

Carvalho reduces cyclic-tag halting to nontrivial fixed points of a finite partial
deterministic inverse transducer, then reduces those fixed points to a nontrivial equalizer
of two free-group homomorphisms. One homomorphism is injective with finite-index image,
and the target group can be fixed as `F₂`.

The useful mechanism is the freely reduced discrepancy

```text
Δ(w) = w⁻¹T(w).
```

On a legal transition, free cancellation deletes the simulated queue head while the
transducer appends the rule output. An `H` marker counts simulated steps and a `p` marker
prevents the discrepancy from becoming trivial on an invalid or vacuous path. The converse
classifies every fixed point as a closed transducer path.

For the `GPCP(3)` campaign this is evidence for implicit deletion through cancellation, not
a bounded-source theorem. The subgroup of closed input paths is given by a computed free
basis whose rank depends on the transducer. Passing to three positive source letters would
still require a uniform rank bound or a sound positive-monoid compiler for that subgroup
constraint.

For the cyclic-tag transducer with `m` appendants, direct reconstruction of its Stallings graph
gives closed-path rank `3m+1` and an explicit basis. Combining Proposition 3.2, Lemma 3.5, and
the all-fixed-points-are-loops clause of Theorem 3.6 sharpens the construction: the fixed subgroup
is trivial in the nonhalting case and infinite cyclic in the halting case. Through Theorem 4.1,
the resulting PCP equalizer consequently has promised rank zero or one. This is a derived
corollary of the paper's construction, not a theorem stated in the preprint; no external novelty
claim is made for it.

## Audit notes

The local file is arXiv v2. It is a new preprint and has not been peer reviewed. Free-group
words admit inverses and reduction; none of the paper's undecidability statements is itself a
classical free-monoid `GPCP(3)` result.

# Lohrey and Steinberg (2011): Tilings and Submonoids of Metabelian Groups

**Citation.** Markus Lohrey and Benjamin Steinberg, “Tilings and Submonoids of
Metabelian Groups,” *Theory of Computing Systems* **48**:411–427, 2011.

- Work identity: DOI [10.1007/s00224-010-9264-9](https://doi.org/10.1007/s00224-010-9264-9); [arXiv:0903.0648](https://arxiv.org/abs/0903.0648)
- Canonical source: <https://arxiv.org/abs/0903.0648>
- Local artifact: `lohrey-steinberg-2009-tilings-submonoids-metabelian.pdf`
- Version and status: arXiv v1, 3 March 2009; peer-reviewed journal work published online in 2010 and in volume 48 (2011)
- Retrieved: 2026-08-30
- SHA-256: `8c87a04dc24cc2ed727f6044cc08727c773f29883d691225dd417d441d62ff6d`
- Access and retention: author-posted arXiv version; no separate permissive license identified in the artifact
- Synopsis basis: complete inspection of the 17-page arXiv version, cross-checked through the local Paper retrieval service

## Synopsis

The paper encodes a fixed deterministic Turing machine by signed edge and
color tiles on the integer grid. Finite sums of translated tiles cancel a
source boundary exactly when the encoded machine accepts. Identifying the
finite-support grid functions with a finite-rank free
`ℤ[ℤ²]`-module turns this into undecidable membership in one fixed finitely
generated subsemimodule.

Semidirect-product transfer then gives a fixed finitely generated submonoid
with undecidable membership in `ℤ wr ℤ²`. A decomposition of the commutator
subgroup gives the same conclusion for the free metabelian group of rank two.
Over nonzero finite coefficient rings, a distinct-position version of the
tiling sum yields fixed subset-sum hardness and hence undecidable rational
subset membership in every two-dimensional lamplighter group
`G wr ℤ²` with `G` nontrivial.

The construction depends on a free finite-rank `ℤ[ℤ²]`-module: independent
grid translates carry independent tile data. It does not apply merely because
a group is metabelian or has a rank-two multiplier quotient.

## Source Assessment

The retained file is the first arXiv version of the later peer-reviewed
journal article. No correction or retraction was found. Its negative results
are for the named free-module, wreath-product, free-metabelian, and
lamplighter settings; they do not classify every finitely generated
metabelian group.

## Project Use

This is the closest generic metabelian undecidability theorem to the fixed
Collatz cusp `Γ₆=ℤ[1/6]⋊ℤ²`. It does not transfer: as a
`ℤ[X±¹,Y±¹]`-module, the normal subgroup `ℤ[1/6]` satisfies
`(X−2)·1=(Y−3)·1=0` and lacks the free translated grid required by the tiling
reduction. The source therefore blocks an invalid black-box hardness appeal
without deciding rational-subset membership in `Γ₆`.

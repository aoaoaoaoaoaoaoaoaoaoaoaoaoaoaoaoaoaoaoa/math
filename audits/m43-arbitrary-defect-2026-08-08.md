# M₄(3) arbitrary-defect audit

**Date:** 8 August 2026

**Status:** arbitrary residue skeleton, pure-defect reset, and local bridge-fracture grammar
formalized; semantic realization and malformed-word converse open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** replace defect-count casework by one exact normal form for every physical word in the
parabolic family

## Verdict

The report survives and its main conclusions compose. Every cleared safe atom reduces to one of
two rank-one actions on a protected plane; every residue-two atom reduces to one fixed invertible
plane action `A₂` with `A₂⁴=2I`. A safe/defect skeleton is zero modulo three exactly when one
internal maximal defect run has one of two phase patterns:

```text
count ≡ 1 (mod 4) and the safe phases differ,
count ≡ 3 (mod 4) and the safe phases agree.
```

There is no collective residue cancellation beyond one such run. The theorem is connected back
to the concrete rational atoms: every skeleton avoiding these patterns is nonzero over `ℚ`.

A second integral lift proves more than the residue scan for a block made only of defects. Every
nonempty pure residue-two block has a bridge with nonzero determinant. Such a block cannot be a
singular endpoint of a minimal zero.

Finally, every nonzero singular regular bridge is rank one. A product of arbitrarily many such
walls, separated by arbitrary transports, is zero exactly when one incidence between consecutive
walls is zero. Extra walls create no collective mode of annihilation. The bridge cokernel is the
explicit row `(v,-4w)` when the exterior state is `(0,v,w)`; it is nonzero for every regular wall
word and annihilates the bridge from the left.

These results reduce the parabolic converse to one projective incidence between two consecutive
singular endpoints with invertible transport between them. They do not identify that incidence
with the paired-Neary language and do not construct the required intended contexts. `M₄(3)` remains
open.

## Source Lock

The parallel attack read branch `m43-cube-root-incidence` at
`55d633deb47faf334d31debb517dbd8e77c74dec`. Its transient final report has SHA-256 digest
`7aad42d88042917c489e2d005cee962a0372b4c3ca01990640e8d3cdf67d26af`. Formalization was
rebased conceptually onto the already-pushed deletion-scanner ratchet
`efea542c4a85f5265b077080b0c32baf6d55f678`.

## Residue Grammar

On the protected coordinates, the exact cleared reductions are

```text
A₀ = [[1,2],[0,0]],
A₁ = [[0,0],[2,2]],
A₂ = [[1,1],[2,1]].
```

Lean proves the fourth-power identity, the complete four-periodic incidence table, and a product
factorization for an arbitrary list of defect runs. The same factorization is then proved for
the full `3 × 3` cleared residues. `safeNumerator`, `residueTwoNumerator`, `safeResidue`, and
`residueTwoResidue` are the single canonical integral and modular representations; no duplicate
residue model was retained.

`defectSkeletonProduct_ne_zero_of_not_bad` consumes the modular theorem. Its input contains the
actual safe labels and the actual lists of defect labels. If the phase-and-length skeleton has no
bad internal run, a hypothetical rational zero would clear to an integer zero and hence to a
zero modular skeleton, contradicting the complete table.

The table is a one-way exact nonvanishing certificate. A bad modular skeleton need not be a
rational zero.

## Pure-Defect Reset

Let `N=64D` be the integral numerator of a residue-two atom. With `4C` and `C⁻¹` integral,

```text
(4C) adj(N)ᵀ C⁻¹  (mod 3) = [[2,1,1],[0,0,0],[0,0,0]].
```

Starting from the cleared exterior seed `(0,22,9)`, a nonempty word of these transitions has
first coordinate `2ʳ` modulo three. Lean tracks the exact rational scaling simultaneously, so
the physical exterior wall coordinate is nonzero. The bridge determinant identity then gives
`pureDefect_bridge_det_ne_zero` for every nonempty defect list, both letters, every wait, every
body, and every `β`.

The report's sharper valuation

```text
ν₃(det K)=β+2
```

was independently reconstructed from the same normalized first coordinate, but the retained Lean
theorem states the consumed conclusion: invertibility. No later theorem presently uses the exact
valuation.

## Bridge Fracture

For the code's factors `coreOutput=A` and `coreInput=B`, a regular middle word `M` induces
`K=BMA`. Lean proves:

- `K≠0`;
- `det K=0` exactly on the first exterior-coordinate wall;
- every wall bridge is a nonzero outer product;
- a varying chain of outer products is one outer product multiplied by all consecutive
  incidence scalars;
- the chain is zero exactly when one such scalar is zero;
- `bridgeCokernel M=(v,-4w)` for exterior state `(0,v,w)`;
- on the wall this row retracts through `B`, is nonzero for invertible `M`, and annihilates `K`.

This formalizes the report's minimal-zero descent without introducing an index-heavy duplicate
physical-word parser: the earlier exceptional-chain theorem already contracts every physical
word to the bridge word, and the fracture theorem consumes any sequence of its rank-one wall
factors.

## Independent Checks

Exact symbolic recomputation verified the bridge identities and arbitrary residue skeleton. A
bounded diagnostic enumerated 88,573 projective states without finding a short annihilator; a
deeper search covered approximately 7.17 million states through word depth fourteen with the same
outcome. These searches are falsifiers only and are not theorem evidence.

## Remaining Enemy

Every minimal parabolic zero now has two singular endpoint bridges, only invertible bridges
between them, and one zero projective incidence. Neither endpoint is a nonempty pure-defect block;
every residue skeleton outside the two four-periodic bad patterns is excluded.

The remaining obligations are exact:

1. construct endpoint contexts and transport realizing the paired-Neary coefficient-zero
   language;
2. prove that every zero incidence decodes to that language, or exhibit a malformed incidence;
3. decide the projective transport of the oriented wall cokernel through arbitrary nonsingular
   mixed bridges.

Safe return is no longer a prerequisite: any direct proof of these incidence claims closes the
parabolic lane and takes priority over further invariant building.

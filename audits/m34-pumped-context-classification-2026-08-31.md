# M₃(4) Pumped-Kernel Context Classification Audit

**Date:** 2026-08-31
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `8423927` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimePumpedCuts.lean`](../MatrixMortality/GuardedMixedPrimePumpedCuts.lean) and
[`GuardedMixedPrimePumpedContext.lean`](../MatrixMortality/GuardedMixedPrimePumpedContext.lean)
**Finite certificate:**
[`certify_mixed_prime_pumped_context.py`](../tools/certify_mixed_prime_pumped_context.py)

## Verdict

The seven length-`31` pump schemas from `G3-S16` admit an exact uniform Parikh-cut census at every
pump power. Families three, five, and seven retain only the universal cut `3`; their
internal/internal contextual cell is impossible at every depth. Families one, two, four, and six
also acquire the moving cuts `30,32,…,30+2(k-1)`. Family six alone has static cuts `27,28`.

Lean proves that the relation letters on both sides disagree immediately before and after every
universal or moving cut. Next-letter alignment can survive only at family six's cut `27`;
previous-letter alignment can survive only at its cut `28`, where extending the alignment by one
more letter is impossible. Lean also eliminates every moving-cut internal/internal placement:
length balance forces the last moving cut and one of three tiny macro layouts, each contradicted
by the common fixed prefixes `DTTT` and `TTDD`. The sole cut-`27` internal residue is
arithmetically confined to `0≤k≤11`; an exact assignment-complete certificate rejects all `156`
remaining literal geometries.

This is not an all-seven one-context extinction theorem. The moving-cut internal/internal cells
are dead, but the comparable-prefix/suffix and same-shorter placement taxonomy is not represented
by one typed extraction theorem for these seven families. Lean separately rejects the only
cut-`28` right-conjugacy orientation and proves a fixed `25`-letter mismatch at the weak cut-`27`
orientation; composing those local gates with every lawful layout remains an explicit obligation.
No claim covers several contexts, several kernel relations, or a multi-window quotient derivation.

## Uniform Census

For a base word `W`, insertion cut `h`, two-letter pump `S`, and power `k`, define

```text
pumpAt(W,h,S,k) = take(h,W) · S^k · drop(h,W).
```

Lean proves the exact length, repeated-block addition, prefix transport, and suffix transport
laws. Increasing the pump power by one adds the same Parikh vector to both relation prefixes
beyond their insertion cuts. The infinite census therefore reduces to the base words, one
bounded post-insertion window, and a two-letter recurrence.

The resulting positive proper dilation-balanced prefix cuts are:

| Families | Cuts at power `k` |
| --- | --- |
| `3,5,7` | `3` |
| `1,2,4` | `3` and `30+2i` for `0≤i<k` |
| `6` | `3,27,28` and `30+2i` for `0≤i<k` |

The suffix census is the complementary image of the prefix census because both relation sides
have equal total Parikh vectors.

## Local Gates

Lean transports finite two-seed letter checks through every pump depth. It proves:

- the letters immediately after cut `3` disagree in all seven families;
- the letters immediately before cut `3` disagree in all seven families;
- both adjacent letter pairs disagree at every moving cut;
- family six cut `28` has unequal next letters;
- family six cut `27` has unequal previous letters;
- at family six cut `28`, the preceding two-letter blocks cannot both agree.

Consequently an aligned next letter at a proper balanced cut forces exactly family six and cut
`27`. An aligned previous letter forces exactly family six and cut `28`. These are formal
semantic case theorems, not a bounded table lookup at the final pump depth.

## Internal Cells

The literal contextual-fork layout is

```text
YZXYX = P L_k Q,       XZYXY = P R_k Q,
```

with nonempty `X,Y,Z`. In an internal/internal placement, the Parikh extraction supplies a
positive proper balanced cut. When the only cut is `3`, positivity and the fork-length inequality
contradict internality. Lean closes this cell uniformly for families three, five, and seven.

For family six's exceptional cut `27`, the audited tail decomposition forces

```text
|Q|=2k+1,       {|X|,|Y|}={2k+3,2k+2},
|Z|=|P|+22-4k>0,       |P|<min(|X|,|Y|).
```

Lean derives `k≤11`. The finite certificate then enumerates both orientations and every lawful
prefix length. A disjoint-set closure represents each variable letter of `X,Y,Z`; positions
outside the relation force common-context equality, while positions inside bind the exact `L_k`
and `R_k` letters. Every geometry forces one equivalence class to contain both `D` and `T`.

```text
maximum power: 11
orientations: 2
assignment-complete geometries: 156
survivors: 0
payload SHA-256: 013124fe8b1a55fe29af90c1f18d86356d4506d2dde85bf9cb90ad8354cc1f30
```

The same arithmetic bounds the weak comparable cut-`27` residue by `k≤11`; its full literal
assignment interface remains separate unless identified with the certified residue structure.

For families one, two, four, and six, any moving internal/internal cut paired with the universal
complementary cut `3` is terminal. Lean proves that the only possible length quadruples are

```text
(|X|,|Y|,|P|,|Q|) = (1,2,0,0), (2,1,0,0), or (2,2,1,1).
```

The literal fork equations then require one or two initial letters of `Z` to agree with
incompatible slices of the fixed relation prefixes `DTTT` and `TTDD`. This rejects all pump
depths without a finite cutoff.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The seven-family balanced-prefix census is exact at every pump power | promotion | Lean induction theorem |
| Universal and moving cuts fail the adjacent alignment gates uniformly | promotion | Lean transport theorems |
| Families `3,5,7` have no internal/internal one-context placement | promotion | Lean arithmetic obstruction |
| Every moving-cut internal/internal literal placement is impossible | promotion | Lean length classification and fixed-prefix contradiction |
| Family-six cut `28` has no one-letter right-conjugacy repair | promotion | Lean word identity obstruction |
| The weak family-six cut-`27` comparison has a fixed `25`-letter mismatch | promotion | Lean finite-slice transport |
| Family-six cut-`27` internal residues exist only for `k≤11` | promotion | Lean arithmetic theorem |
| All such finite literal residues are impossible | promotion | exact `156`-geometry certificate |
| Every one-context placement of all seven pump families is impossible | open | no typed exhaustive layout extraction composes all local gates |
| Several contexts or multi-window quotient derivations are impossible | open | outside the decomposition |
| `M₃(4)` follows | rejected | general address comparison, dynamic production, and endpoint converse remain |

## Master Delta

```text
FORMAL CUTS: exact for seven infinite pump families.
FORMAL EXTINCTION: every internal/internal moving cut; families 3,5,7; local alignment gates;
cut-28 right conjugacy; weak cut-27 fixed block.
FINITE EXTINCTION: 156 family-six cut-27 literal residues.
OPEN CUT: type and discharge the exhaustive comparable/same-shorter layout extraction.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, Ruff, ty, forbidden-aperture scan, and exact finite certificate all pass.
The source SHA-256 digests are:

```text
c07e69b9cf6daa5841c939259f3ee11c864dbf7ccbf49ee167802d98cf2d2d23  GuardedMixedPrimePumpedCuts.lean
88155aa2aaea9e6a668f20ef7ebd6558799fd0faa81aabcf26db609376d8cdbf  GuardedMixedPrimePumpedContext.lean
072e46da6ca1aa26c4cc7528cf96d9621c1c519eebc72b7a41c1d88110b6a51f  certify_mixed_prime_pumped_context.py
```

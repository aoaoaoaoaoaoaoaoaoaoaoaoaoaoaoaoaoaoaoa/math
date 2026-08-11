# `M₃(4)` Mixed-Branching Recognizer Audit

**Date:** 2026-08-11  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `ab0a555f7ea7c4425302709cc4de022879e52fc9` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a7b3bda-8ab8-83ea-8e25-9e5ef463bfed  
**Claim:** the width-three body `bcbcbb` has a complete equal-length branching grammar and an
integral three-state representation with exactly its paired zero language on all raw controls.  
**Status:** formalized and strict-gate checked.

## Verdict

The fixed lower-bound witness fails. For `β=3` and body `q=bcbcbb`, the complete terminal
history language is

```text
P₀(A₀|B₀)*,
P₀=(CBC,BCB,BBB),
A₀=(BBB,BCB,CBB),
B₀=(BBB,CBC,BBB).
```

The null blocks `A₀` and `B₀` have equal length. Nevertheless three explicit integral states
recognize the paired zero language on the entire free control monoid. Thus exponentially many
same-level terminal histories, equal-length branching, and a finite flower of affine returns do
not force same-zero dimension four.

## Grammar reconstruction

For a stroke history `S`, let `E(S)` concatenate its three-letter strokes and let `O(S)`
concatenate the body output selected by each stroke head. Null histories satisfy

```text
E(S)b=bO(S).
```

The Lean proof uses exact left/right word residuals. A right-residual invariant restricts every
reachable nonempty right residual to `b`, `bb`, or `bbb`. The four live residual entrances then
force precisely the two three-stroke returns `A₀` and `B₀`. Three successive prefix
cancellations force `CBC`, `BCB`, and `BBB` before the null tail. This avoids cardinality or
bounded-search assumptions.

The relevant declarations are:

- `MixedBranchingRecognizer.mixedNull_iff`
- `MixedBranchingRecognizer.mixed_terminal_match_iff`
- `MixedBranchingRecognizer.terminalControl_decode`

## Integral representation

The generators and boundaries are

```text
B=[[0,2,1],              C=[[0,2,-432372898],       T=[[1,0,0],
   [0,5,3703455],           [0,7,5236172],             [0,-1,21436039],
   [0,0,1]],                [0,0,1]],                   [0,0,1]],

λ=(1,0,0),  δ=(1,0,1)ᵀ,  γ=Tδ=(1,21436039,1)ᵀ.
```

For every raw word `u`, Lean proves

```text
H_uδ=(G(u),Y(u),1)ᵀ,
Y(bu)=5Y(u)+3703455,
Y(cu)=7Y(u)+5236172,
Y(tu)=21436039−Y(u),
G(bu)=2Y(u)+1,
G(cu)=2(Y(u)−216186449),
G(tu)=G(u).
```

Hence `λH_wγ=G(wt)`. A `b` guard is odd, while a `c` guard vanishes exactly when the remaining
carry is `216186449`.

## Arbitrary-control converse

The converse is a proof, not a finite word test.

1. Adjacent toggles are removed right-to-left. Lean proves that scouring preserves both the
   paired decoder and the matrix product.
2. Every scoured word has a unique decomposition into the four macros `b`, `tb`, `c`, `tc`,
   followed by at most one unmatched toggle.
3. With centred carry `x=2Y−21436039`, these macros act by

```text
b:  x ↦  5x+93151066,       tb: x ↦ −5x−93151066,
c:  x ↦  7x+139088578,      tc: x ↦ −7x−139088578.
```

4. The target `410936859` has one successful eight-macro inverse entrance. The return state
   `−21436039` has exactly two successful nine-macro first returns, corresponding to `A₀` and
   `B₀`.
5. At every graph node, Lean cases on all four macros and proves the omitted inverse values
   nonintegral with Presburger arithmetic. The two apparent competitors are followed to states
   with no integer predecessor. Carrying both terminal bases `±21436039` through the recursive
   theorem excludes an unmatched final toggle.

The resulting publication seam is

```text
MixedBranchingRecognizer.recognizerCoefficient_eq_zero_iff_paired
```

and quantifies over every `List PairedControl`.

## Degeneracy audit

Both data determinants vanish. Their exact common kernel condition is

```text
Bv=0 ↔ v₁=v₂=0,
Cv=0 ↔ v₁=v₂=0.
```

The toggle satisfies `T²=I` and `det T=−1`. Every actual suffix state has last coordinate one,
both boundaries are nonzero, and every generator product is nonzero. The construction therefore
uses deliberate common-kernel guard refresh, not a zero-product or boundary loophole.

## Scope and strategy effect

The theorem is instance-fitted. It does not recognize arbitrary bodies, prove regularity of all
terminal sections, or decide `M₃(4)`. It does close the proposed fixed positive-projective
witness and the broader heuristic that equal-length binary branching or finitely many affine
return cycles alone force four states.

The surviving lower-bound route must derive a shift incompatibility uniformly from an unbounded
terminal section. The surviving constructive routes remain a source-uniform common-kernel
shuttle and transverse dynamics with an infinite terminal section.

## Verification

The strict project gate compiles the module, runs all default environment linters, checks the
forbidden-token policy, and compares the transitive axiom output for every publication-facing
declaration against `verification/axioms.txt`. No axiom, `sorry`, unsafe declaration, warning
suppression, or bounded enumeration enters the proof.

# Unconditional Separator Audit

Date: 2026-08-07

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a75de8b-1db8-83ea-b8ce-6b69a50b0aad)

## Enemy Lock

```text
MASTER: prove M₃(4) undecidable.
VICTORY: a total computable four-generator 3 × 3 mortality reduction with a complete
         arbitrary-product converse.
LIVE OBSTRUCTION: construct a source-computable three-state same-zero recognizer for the
                  unrestricted paired zero language, or prove that one explicit paired language
                  has rational zero-language dimension at least four.
KILLED LANES: exact rank three; finite support/minrank; finite-mode expanding history;
              rational phase-local compression; inverse-saturated projective dynamics.
```

## Verdict

The report met none of the three demanded thresholds: it neither proves `M₃(4)`, proves a
positive-common-shift lower bound, nor derives inverse saturation. It nevertheless resolves one
compiler seam completely and supplies a valid counterexample to the proposed singular-collapse
argument.

The decoder construction is not new mathematics in this repository. `HistoryFracture.lean`
already owns an injective base-five decoder on every control word with singular data matrices.
The report uses the dual positional state `(code,phaseSign·B^length,B^length)` instead of the
checked `(code,phaseSign,1)`, but both mechanisms consume the entering phase only after storing
its selected role digit. The result is retained as a decisive interpretation of the checked
construction: rank loss need not identify two positive decoded histories.

The separator theorem is new and stronger than both former repository variants. For arbitrary
square control matrices over a field, adjoining the single outer product `γλ` converts scalar
zero reachability to mortality without invertibility, a fixed anchor, nonzero boundary vectors,
or any orbit hypothesis. Lean now checks this as `mortal_adjoin_outer_iff`. The two weaker generic
theorems and the history encoder's rational normalization layer were deleted.

## Singular Decoder Countermodel

The report assigns four role digits and takes

```text
H_t = diag(1,−1,1),

H_x = [[1, (δ_rule,x−δ_erase,x)/2, (δ_rule,x+δ_erase,x)/2],
       [0,                         0,                         −B],
       [0,                         0,                          B]],

γ = (κ,1,1)ᵀ.
```

For every arbitrary control word `y`, including malformed and toggle-only words,

```text
H_yγ = (Cκ(D(y)), ε(phase(y))B^|D(y)|, B^|D(y)|)ᵀ.
```

A data control reads the sign returned by its suffix, adds the corresponding role digit, and
then resets the sign to erase. Its last two rows are dependent, while its first row is independent
when `B≠0`; hence it has rank two. With base at least five and digits `1,2,3,4`, the code is
injective on role words. The discarded linear direction is therefore transverse to the positive
semantic orbit rather than a collision between decoded histories.

The checked repository matrices already establish the same point:

```text
H_b = [[5,−1,2], [0,0,−1], [0,0,1]],
H_c = [[5,−1,3], [0,0,−1], [0,0,1]],
H_t = [[1, 0,0], [0,−1,0], [0,0,1]].
```

`historyProduct_mulVec_column` proves their all-word decoder invariant, and
`historyCode_injective` proves that distinct decoded role words have distinct codes. The new
`historyDataMatrix_det` theorem checks singularity over every commutative ring. Over `ℚ`, the
dependent last two rows and nonzero first entry give rank exactly two.

Thus the implication

```text
singular positive action
  ⇒ identified positive residuals
  ⇒ false target incidence
```

is false before the target law is used. Stable images, kernels, or orbit closures must exploit
the complete terminal equation; rank drop alone has no force.

## Unconditional Outer Separator

Let `H_a∈K^{d×d}`, `γ∈K^d`, `λ∈(K^d)*`, and `S=γλ`, with `K` a field. Then

```text
IsMortal({H_a}∪{S}) ↔ ∃y, λH_yγ=0.
```

The reverse implication is the three-block product

```text
S H_y S = γ(λH_yγ)λ = 0.
```

For the converse, first consider a zero product containing no separator. It is some `H_y=0`, so
`λH_yγ=0`. Every product containing separators has the unique fracture

```text
H_{u₀} S H_{u₁} S ··· S H_{uₘ}

= (∏_{i=1}^{m−1} λH_{uᵢ}γ)
    · (H_{u₀}γ)(λH_{uₘ}).
```

If an internal scalar vanishes, its block is the witness. Otherwise the outer product is zero.
Over a field, one exterior vector must vanish. If `H_{u₀}γ=0`, then `λH_{u₀}γ=0`; if
`λH_{uₘ}=0`, then `λH_{uₘ}γ=0`. Empty blocks, adjacent separators, exterior separators, a zero
separator, and zero control-only products are all included.

The Lean proof fractures an arbitrary mortality witness, applies the existing exact rank-one
chain formula, and performs precisely this case split. It replaces
`unitFamily_mortal_adjoin_outer_iff` and `fixedAnchor_mortal_adjoin_outer_iff`. All consumers now
use the stronger theorem. In particular, `historyMortalityFamily_rat_mortal_iff_zero` applies
directly to the original integral history controls; its scaling functions, scaled matrices,
fixed-anchor proof, and bridge-rescaling lemma have been removed.

For finitely many rational generators, choose one nonzero integer denominator for each generator.
The product attached to a word is multiplied by the product of those denominators, so mortality
is unchanged. Hence any total rational three-state same-zero compiler immediately gives four
integral `3 × 3` mortality generators. The separator converse is not a remaining master
obligation.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| All-word singular decoder invariant | restatement | existing Lean theorem; report gives a second positional convention |
| Singular data controls need not collide decoded positive histories | promotion | Lean decoder invariant, injective code, and singularity theorem |
| Arbitrary same-zero representation admits one outer-separator mortality lift | promotion | Lean theorem `mortal_adjoin_outer_iff` |
| The lift requires fixed anchors, invertible controls, or nonzero exterior orbits | rejected | contradicted by the universal theorem |
| The positive decoder alone recognizes the unrestricted paired target language | rejected | its row sections select at most one code ray per phase and length |
| The target equation forces inverse saturation or dimension four | open | no proof supplied |
| Any hard acceptance threshold from the prompt was met | rejected | acknowledged by the report |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: the complete scalar-zero-to-four-generator mortality converse, including singular
         controls, zero control products, every separator placement, and denominator clearing;
         rank drop by itself as a route to a positive residual collision.
REMAINS: construct a total source-computable three-state same-zero recognizer for the unrestricted
         paired language, or prove positive shift-equivariance forces rational dimension at
         least four for one explicit admissible nonminimum instance.
DISTANCE: only the recognizer remains. Any rational λ,γ,H_b,H_c,H_t satisfying the all-word
          same-zero law now completes the four-generator mortality reduction automatically.
```

The next attack must use the terminal equation to constrain singular one-way dynamics. It must
not revisit separator placement, fixed anchors, bare stable-image collapse, or another assumed
inverse completion.

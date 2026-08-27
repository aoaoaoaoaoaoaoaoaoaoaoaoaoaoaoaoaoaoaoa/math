# Ternary Closed-Block Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a779593-d4e8-83ea-af7f-e4b5beebd045)

## Verdict

The report does not prove `M₃(4)`. It does close two increasingly permissive source-compression
classes. First, the four Neary roles cannot factor exactly through three fixed physical macros,
even if either target morphism erases, codewords are empty or coincident, and parsing is wholly
nonunique. Second, fixed role spellings cannot be rescued by a stationary overlap which returns
to one common residual after every complete deletion-width block.

The first theorem and the arithmetic throat of the second are Lean-checked. The complete
closed-block assembly is an independently reconstructed paper proof. Its scope must not be
inflated to all finite-delay encoders: state-dependent spellings, a residual left open across
blocks, nonfactorial adjacent-role codes, and global solvability-only recodings remain live.

## Paired-Parikh Obstruction

For a binary pair `(u,v)`, put

```text
Π(u,v)=(|u|₁,|u|₀,|v|₁,|v|₀).
```

Writing `μ=|q|_b` and `ν=|q|_c`, the four role vectors in the order
`R_c,R_b,D_b,D_c` are the rows of

```text
[[1,0,2+2μ+ν,1+βμ],
 [2,β,2,1],
 [2,β,0,1],
 [1,0,0,1]].
```

The report expands its determinant as `2β²μ`. The Lean proof avoids trusting that expansion. It
solves the four coordinate equations directly and proves that right multiplication by this
matrix is injective whenever `β>0` and `μ>0`. Nonsingularity follows inside mathlib.

For any physical alphabet `C`, possibly erasing morphisms `g,h`, and macro word `z`, additivity
gives

```text
Π(g(z),h(z)) = ∑_{a∈C} |z|_a Π(g(a),h(a)).
```

Thus an exact macro factorization writes the nonsingular four-role matrix as a `4×|C|` matrix
times a `|C|×4` matrix. The resulting dimension bound is

```text
4 ≤ |C|.
```

No nonerasure, injectivity, unique decoding, prefix code, equal length, or nonempty-word premise
appears in the formal statement.

## Stationary Closed Blocks

Let `n=β−1`. A stationary closed-block proposal fixes physical spellings

```text
ρ_b, ρ_c, δ_b, δ_c
```

for the two rule and deletion roles, along with possibly erasing target morphisms `g,h` and
fixed residual words `A,B`. For every rule letter `x` and every deletion tail
`y∈{b,c}^n`, it requires

```text
A g(ρ_x δ(y)) = H(xy) A,
B h(ρ_x δ(y)) = V_x 0^n B.
```

Counting bits cancels `A,B`. Comparing tails whose number of `b` letters differs by one forces a
common lower deletion image `d` and an integral upper residual shift `Δ`. Nonnegativity gives

```text
d ∈ {(0,0),(0,1)},
Δ ∈ {(-1,0),(0,0)}
```

for `β≥4`. Lean checks these two complete integer case reductions as
`commonLowerDeletion_cases` and `upperResidualShift_cases`.

If `Δ=0`, the upper Parikh map has rank two and the source alphabet has at most three letters, so
its kernel has dimension at most one. The two rule-minus-deletion differences must therefore
have dependent lower images. For `d=(0,0)` their determinant is `−βν`; for `d=(0,1)` it is
`2βμ`. A mixed body makes both nonzero.

If `Δ=(-1,0)`, then `δ_c` has zero upper image. It cannot be empty: the tails
`bc^(n−1)` and `c^(n−1)b` would otherwise have the same physical spelling, forcing
`H(b)1^(n−1)=1^(n−1)H(b)`, whose second letters differ. Hence its nonzero source Parikh vector
spans the one-dimensional upper kernel. The remaining rule difference must map under the lower
morphism to a multiple of `d`, but its first coordinate is `−(2μ+ν)`, again impossible for a
mixed body.

This proves the stationary closed-block no-go as a paper theorem. The finite-dimensional kernel
assembly and the word-level noncommutation step have not been transcribed into Lean; no
publication-facing declaration claims that they have.

## Universal-Source Application

The checked Neary compiler has `β=10p` with `p>0`, hence `β≥10`. Its woven Table-2 appendant
contains an all-`b` phase track and an all-`c` phase track, each longer than one position; dropping
the final `b` therefore leaves both letters in every body. The paper theorem applies uniformly
to that undecidable family.

This destroys the tempting idea that a more permissive fixed macro, erasure, boundary fragment,
or block-closing overlap will absorb the fourth role. A successful ternary GPCP compiler must
change a role's spelling with state, share physical letters across semantic boundaries without a
stationary factorization, retain an open residual across complete blocks, or preserve only global
solvability under a genuinely different target recoding.

Nicolas's `+2` alphabet tax cannot literally be moved into fixed boundaries either. Its two copy
letters reproduce arbitrary left and right contexts and its delimiter recurs between every pair
of simulated rewrites. Keeping three rule letters leaves no copy channel; keeping the copy
letters leaves one oriented rewrite rule, whose accessibility problem is decidable by a
length-bounded search. This diagnoses the tax but does not prove that every possible compiler
pays it.

## Unary Exception

The mixed-body hypotheses are substantive. When `q=c^m`, a local three-letter exact
factorization exists. It is not a reduction: the malformed word `t^(β+1)c^β` is an unconditional
false fixed-boundary witness. The exception is therefore noted, not promoted as a mechanism.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Paired Neary role counts form a nonsingular four-channel system | promotion | Lean theorem `nearyPairedParikh_det_ne_zero` |
| Erasing exact role macros require at least four physical letters | promotion | Lean theorem `ExactErasingMacroFactorization.four_le_card` |
| The two stationary residual variables have only the displayed integral cases | promotion | Lean theorems `commonLowerDeletion_cases`, `upperResidualShift_cases` |
| No stationary closed-return ternary block encoder exists for mixed bodies | audited, not fully formalized | reconstructed kernel and word-cancellation proof |
| Every finite-delay or overlapping ternary encoder is excluded | rejected | state-dependent and open-residual encoders lie outside the hypotheses |
| Nicolas's recurrent copy alphabet can be absorbed into boundaries | rejected | every derivation certificate uses it internally |
| `M₃(4)` follows | rejected | no surviving ternary source or three-state same-zero compiler is supplied |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: erasing fixed macros; empty or nonuniquely decoded role words; stationary overlap that
         closes to one residual after every complete Neary block; literal boundary absorption of
         Nicolas's recurrent copy alphabet.
REMAINS: state-dependent or nonfactorial ternary spelling, an open block residual,
         solvability-only target recoding, the paired same-zero lane, square-root punctuation,
         and positive free cancellation.
DISTANCE: no local fixed-role refinement remains. The next source attack must carry real history.
```

## Artifact

[`TernaryClosedBlockNoGo.lean`](MatrixMortality/TernaryClosedBlockNoGo.lean)

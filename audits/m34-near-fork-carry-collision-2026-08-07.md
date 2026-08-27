# Near-Fork Carry-Collision Audit

Date: 2026-08-07

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a76a50f-5974-83ea-b8aa-a950009dad6f)

## Verdict

The report does not meet a hard acceptance outcome. It supplies neither a three-state `bcbc`
recognizer nor an unconditional dimension-four lower bound. Its conditional collision is correct,
and local reconstruction strengthens its parametric example: the proposed phase-line controls
identify one terminal control with one nonterminal control as full matrices for every rational
parameter away from the denominator pole. No row or column can repair this false zero.

This closes the one-projective-coordinate stroke-carry family, including rational contraction and
singular reset behavior outside the integral expanding normalization of `G3-O04`. It does not
exclude genuinely two-dimensional singular dynamics.

## Terminal and Near-Fork Controls

Write `R_a,E_a` for rule and erasure roles. The fixed terminal prefix and the malformed near-fork
are

```text
P = R_c E_b E_c R_b E_c E_b,
Q = R_b E_c E_b R_c E_c E_b.
```

Their canonical controls are

```text
p = c t b c b t c b t,
q = b t c b c t c b t.
```

Lean checks both decodings. The fixed prefix is `bcbcTerminalFork []`, so its paired coefficient
vanishes. The upper spelling of `Q` begins with `10`, while its lower spelling begins with `11`;
Lean decides the complete word inequality and proves

```text
pairedCoefficient(3,bcbc,p)=0,
pairedCoefficient(3,bcbc,q)≠0.
```

Thus equality of the two reached states is an all-control soundness failure, not merely a defect
on an auxiliary stroke alphabet.

## Local Collision Law

Let `B,C,T` be arbitrary common controls over any semiring and in any finite dimension. In stroke
notation put

```text
D = B T C B,       Z = C T B B,
F = C T B C,       X = B T B B.
```

For a column `γ` and a recovery witness `v`, assume only

```text
(B B)v = (C B T)γ,
(D Z)v = (F X)v.
```

Expanding the two physical controls gives

```text
qγ = B T C B C T C B T γ
   = D (C T) (C B T γ)
   = D Z v,

pγ = C T B C B T C B T γ
   = F (B T) (C B T γ)
   = F X v.
```

Hence `qγ=pγ`. `bcbcNearFork_state_eq_of_local_fork` formalizes this without subtraction,
global cancellation, invertibility, or dimension three. Combining the state equality with the
checked terminal/nonterminal pair proves `no_bcbc_sameZero_of_local_fork`: no rational same-zero
representation in any dimension can satisfy both local identities.

This is the exact bridge missing from an unconditional lower bound. The fork zeros alone make the
complete binary blocks preserve a subspace of dimension at most two; they do not force either
local identity through the partial factors.

## Parametric Phase-Line Family

For `ρ∈ℚ`, set

```text
a = 2/(ρ+1),       σ = ρ(ρ+1)²/4,

B = [[1, 0, 0],       C = [[1, ρ+1, −σ],      T = [[1,0,0],
     [0, a, σ],            [0,   a,  σ],           [0,0,1],
     [0, 0, 0]],           [0,   0,  0]],          [0,1,0]].
```

The report derives their projective affine stroke maps. Reconstruction instead multiplies the
physical matrices. For every `ρ≠−1`, the three relevant stroke products have normal forms

```text
D = [[1, 2, ρ(ρ+1)³/4],
     [0, ρ, ρ²(ρ+1)³/8],
     [0, 0, 0]],

F = [[1, 1, −ρ(ρ+1)²(ρ²+ρ+2)/8],
     [0, ρ, ρ²(ρ+1)³/8],
     [0, 0, 0]],

G = [[1, 2−ρ, ρ(ρ+1)³(2−ρ)/8],
     [0,   ρ, ρ²(ρ+1)³/8],
     [0,   0, 0]].
```

Exact polynomial multiplication gives

```text
D G = F D.
```

The terminal and near-fork control products are respectively `FDT` and `DGT`. Therefore Lean
proves their equality as full matrices, strengthening the report's equality of projective affine
maps. `no_phaseLine_bcbc_sameZero` then excludes every row and column for the entire parametric
family; all intended parameters `ρ≥3` are covered.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `P` is terminal and `Q` is nonterminal | promotion | Lean theorem `bcbc_terminal_nearFork` |
| Local recovery plus `DZ=FX` forces the near-fork state to equal the terminal state | promotion | Lean theorem `bcbcNearFork_state_eq_of_local_fork` |
| No same-zero representation can satisfy those local identities | promotion | Lean theorem `no_bcbc_sameZero_of_local_fork` |
| The displayed phase-line family collides projectively for every `ρ≥3` | promotion, strengthened | Lean proves equality of the full physical products for every `ρ≠−1` |
| The phase-line family recognizes the `bcbc` language | rejected | Lean theorem `no_phaseLine_bcbc_sameZero` |
| The complete terminal grammar is `FD(B(DC)*F)*` | not promoted | no complete dead-residual invariant was supplied or needed for the collision |
| Every rational three-state recognizer forces the local collision hypotheses | open | fork invariance alone does not control the partial-factor images |
| `bcbc` has zero-language dimension at least four | open | no unconditional common-shift implication was proved |
| `M₃(4)` follows | rejected | the source-uniform recognizer or unconditional lower bound remains absent |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: the parametric two-phase, one-projective-coordinate stroke carry; more generally, every
         compiler in which the fork identity and two-step erase recovery hold on one witness.
REMAINS: construct genuinely two-dimensional singular common-shift dynamics for bcbc, or derive
         the local collision or another false zero from the complete all-context zero law.
DISTANCE: the first internal near-fork collision is exact and physical, but arbitrary singular
          partial factors can still separate the two fork paths before their common return.
```

# `bcbc` Singular-Recognizer Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a77959f-6604-83ea-8d37-5492f2b146d0)

## Verdict

The report does not prove `M₃(4)`, but it defeats `bcbc` as a lower-bound instance. Its exact
terminal grammar is correct, and its displayed singular matrices recognize that fixed regular
language on the complete paired-control free monoid. The construction is intrinsically
two-coordinate: the integer carry can agree at an internal fork while the transient guard still
separates the paths.

Lean now proves the complete null and terminal grammars, the report's missing residual invariant,
the affine state recurrence on every raw control word, every canonical terminal zero, both data
determinants, and the toggle determinant. The exhaustive reverse-carry converse remains an audited
finite certificate rather than a kernel-checked theorem. Accordingly, the fixed-instance
zero-language dimension bound is strategically accepted but is not listed as a formal theorem.

## Residual Reconstruction

Put

```text
X=BBB,    D=BCB,    Z=CBB,    F=CBC.
```

For a stroke history `h`, write `A(h)` for its consumed word and `P(h)` for its produced word.
The null equation is

```text
A(h)b = bP(h).
```

After maximal common-prefix cancellation, use three live residuals

```text
Q₀=(ε,b),    Q₁=(b,ε),    Q₂=(bcb,ε).
```

The report's indispensable invariant is:

> Every reachable nonempty right residual is exactly `b`.

The first draft attempted to orient this as a recursion on the first stroke. That statement is
false: an arbitrary tail may compensate a nonlive forward residual. The checked proof instead
defines canonical residual paths and classifies entrances to the three live states:

```text
Q₀ --X--> Q₁,    Q₁ --D--> Q₂,
Q₂ --Z--> Q₁,    Q₁ --F--> Q₀.
```

Backward decomposition therefore gives

```text
null histories      = (X(DZ)*F)*,
terminal histories  = FD(X(DZ)*F)*.
```

`BranchingRecognizer.bcbcNull_iff` and
`BranchingRecognizer.bcbc_terminal_match_iff` prove these statements for arbitrary stroke and
role words, not merely for the previously known binary fork.

## Singular Affine System

With textual products `H_{a₁…aₙ}=H_{a₁}···H_{aₙ}`, take

```text
λ=(1,0,0),        γ=(1,2983,1)ᵀ,

B=[[0,1,1/2],                 C=[[0,1/6125,-29503/6125],
   [0,5,385],                    [0,7,534],
   [0,0,1]],                     [0,0,1]],

T=[[1,0,0],
   [0,-1,2983],
   [0,0,1]].
```

From `δ=(1,0,1)ᵀ`, every raw control word reaches

```text
H_wδ=(X(w),Y(w),1)ᵀ,
```

where `Y(w)` is integral and

```text
Y(bv)=5Y(v)+385,       X(bv)=Y(v)+1/2,
Y(cv)=7Y(v)+534,       X(cv)=(Y(v)-29503)/6125,
Y(tv)=2983-Y(v),       X(tv)=X(v).
```

Lean proves this recurrence in `recognizerProduct_mulVec_delta` and proves

```text
λH_wγ = X(wt)
```

in `recognizerCoefficient_eq_guard`. Both data matrices are singular and the toggle has
determinant `-1`.

For the canonical stroke macros `h t u v`, the carry actions are

```text
x: y↦-125y+3750,      d: y↦-175y-845,
z: y↦-175y+5245,      f: y↦-245y+30.
```

The checked trajectory `0 --f→ 30 --(zd)*→ 30 --x→ 0` proves that every canonical terminal
control is a matrix zero. The decoder independently proves that these controls are precisely the
role words supplied by the formal terminal grammar.

## Reverse Certificate

For a `tt`-reduced word, reverse stripping from a target carry `z` uses

```text
b: (z-385)/5,    c: (z-534)/7,    t: 2983-z,
```

with the data predecessors admitted only when integral and with no second `t` after a `t` edge.
Independent exact search terminated on 22 states from target `0` and 44 states from target
`29503`. The live paths are exactly

```text
Y(v)=0      ⇔ red(v) ∈ (btbb (btcb ctbb)* ctbc)*,
Y(v)=29503  ⇔ red(v) ∈ tbcbtcb (btbb (btcb ctbb)* ctbc)*.
```

The dead exits admit the descending rank certificate reproduced in the external report. Exact
enumeration of all 797,161 controls of length at most twelve found sixteen semantic zeros,
sixteen matrix zeros, and no mismatch. These computations check transcription; the finite reverse
argument, not the bounded enumeration, supports the audited all-word converse.

## Uniformity Boundary

This fixed system recognizes one regular language. Its persistent state is one expanding affine
carry plus a transient singular guard. A source-uniform version with computably supplied finite
targets would lie inside the class excluded by `G3-O04`; fitting new constants to each body does
not yield a reduction.

The result therefore retires `bcbc` as a lower-bound target and vindicates genuinely
two-coordinate singular dynamics at one fixed instance. It does not supply the total formulas

```text
(β,body) ↦ λ,γ,H_b,H_c,H_t
```

required for the universal paired source.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Null histories are `(X(DZ)*F)*` | promotion | Lean theorem `BranchingRecognizer.bcbcNull_iff` |
| Terminal histories are `FD(X(DZ)*F)*` | promotion | Lean theorem `BranchingRecognizer.bcbc_terminal_match_iff` |
| The displayed matrices obey the affine recurrence on every control | promotion | Lean theorem `BranchingRecognizer.recognizerProduct_mulVec_delta` |
| Every canonical terminal control is a matrix zero | promotion | Lean theorem `BranchingRecognizer.recognizerCoefficient_terminalControl` |
| The matrices have exactly the paired zeros on every raw control | audited, not formalized | finite reverse certificate; exhaustive bounded cross-check |
| `zdim_ℚ(L₃,bcbc)≤3` | audited, not formalized | all-word converse plus the displayed rational matrices |
| A source-uniform three-state compiler follows | rejected | constants encode this one regular instance |
| `M₃(4)` follows | rejected | no uniform undecidable family is compiled |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: bcbc as a rational same-zero lower-bound instance; the claim that branching alone forces
         four states; another fixed-instance search with freely fitted affine constants.
REMAINS: a source-uniform singular same-zero compiler, square-root punctuation fusion, a genuinely
         state-dependent ternary GPCP code, or a positive spelling-sensitive cancellation engine.
DISTANCE: the fixed branching fork is now understood. Uniformity, not local state dimension, is
          the paired route's live obstruction.
```

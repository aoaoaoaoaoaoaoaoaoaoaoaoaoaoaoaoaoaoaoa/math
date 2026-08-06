# History-Fracture Audit

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a74ec2f-4e30-83ea-88bb-fdbb4d9a3924)

## Enemy Lock

```text
MASTER: prove M₃(4) undecidable.
VICTORY: a computable four-generator 3 × 3 mortality reduction with an arbitrary-word converse.
LIVE OBSTRUCTION: uniformly compile the paired zero language into three states without embedding
                  a halting witness in the emitted matrices, or exclude a delimited uniform class.
KILLED LANES: exact-series minimization; nonerasing three-letter role macros; rational phase-state
              maps; universal terminal-word uniqueness; generic single-valuedness of every
              history-sensitive phase graph.
```

## Verdict

The report's principal theorem is false. Determinism of `TagStep` gives at most one lawful
execution, but the global terminal equation can encode additional strokes after the execution
has already reached a short queue. `tagHaltsFrom_of_history` states this boundary explicitly: it
may stop at an earlier short queue without consuming the rest of the supplied history.

The report nevertheless contains two results that change the master frontier.

1. On the infinite subclass `body.length = β−1`, the terminal role word really is unique. The
   proposed base-five matrices then give an exact history-sensitive three-state same-zero
   representation on the complete paired-control free monoid.
2. The explicit phase-graph calculation is correct on that subclass. Each phase graph closure is
   the product of the checked source plane with a target line. Generic single-valuedness is
   therefore false; uniform computability, not instancewise geometry, is the surviving boundary.

The first result and its integral mortality lift are Lean-checked. The graph-closure calculation
is independently audited below and remains outside the kernel.

## Rejected Uniqueness Claim

Set `β=3` and

```text
body = [b,c,b,b].
```

The following distinct role words both satisfy the terminal equation:

```text
short = R_c E_b E_c  R_b E_b E_b

long  = R_c E_b E_c  R_b E_b E_b  R_b E_b E_b  R_c E_b E_b.
```

The first two strokes are the canonical terminating execution. The last two strokes of `long`
are not executed. They satisfy the residual history equation

```text
consumed(null) ++ [b] = [b] ++ produced(null)
```

for heads `b,c` and wakes `bb,bb`. The global word equality therefore accepts the extension even
though the queue was already shorter than the deletion width.

`NullHistoryCounterexample.terminal_word_not_unique` checks both complete binary word equations
and the inequality of their witnesses by reduction in Lean. This refutes the report's claimed
“nonuniform collapse theorem” for arbitrary admissible paired instances.

## Minimal-Body Uniqueness

Assume

```text
1 < β,    body.length = β−1.
```

Pulse normalization turns any terminal role word into `tileHistory (first :: history)`. The
semantic terminal equation forces

```text
first.head = c,
first.wake = body,
consumed(history) ++ [b] = [b] ++ produced(tagOutput body, history).
```

If `history` were nonempty, its first head would be `b` by comparing the first symbols. That
stroke consumes `β` symbols and produces one. Every later stroke produces at most `β` symbols.
For `history = stroke :: later`, comparison of lengths would give

```text
β(1 + later.length) + 1
  ≤ 2 + β later.length,
```

contradicting `1 < β`. Thus `history=[]`, and the unique terminal word is

```text
ω(body) = R_c :: body.map E.
```

For `2<β`, this word exists: the initial queue is `[b]` and is already short. Lean checks
uniqueness, existence, and the exact terminal equation as

```text
minimalBody_terminal_word_unique
minimalBody_terminal_match.
```

## Base-Five Encoder

Assign digits

```text
δ(R_b)=1,  δ(R_c)=2,  δ(E_b)=3,  δ(E_c)=4
```

and define the least-significant-first code

```text
κ(r :: w) = δ(r) + 5κ(w).
```

The nonzero digits remove the trailing-zero ambiguity of positional notation. Lean proves
`historyCode_injective` through `Nat.digits_ofDigits`.

For paired controls `b,c,t`, put

```text
H_b = [[5,-1,2], [0,0,-1], [0,0,1]]
H_c = [[5,-1,3], [0,0,-1], [0,0,1]]
H_t = [[1, 0,0], [0,-1, 0], [0,0,1]]
γ   = (0,1,1)ᵀ.
```

Writing `σ(rule)=1` and `σ(erase)=−1`, Lean checks for every arbitrary control word `y`

```text
H_y γ = (κ(decodePairedWord y), σ(suffixPhase y), 1)ᵀ.
```

No intended-word condition occurs. For a prescribed role word `ω`, the row

```text
λ_ω = (1,0,−κ(ω))
```

therefore emits

```text
λ_ω H_y γ = κ(decodePairedWord y) − κ(ω),
```

which vanishes exactly when `decodePairedWord y=ω`.

Combining this invariant with minimal-body uniqueness gives the complete free-monoid identity

```text
historyCoefficient κ(ω(body)) y = 0
  ↔ pairedCoefficient β body y = 0.
```

This is `minimalBody_history_zero_iff_paired_zero`.

## Integral Mortality Lift

Let

```text
A_K = γ(1,0,−K)
    = [[0,0,  0],
       [1,0,−K],
       [1,0,−K]].
```

The physical family consists of `A_K,H_b,H_c,H_t`. The data controls have common eigenvector
`e₁` with eigenvalue `5`; the toggle fixes `e₁`. Scaling each data control by `1/5` makes `e₁`
pointwise fixed. Independent nonzero generator scaling preserves mortality, so the existing
fixed-anchor rank-one compiler applies. Casting between integral and rational matrices is exact.

Lean consequently proves

```text
IsMortal {A_K,H_b,H_c,H_t}
  ↔ ∃ y, λ_K H_y γ = 0.
```

The declarations are `historyMortalityFamily_rat_mortal_iff_zero` and
`historyMortalityFamily_int_mortal_iff_zero`. The latter covers every number and placement of
separators, control-only products, adjacent separators, toggle-only blocks, and malformed control
words.

For `β=3`, `body=[b,b]`,

```text
ω = R_c E_b E_b,
κ(ω) = 92,
y = c t b b t.
```

Lean checks `decodePairedWord y=ω`, both scalar zeros, and mortality of the four integral matrices
with `K=92` in namespace `MinimalBodyExample`.

## Phase-Graph Audit

The target suffix points lie on the phase lines

```text
ℓ_E : S+W=0,    ℓ_R : S−W=0
```

in target `P²`. Consider erase-phase words `b^m c^(n+1)`. Their decoded roles are

```text
E_b^m E_c^n R_c.
```

In the checked source chart `(t,r)`, write

```text
q=3^(β+1),  a=3q,  t*=d/(a−1),
R_c(t₀,r₀)=(τ,η),  τ≠0, η≠0.
```

The source point and target code are

```text
r_mn = η q^(−m),
t_mn = t* + a^(−m)(τ3^(−n)−t*),
z_mn = 3·5^(m+n) − 5^m/4 − 3/4.
```

Multiplicative independence of `3` and `5` makes

```text
{(3^(−m),3^(−n),5^m,5^n) : m,n≥0}
```

Zariski dense in `G_m⁴`. With variables `X,Y,U,V`, the map to `(r,t,z)` has Jacobian minor

```text
3ητ(β+1) U X^(2β+2),
```

which is nonzero. Its image is therefore dense in `A³`. Hence the erase graph closure is
`P² × ℓ_E`; prefixing a toggle gives `P² × ℓ_R`. Both projections have one-dimensional generic
fibers. The positivity calculation

```text
1 + 2v − 3ρ = 9·3^N + 18w + 15 > 0
```

supplies `τ≠0`; all multiplication orders agree with `suffixDecode`.

This calculation validates the report's geometric counterexample on every nonempty minimal body.
It is not needed by the Lean same-zero theorem and remains classified as `audited`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every admissible mortal instance has one terminal role word | rejected | Lean counterexample |
| Every fixed paired zero language has zero-language dimension at most three | rejected | depends on false uniqueness |
| Minimum-length bodies have one terminal role word | promotion | Lean theorem |
| Base-five matrices encode the total paired decoder | promotion | Lean theorem |
| Exact same-zero representation on minimum-length bodies | promotion | Lean theorem |
| Four-generator integral mortality lift | promotion | Lean theorem |
| Explicit `β=3`, body `bb`, `K=92`, witness `ctbbt` | promotion | Lean theorem |
| Phase graph closures are full products on that subclass | promotion | independent audit |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: universal terminal-word uniqueness; every attempt to prove all three-state phase graphs
         generically single-valued; instancewise geometric exclusion of history-sensitive states.
REMAINS: a total computable choice of three-state matrices from the unrestricted source instance,
         without a parameter encoding a terminal witness; or a no-go for an explicitly delimited
         uniform compiler class that forces a different M₃(4) architecture.
DISTANCE: replace the nonuniform oracle K=κ(ω) by source-computable algebra that recognizes all
          terminal histories, then compose the checked rank-one lift; or prove that replacement
          impossible under hypotheses strong enough to redirect the master attack.
```

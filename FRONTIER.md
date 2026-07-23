# Completing the Matrix Mortality Table

**Author:** GPT-5.6 Sol

**Elicited by:** [@eternalism_4eva](https://x.com/eternalism_4eva)
**Status date:** 2026-07-22

This memorandum records the state of the bounded matrix-mortality campaign
after the proposed results `M₃(5)` and `M₄(4)`. It consolidates the positive
constructions, the supporting obstruction theorems, the remaining cells, and
the research program.

The status labels are deliberately severe:

- **checked** means present in the Lean development and covered by the
  repository verification gate;
- **external** means used from an identified published theorem but not
  formalized locally;
- **provisional theorem** means a complete mathematical argument is in hand
  but has not passed the local formalization and independent-review standard;
- **conditional obstruction** means a no-go theorem for a stated architecture,
  not for the target decision problem;
- **open** means no proof is claimed.

In particular, this document does not promote `M₄(4)` or the Hankel-rank
obstruction to the same evidentiary status as the checked `M₃(5)`
instance-level reduction.

## 1. Problem and order structure

`M_d(k)` is the following decision problem:

> Given at most `k` integer `d × d` matrices, does some nonempty product of
> them equal the zero matrix?

Two monotonicities organize the table.

1. Increasing the generator allowance preserves undecidability.
2. Increasing dimension by `A ↦ A ⊕ 0` preserves mortality and therefore
   undecidability.

Every undecidability result consequently fills the northeast quadrant above
its cell. Every decidability result fills the southwest quadrant below its
cell. The table is an order ideal of decidable cells and an order filter of
undecidable cells, separated by an unknown band.

The trivial boundaries are:

- `M₁(k)` is decidable for every `k`;
- `M_d(1)` is decidable for every `d`;
- `M₂(2)` is decidable.

The last item is nontrivial; see [BB02](references/bournez-branicky-2002-low-dimensional-mortality.md).

## 2. Present table

Assuming the checked source-to-matrix theorem behind `M₃(5)` and the
provisional `M₄(4)` theorem, the table is:

| `d ↓`, `k →` | `2` | `3` | `4` | `≥5` |
| ---: | :---: | :---: | :---: | :---: |
| `2` | D | ? | ? | ? |
| `3` | ? | ? | ? | U★ |
| `4–5` | ? | ? | U† | U |
| `6–11` | ? | U★ | U | U |
| `≥12` | U★ | U | U | U |

Here:

- `U★` is new from `M₃(5)` and the CHHN generator–dimension trade;
- `U†` depends on the provisional `M₄(4)` proof;
- unmarked `U` follows by padding or was already known;
- `?` means not resolved by any valid result found in the present literature
  audit, not that no unpublished proof exists.

The previous accepted minimal mortality-undecidability antichain was

```text
M₃(6), M₅(4), M₉(3), M₁₅(2).
```

`M₃(5)` changes it to

```text
M₃(5), M₅(4), M₆(3), M₁₂(2).
```

If `M₄(4)` survives hardening, the antichain becomes

```text
M₃(5), M₄(4), M₆(3), M₁₂(2).
```

The old table, the reduction `Z_d(k) → M_d(k+1)`, and the trade

```text
M_d(hk+1) → M_kd(h+1)
```

are due to [CHHN14](references/cassaigne-halava-harju-nicolas-2014-matrix-mortality.md).

There are then thirteen unknown cells with `d ≥ 3`:

```text
k = 4:  M₃(4)
k = 3:  M₃(3), M₄(3), M₅(3)
k = 2:  M₃(2), M₄(2), …, M₁₁(2).
```

The entire row `M₂(k)` for `k ≥ 3` also remains unknown.

### 2.1 The two minimal unknown kernels

Despite the visible width of the unknown band, it has only two
coordinatewise-minimal cells:

```text
M₃(2)        and        M₂(3).
```

Every unknown cell with `d ≥ 3` lies northeast of `M₃(2)`. Every unresolved
two-dimensional cell lies northeast of `M₂(3)`.

Therefore:

- if `M₃(2)` is undecidable, every `M_d(k)` with `d ≥ 3` and `k ≥ 2`
  is undecidable;
- if `M₂(3)` is undecidable, every `M₂(k)` with `k ≥ 3` is undecidable;
- the CHHN trade additionally sends `M₂(3)` to `M₄(2)`;
- if both are undecidable, the complete table follows immediately.

The converse is asymmetric. Decidability of a minimal cell does not imply
decidability above it. If either kernel is decidable, completion requires
locating the first undecidable threshold farther northeast.

This is the principal strategic division:

- the current work improves the northeast undecidability staircase;
- completing the table may require southwest decidability theorems.

## 3. First result: fixed-boundary source compression

### 3.1 What is proved

The checked source theorem is:

> Binary-target `GPCP(4)` is undecidable, even with empty left boundaries, one
> empty right boundary, and nonempty morphism images.

For Neary's four ordinary roles, it takes the form

```text
∃w ∈ {R_c,R_b,D_c,D_b}*: U(w)10^β = V(w).
```

The proof does not depend on Neary's defective fifth pair or on Rote's longer
unary terminal guard. It proves the fixed-boundary equation directly.

The soundness direction accepts an arbitrary role word:

1. a zero-run automaton forces exact blocks containing one rule role and
   `β−1` deletion roles;
2. those blocks decode to width-`β` tag-system strokes;
3. the global word equality becomes a queue-history certificate;
4. prefix cancellation reconstructs lawful tag steps;
5. the history proof stops at the first short queue and does not interpret
   post-halting junk.

This replaces the unsafe claim that every wrong local choice quickly
mismatches with an exhaustive global synchronization theorem.

`GPCP(4)` was explicitly listed as open by
[Nicolas08](references/nicolas-2008-gpcp-semi-thue.md) and
[CHHN14](references/cassaigne-halava-harju-nicolas-2014-matrix-mortality.md).
The historical priority qualifications are recorded in [NOVELTY.md](NOVELTY.md).

### 3.2 Fixed-boundary mortality compiler

Let `X_i` be the four nonsingular `3 × 3` word-pair matrices, let `X_*`
encode the fixed right boundary, and put

```text
c = X_* e₃,
S = c e₁ᵀ.
```

Then

```text
S X_w S = c (e₁ᵀ X_w X_* e₃) e₁ᵀ.
```

The scalar in parentheses is zero exactly when the fixed-boundary word
equation holds.

An arbitrary product containing occurrences of `S` fractures uniquely as

```text
P₀ S P₁ S ··· S P_t,
```

where the `P_i` are products of ordinary matrices. Expansion gives

```text
(P₀c)
  [∏_{1≤i<t} e₁ᵀP_i c]
(e₁ᵀP_t).
```

The exterior vectors are nonzero because every `P_i` is nonsingular. Thus:

- no-separator products are nonsingular;
- one-separator products are nonzero outer products;
- a product with at least two separators is zero exactly when an internal
  fixed-boundary scalar is zero.

This yields `M₃(5)`. The broad rank-one absorption method is prior art in
[HHH07](references/halava-harju-hirvensalo-2007-claus-instances.md) and
[CHHN14](references/cassaigne-halava-harju-nicolas-2014-matrix-mortality.md).
The new part is the rigorously proved four-role fixed-boundary source.

### 3.3 Immediate consequences

CHHN propagation gives:

```text
M₃(5) → M₆(3)       using 5 = 2·2+1,
M₃(5) → M₁₂(2)      using 5 = 1·4+1.
```

The corresponding scalar and right-corner antichains are provisionally:

```text
Z:  Z₃(4), Z₅(3), Z₇(2)
R:  R₃(5), R₄(4), R₆(3), R₈(2).
```

These are external CHHN corollaries, not yet part of the Lean development.

## 4. Second result: semantic-agreement compression

`M₄(4)` arose while attacking `M₅(3)`. Its current status is **provisional
theorem**: the algebraic proof has survived adversarial review but has not yet
been formalized or independently rebuilt from a publication artifact.

### 4.1 Side-normal form

Conjugating the standard word-pair matrix gives

```text
           [ 1  σ(v)  σ(u) ]
Φ(u,v)  =  [ 0  3^|v|   0  ].
           [ 0    0   3^|u|]
```

The upper and lower word channels are now separate.

Neary's roles occur in two pairs:

```text
(R_b,D_b)        and        (R_c,D_c).
```

Within each pair the upper word is identical. On

```text
E_U^Φ = span{e₁,e₃}
```

the matrix `Φ(u,v)` depends only on `u`. Hence

```text
R_b|E_U^Φ = D_b|E_U^Φ,
R_c|E_U^Φ = D_c|E_U^Φ.
```

This two-dimensional equality of actions is the state resource that generic
packing ignores.

### 4.2 Paired-role compression theorem

Let `R₀,R₁,D₀,D₁` act on a `d`-dimensional space `V`, and suppose

```text
R_i|E = D_i|E
```

on an `r`-dimensional subspace `E`. On `V ⊕ V`, define two data controls and
a toggle:

```text
Ĝ_i = [ 0  0 ]       T̂ = [ 0  I ].
      [ R_i D_i ]            [ I  0 ]
```

The anti-diagonal agreement space

```text
K = {(p,−p) : p∈E}
```

is invariant: every `Ĝ_i` annihilates it and `T̂` acts on it by `−1`.
Therefore the controls descend to

```text
W = (V⊕V)/K,
dim W = 2d−r.
```

For `d=3` and `r=2`, the dimension is four.

The quotient is not sufficient by itself. Its decisive property is a total
right-to-left decoder:

- the toggle changes the current phase;
- data control `i` emits `R_i` in phase zero and `D_i` in phase one;
- after emitting a role, the phase is reset as prescribed.

Every arbitrary control word is assigned a legitimate four-role word. The
decoder is also surjective: every four-role word has an explicit control
encoding. No malformed-control language remains to audit.

### 4.3 Explicit scalar system

In integral quotient coordinates, the two data matrices have the form

```text
      [ 1  V_x^R  U_x  V_x^D ]
G_x = [ 0    0     0     0   ]
      [ 0    0    A_x    0   ]
      [ 0  B_x^R   0   B_x^D ]
```

for `x∈{b,c}`, and the toggle is

```text
    [ 1 0 0 0 ]
T = [ 0 0 0 1 ].
    [ 0 0 1 0 ]
    [ 0 1 0 0 ]
```

The boundary vectors are

```text
L = [1 0 0 0],
C = [μ −1 t 0]ᵀ.
```

All three matrices fix `e₁`, and `LC=μ≠0`. For every control word `z`,

```text
L G_z C = e₁ᵀ X_{τ(z)} d₃.
```

Surjectivity of `τ` gives scalar-zero equivalence with the four-role terminal
equation. Toggle-only words have coefficient `μ`, so the nonempty-word
convention introduces no false witness.

This proves, subject to hardening,

```text
structured Z₄(3) is undecidable.
```

### 4.4 Scalar reachability to mortality

Put

```text
P = C L.
```

The four candidate mortality generators are

```text
G_b, G_c, T, P.
```

The three controls are singular, so the `M₃(5)` converse cannot use
nonsingularity. Their common fixed column replaces it.

Every product containing copies of `P` has a unique expansion

```text
Q₀ P Q₁ P ··· P Q_m
  =
(Q₀C)
  [∏_{1≤i<m} LQ_iC]
(LQ_m).
```

The terminal row is nonzero because

```text
(LQ_m)e₁ = Le₁ = 1.
```

If `Q₀C=0`, then `LQ₀C=0` is already a scalar-zero witness. Otherwise the
exterior outer product is nonzero, and a zero product requires an internal
scalar-zero block. Empty internal blocks contribute `LC=μ≠0`.

This is the provisional proof of

```text
M₄(4) is undecidable.
```

The generic paired-role theorem must state its nonempty-witness side
condition explicitly. The Neary specialization satisfies it through
`LC=μ≠0`.

### 4.5 Frontier consequences

If the theorem is confirmed:

```text
Z:  Z₃(4), Z₄(3), Z₇(2)
R:  R₃(5), R₄(4), R₅(3), R₈(2)
M:  M₃(5), M₄(4), M₆(3), M₁₂(2).
```

`M₄(4)` replaces the old `M₅(4)` anchor. Its generic CHHN trade reaches
`M₁₂(2)`, already known from `M₃(5)`.

## 5. Supporting obstruction: exact six-state packing

The first attack on `M₅(3)` specialized the CHHN trade

```text
M₃(5) → M₆(3).
```

It asked whether the resulting six-state representation could lose one state.
The answer is negative for exact reproduction of its natural coefficient
series.

This is a **provisional theorem**. The symbolic argument is complete but has
not yet been formalized locally.

### 5.1 Packed representation

Place the rank-one separator `S` and four ordinary matrices in any order

```text
(G₀,G₁,G₂,G₃,G₄).
```

Define three `6 × 6` controls:

```text
    [ 0 G₀ ]          [ G₁ G₂ ]          [ G₃ G₄ ]
V = [ I  0 ],    B₁ = [  0  0 ],    B₂ = [  0  0 ].
```

With

```text
ℓᵀ = (e₁ᵀ,0),
ĉ  = (c,0)ᵀ,
```

define the rational coefficient series

```text
F(w) = ℓᵀ T_w ĉ
```

over the alphabet `{v,b₁,b₂}`.

For prefixes `p_i` and suffixes `q_j`, the Hankel minor factors as

```text
H_ij = F(p_iq_j),
H = O R,
```

where the rows of `O` are `ℓᵀT_{p_i}` and the columns of `R` are
`T_{q_j}ĉ`.

### 5.2 All-placement rank theorem

For every admissible Neary body and every one of the `5! = 120` labelled
placements:

- six explicit observable rows have nonzero determinant;
- six explicit reachable columns have nonzero determinant;
- consequently a `6 × 6` Hankel minor is nonzero;
- the series has Hankel rank exactly six.

The proof partitions placements into three cases:

1. `S` occupies the wrap slot `G₀`;
2. `S` occupies the first slot of a payload pair;
3. `S` occupies the second slot of a payload pair.

The determinant certificates reduce to four families of `3 × 3` minors:

- `Δ₂(i,j)`, measuring projective independence of ordinary first rows;
- `Δ₃(i,j,k)`, measuring independence of three ordinary first rows;
- `Θ(i,j)`, involving a composite row `a_jX_i`;
- `Λ(i,j)=det(c,X_ic,X_jc)`, measuring boundary-column reachability.

Every required `Δ₂`, `Δ₃`, and `Θ` is excluded by explicit sign formulas.
The two difficult `Λ` factors are excluded by congruences modulo `18` and
`162`.

For the canonical placement

```text
G₀=S, G₁=X_Rc, G₂=X_Rb, G₃=X_Dc, G₄=X_Db,
```

one may take

```text
prefixes:  ε, v, b₁, b₂, b₁v, b₂v
suffixes:  ε, v, b₁, b₂, vb₁, vb₂.
```

The resulting determinant is

```text
μ (24h)² [t²(z−3)/3]²,
```

which is nonzero.

### 5.3 Exact scope

The theorem proves:

> No rational linear representation of this particular coefficient series
> has dimension at most five.

It is stronger than the earlier invariant-line and invariant-hyperplane
obstructions. It excludes every exact five-state realization, including one
unrelated to the CHHN matrices by restriction, quotient, or similarity.

It does **not** prove:

- that `M₅(3)` is decidable;
- that no five-state series has the same zero set as `F`;
- that no different word code realizes the mortality language;
- that six states are intrinsic to every compiler using the same source.

The distinction between value preservation and zero-set preservation is
load-bearing. Hankel rank controls the former only.

## 6. Supporting obstruction: one-sided phase overlap

The obvious escape from exact six-state minimization is a value-changing
phase fusion. The simplest such fusion glues two three-dimensional phase
spaces along one line and tries to turn a control word into rank-one
punctuation.

The following result is an algebraic theorem about that architecture. Its
extension to a global mortality no-go is **conditional** on an explicit
bridge-normal-form hypothesis.

### 6.1 Side-plane lemma

Let `q=(x,y,z)ᵀ`. For an ordinary word-pair matrix `X_i`,

```text
(X_iq)₂ / (X_iq)₃
  =
1 + [(y−z)/z] 3^(n_i−m_i)
```

whenever `z(y−z)≠0`.

The four Neary roles have pairwise distinct length defects `n_i−m_i`.
Therefore no two images `X_iq` can be collinear unless

```text
z=0        or        y=z.
```

These conditions define the two invariant planes in the original `Ψ` basis:

```text
E_V^Ψ = {(x,y,0)ᵀ},
E_U^Ψ = {(x,z,z)ᵀ}.
```

On `E_V^Ψ`, the action depends only on the lower word. On `E_U^Ψ`, it
depends only on the upper word. Under the side-normal conjugacy,
`E_U^Ψ` becomes the plane `E_U^Φ=span{e₁,e₃}` used in the `M₄(4)`
construction.

Consequently, every common-line selector quotient in the exact paired-phase
architecture loses one entire side of the correspondence instance.

### 6.2 Regularity of one-sided bridges

On either side plane, a bridge coefficient has the form

```text
A σ(x) + B 3^|x| + C.
```

After clearing denominators, its zero language is effectively regular. A
right-to-left automaton stores the bounded carry

```text
k_{j+1} = (k_j + aδ_j)/3
```

whenever the numerator is divisible by three. A uniform bound on the carries
gives a finite state set.

Thus a phase-fusion compiler whose complete arbitrary-product converse
reduces to finitely many such one-sided bridges is decidable and cannot carry
the source undecidability.

### 6.3 Exact scope

This closes:

- exact common-line phase fusion;
- projective rescalings of the exact rule and deletion actions;
- rank-one punctuation whose bridges remain within the resulting one-sided
  normal form.

It does not close:

- rank-two punctuation;
- a value-changing representation not built from exact phase copies;
- a fusion with a larger or nonlinear overlap;
- an architecture in which malformed controls themselves carry nonregular
  computation.

The broad statement “rank-one punctuation cannot prove `M₅(3)`” is not
established and must not be used.

## 7. The scalar-reachability ladder

The generic reduction

```text
Z_d(k) → M_d(k+1)
```

identifies useful sufficient intermediates:

| Mortality target | Sufficient scalar target |
| --- | --- |
| `M₅(3)` | `Z₅(2)` |
| `M₄(3)` | `Z₄(2)` |
| `M₃(4)` | `Z₃(3)` |
| `M₃(3)` | `Z₃(2)` |
| `M₃(2)` | `Z₃(1)` |

The last line explains a real change of regime. `Z₃(1)` is a
single-matrix scalar-orbit problem, hence a low-order Skolem problem and
decidable. `M₃(2)` cannot become undecidable through the ordinary
payload-plus-rank-one-separator compiler. Both mortality generators must
participate intrinsically in rank descent.

The new `M₄(4)` construction supplies structured `Z₄(3)`. The generic
structured CHHN trade sends it to `Z₇(2)`, which was already obtained from
`Z₃(4)`. The meaningful special targets are therefore:

```text
Z₆(2): technique milestone only;
Z₅(2): yields M₅(3);
Z₄(2): yields M₄(3);
Z₃(2): yields M₃(3).
```

## 8. Target-by-target analysis

### 8.1 `M₅(3)`: best next positive target

Success would:

```text
M₅(3) → M₁₀(2),
```

supersede `M₅(4)` and `M₆(3)`, and reduce the mortality antichain to

```text
M₃(5), M₄(4), M₅(3), M₁₀(2).
```

There are two equivalent strategic views.

**Scalar view.** Construct `Z₅(2)`: two five-state controls and boundary
vectors whose scalar zero language is the three-control `Z₄(3)` language.

**Punctuation view.** Starting from `G_b,G_c,T,L,C`, construct three
five-state mortality generators in which a fixed control word `E` acts as
rank-two punctuation.

If `E=UV` has rank two, the desired bridge identity is

```text
V Ĝ_z U
  =
[ 0    0   ]
[ 0  L G_z C]
```

up to fixed invertible row and column changes.

Then every bridge matrix is a scalar multiple of one fixed matrix, and a
chain of punctuation factors vanishes exactly when one source scalar
vanishes. The three structural zero entries prevent nonzero `2 × 2` bridges
from multiplying spuriously to zero.

The remaining obligations are:

1. realize the identity for every control word;
2. realize `E` as a word over the same three generators;
3. prove the exterior factors cannot vanish without already yielding a scalar
   witness;
4. exclude zero products containing no complete punctuation word;
5. retain integrality after denominator clearing.

This is the narrowest serious next ansatz. Another exact minimization of the
literal six-state series is closed by the Hankel theorem.

### 8.2 `M₄(3)`: no spare-state fusion

`M₄(3)` would imply `M₈(2)` and settle both `M₄(3)` and `M₅(3)` by padding.

A sufficient target is `Z₄(2)`. Relative to the provisional `Z₄(3)`
construction, one control must disappear without any increase in dimension.
Equivalently, toggle and data selection must be encoded by two controls, or
toggle and separator must be fused in mortality directly.

The present obstruction is geometric: a rank-one map cannot simultaneously
transport the unrestricted four-dimensional scalar state and serve as a
reset. A macro-generated low-rank map is possible in principle, but its
arbitrary-word grammar must be proved globally.

This target should follow, not precede, the rank-two `M₅(3)` investigation.
The five-dimensional construction has one additional boundary direction in
which to discover the required algebra.

### 8.3 `M₃(4)`: the source-alphabet frontier

`M₃(4)` would imply `M₉(2)` and settle every four-generator cell in dimension
at least three.

The standard route requires `GPCP(3)`. `GPCP(2)` is decidable, while
`GPCP(3)` remained open in the audited literature; see
[Nicolas08](references/nicolas-2008-gpcp-semi-thue.md) and
[HH11](references/halava-holub-2011-binary-gpcp-reduction-tree.md).

The four Neary roles are semantically distinct:

```text
R_c: initialization and the c-rule,
R_b: the b-rule,
D_c: deletion of c,
D_b: deletion of b.
```

The new `M₄(4)` decoder suggests a source-level attack. Use three source
letters `{b,c,t}`, with the dangling residual carrying the suffix phase so
that every word decodes to a four-role word. A word morphism is stateless, so
the phase must be represented by synchronizing residual markers rather than
by an external automaton.

The proof must establish both:

- total decoding of every three-letter word;
- surjectivity onto every four-role word relevant to the source theorem.

A local factorization of tiles or a forced-first occurrence is insufficient:
`R_c` recurs internally.

### 8.4 `M₃(3)`: beyond bounded GPCP

`M₃(3)` would imply `M₆(2)` and dominate both three-generator improvements
above it.

The direct scalar route is `Z₃(2)`. A conventional word-pair construction
would start from two source roles, but `GPCP(2)` is decidable. Therefore a
positive result requires at least one of:

- matrices whose occurrences have several context-dependent semantic roles;
- a source other than word equality under two morphisms;
- an intrinsic mortality construction in which rank descent performs part of
  the computation;
- a zero-set representation strictly more expressive than exact word-pair
  encoding.

This is the first target at which the present PCP compiler loses its natural
source. It may be undecidable, but it is also a plausible boundary for a new
decidability theorem.

### 8.5 `M₃(2)`: lower-left higher-dimensional kernel

An undecidability proof here completes every cell with `d≥3`. A decidability
proof would establish the first nontrivial southwest boundary in dimension
three.

The problem should be stratified by ranks.

**Both generators invertible.** Mortality is impossible.

**One rank-one singular generator.** Write it as `B=crᵀ` and let `A` be the
other, invertible generator. Every internal bridge is

```text
rᵀ Aⁿ c.
```

This is a linear recurrence of order at most three. Zero occurrence is
decidable. The recent order-four theorem
[Bacik25](references/bacik-2025-order-four-skolem.md) gives additional room
for exterior-power variants.

**One rank-two singular generator.** Let `E=im B`. Products beginning and
ending in `B` induce the parameterized family

```text
T_n = B Aⁿ |E       in End(E).
```

The problem becomes mortality of the structured infinite family
`{T_n:n≥0}` of `2 × 2` matrices. Individual rank drops are governed by
low-order exponential polynomials. The unresolved part is an unbounded
sequence of rank-preserving `T_n` followed by a rank drop and a final
annihilation.

**Both generators singular.** Powers stabilize images and kernels, but
alternation can still move between rank-two and rank-one strata. This should
be reduced to a finite graph of image/kernel incidences plus parameterized
orbit problems on the surviving subspaces.

The natural machinery is:

- Fitting decomposition of each generator;
- exterior powers to detect rank drops;
- Skolem decision procedures for individual exponent families;
- projective dynamics on the image planes;
- a finite control graph recording rank strata.

This is primarily a decidability campaign. A successful undecidability
construction must explain how two three-dimensional maps evade this severe
rank geometry.

### 8.6 The pair band `M₄(2)` through `M₁₁(2)`

These should not be treated as nine independent targets.

The CHHN trade supplies the following automatic thresholds:

| Source result | Pair consequence |
| --- | --- |
| `M₂(3)` | `M₄(2)` |
| `M₃(3)` | `M₆(2)` |
| `M₄(3)` | `M₈(2)` |
| `M₃(4)` | `M₉(2)` |
| `M₅(3)` | `M₁₀(2)` |

`M₁₁(2)` is therefore an orphan only while `M₅(3)` remains open. A direct
one-state shave from `M₁₂(2)` has less structural value than the
three-generator attack that would leap past it.

Dimensions five and seven do not arise naturally from the generic trade.
If the true pair threshold lies at one of them, a specialized direct compiler
will be required.

### 8.7 `M₂(3)`: lower-left two-dimensional kernel

CHHN prove the exact equivalence

```text
M₂(k+1) ≡ Z₂(k).
```

Hence

```text
M₂(3) ≡ Z₂(2).
```

Every nonzero singular `2 × 2` matrix has rank one. The known decidability
theorem for families with at most one nonsingular generator
[Heckman19](references/heckman-2019-2x2-mortality-invertible.md) leaves one
exact hard stratum:

```text
two nonsingular matrices A,B
and one rank-one matrix S=crᵀ.
```

Rank-one fracture gives

```text
mortality
  ⇔
∃w∈{A,B}*: rᵀwc=0.
```

Projectively, this asks whether the positive semigroup generated by two
rational Möbius transformations sends `[c]` to the rational line `ker rᵀ`.

The unimodular case is decidable by regular-language methods; see
[PS19](references/potapov-semukhin-2019-vector-scalar-reachability-sl2z.md).
Membership of a fixed nonsingular target is decidable even with arbitrary
nonsingular integer determinants; see
[PS17b](references/potapov-semukhin-2017-nonsingular-2x2-membership.md).
Neither result decides intersection with the infinite incidence variety

```text
{K : rᵀKc=0}.
```

The missing arithmetic is determinant growth. Projective normalization moves
the generators from `SL₂(ℤ)` into matrix groups over larger arithmetic rings;
the virtually-free modular-group normal form no longer applies directly.

The campaign should stratify:

1. commuting generators;
2. simultaneous rational triangularizability;
3. common rational eigenlines;
4. virtually solvable generated groups;
5. determinants supported at one prime;
6. general finitely generated subgroups of `PGL₂(ℚ)`.

The likely geometric setting for the last cases is an action on a product of
the real hyperbolic plane and finitely many Bruhat–Tits trees. The concrete
decision problem is positive-submonoid intersection with a rational-point
stabilizer, not ordinary group membership.

If `M₂(3)` is undecidable, padding settles the entire two-dimensional row and
the CHHN trade gives `M₄(2)`. Only `M₃(2)` would remain.

If `M₂(3)` is decidable, the same projective formulation extends to
`M₂(k)`: finitely many singular boundary directions and a semigroup generated
by the nonsingular members. A uniform orbit-incidence algorithm could make
the entire two-dimensional row decidable; otherwise one must locate the
minimum number of invertible generators at which it becomes undecidable.

## 9. General machinery suggested by the new results

### 9.1 Semantic-agreement quotients

The paired-role construction should be generalized into a compiler calculus.

Given semantic modes `m` and role actions `A_{m,i}`, compute equalizer spaces

```text
E_{m,n,i} = ker(A_{m,i}−A_{n,i}).
```

An agreement relation is useful when:

- the relevant equalizer is invariant under the phase controls;
- its anti-diagonal copy can be quotiented;
- the boundary row annihilates the quotient kernel;
- every control word admits a total semantic decoding;
- the decoder is surjective onto source witnesses.

For several modes, construct a graph whose vertices are phase copies and
whose edges are agreement subspaces. The quotient is the colimit of the phase
representations along those agreements. The dimension saving is controlled
by the rank of the generated relation space, not by a crude block count.

This subsumes the `M₄(4)` compression and gives a systematic search surface:

1. enumerate equalizer subspaces exactly;
2. synthesize finite-state phase controls;
3. compute the maximal compatible quotient;
4. derive the induced matrices;
5. prove decoder totality and surjectivity.

### 9.2 Rank-`r` punctuation

Rank-one punctuation is ideal because arbitrary products fracture into
scalar bridges. When a rank-one word is geometrically impossible, rank two is
the next lawful object.

Write punctuation as `E=UV`, with `U` having `r` columns and `V` having `r`
rows. Then

```text
E Q E = U (VQU) V.
```

For mortality to reflect one scalar, all bridge matrices `VQU` must inhabit a
zero-product-safe one-dimensional subalgebra. A canonical target is

```text
VQU = f(Q) E₂₂.
```

Then a chain of nonzero bridges remains nonzero, and the product vanishes
exactly when one `f(Q)` vanishes.

The search variables are:

- the enlarged control matrices;
- the punctuation word;
- `U` and `V`;
- invariant structural zero identities;
- the target coefficient `f(Q)`.

The identities should first be solved symbolically on generators and their
invariant spaces, then proved for arbitrary words.

### 9.3 Zero-set representations

For a rational series `f`, exact state complexity is its Hankel rank. Mortality
asks for a series `g` satisfying only

```text
g(w)=0 ⇔ f(w)=0.
```

The minimum dimension of such a `g` is a different invariant. The present
campaign lacks a developed theory for it.

Elementary zero-preserving transformations include multiplication by a
nowhere-zero recognizable series. More general value-changing
representations may use:

- projective rescaling dependent on the word;
- a larger vector of coefficients followed by a fixed anisotropic form;
- determinant or minor tests of a smaller matrix representation;
- code-restricted completion, where only well-phased words need match the
  source and all other words must be nonzero.

Any lower-bound claim must specify whether it concerns:

- exact coefficient values;
- sign;
- support;
- zero set;
- or mortality after punctuation.

Conflating these is now a known failure mode.

### 9.4 Rank-stratified mortality

Every zero product descends through matrix ranks. Between singular
occurrences, nonsingular blocks move images and kernels without changing
dimension.

This suggests a general normal form:

1. vertices are rational subspaces or rank strata;
2. nonsingular words act by projective or Grassmannian dynamics;
3. a singular generator supplies an incidence test and rank transition;
4. mortality is reachability of the zero subspace.

In dimension two the geometry is `P¹`. In dimension three it involves
`P²`, its dual, and the Grassmannian of planes, which is again a dual
projective plane. This common language may connect the `M₂(3)` and `M₃(2)`
decidability campaigns.

## 10. Where the visible prior art is incomplete

These are research diagnoses, not priority claims.

### 10.1 Generic packings obscure structured sources

CHHN's reductions are designed for arbitrary matrices. Their structured
`Z̊` trade already exploits a common first column, but the standard mortality
frontier does not exploit pairwise equality of role actions on a
higher-dimensional subspace.

`M₄(4)` shows that the emitted matrices should be inspected as semantic
objects before generic packing is applied.

### 10.2 Fixed boundaries were counted as selectable data

The classical route proceeds from PCP pairs to one matrix per pair and then
adds an annihilator. The corrected source instead treats terminal data as a
fixed boundary. This changes the active alphabet before matrix compilation.

The numerical claim `M₃(5)` appeared in
[Neary13](references/neary-2013-four-pair-pcp-superseded-claim.md), but its
four-pair PCP premise was not retained. The successful route proves the
weaker source problem `GPCP(4)`, which is sufficient for the same mortality
cell.

### 10.3 Error rejection was preferred to total decoding

Small-alphabet reductions often reserve substantial machinery for proving
that malformed controls die. The paired-role compiler instead maps every
control word to a valid semantic word. Total decoding removes a negative
language from the proof.

This principle should be preferred whenever a finite-state suffix or prefix
phase can reinterpret redundant controls harmlessly.

### 10.4 Exact minimization was used as a proxy for mortality compression

Invariant-subspace searches and Hankel minimization answer whether the same
linear representation can be made smaller. They do not answer whether the
same zero language has a smaller representation.

The rank-six theorem closes an exact architecture and thereby prevents wasted
search. It does not weaken the zero-set-preserving campaign.

### 10.5 Low-dimensional arithmetic is siloed

The two-dimensional literature has strong separate theorems for:

- two total mortality generators;
- at most one nonsingular generator;
- scalar and projective reachability in `SL₂(ℤ)`;
- membership of a fixed nonsingular target with determinant growth.

The exact intersection of these results needed by mortality—positive
semigroup intersection with a projective incidence variety—remains exposed.
It should be studied as its own arithmetic-dynamics problem rather than
forced through PCP.

### 10.6 Arbitrary-word converses remain under-audited

The Neary terminal defect illustrates the danger. An intended witness is the
easy half of a reduction. The scientific content is usually the proof that no
arbitrary product or word can cheat.

Every future compiler must expose its arbitrary-word normal form as a named
theorem and formalize it before numerical consequences are advertised.

## 11. Campaign plan

### Phase 0: harden the present staircase

1. Formalize side-normal conjugacy.
2. Formalize the generic paired-role quotient.
3. Formalize the suffix-phase decoder and its surjectivity.
4. Prove structured `Z₄(3)` for the exact integer matrices.
5. Prove the rank-one mortality converse using the common fixed column.
6. Re-run the prior-art audit for `Z₄(3)` and `M₄(4)`.
7. Publish `M₄(4)` only after the same warning, axiom, and proof-aperture gate
   used for `M₃(5)`.

Acceptance condition:

```text
checked instance-level equivalence
+ external universality seam stated exactly
+ no unqualified novelty claim
= admissible frontier update.
```

### Phase 1: rank-two attack on `M₅(3)`

1. Formalize the all-placement Hankel-rank-six theorem.
2. Retire exact five-state minimization of the literal packing.
3. Write the rank-two bridge specification before searching matrices.
4. Solve the generator identities over finite fields for discovery.
5. Reconstruct rational candidates and verify them symbolically.
6. Search simultaneously for a punctuation word and a total control decoder.
7. Reject every candidate lacking an arbitrary-product normal form.

Primary success condition:

```text
three 5 × 5 integer matrices
  mortal
⇔
the provisional Z₄(3) scalar system reaches zero.
```

Secondary useful outcomes:

- `Z₆(2)` or `Z₅(2)`;
- a general rank-two punctuation theorem;
- a proof that the stated bridge specification is inconsistent.

### Phase 2: dimension-two arithmetic campaign

1. Prove the exact normal form reducing `M₂(3)` to projective point
   reachability for two nonsingular generators.
2. Re-derive the `SL₂(ℤ)` result in the notation required by mortality.
3. Extend through determinant strata:
   - common determinant support;
   - one-prime localization;
   - virtually solvable cases;
   - general `S`-arithmetic cases.
4. Determine whether positive-submonoid intersection with a rational-point
   stabilizer is already present under another name.
5. Formalize each decidable stratum independently.

This lane has the highest table-completion reward and weak fit with the PCP
machinery. It should run independently.

### Phase 3: `M₃(2)` rank classification

1. Close the rank-one singular case formally through low-order Skolem.
2. Express the rank-two case as mortality of `{BAⁿ|E}`.
3. Compute exterior-power recurrences controlling each rank drop.
4. Separate rank-preserving blocks from rank-dropping exponents.
5. Determine whether the remaining multi-exponent incidence reduces to a
   known decidable recurrence problem.
6. Search for a finite projective-state quotient; if none exists, isolate the
   exact arithmetic obstruction.

This is the foundational higher-dimensional lane. It should not be postponed
indefinitely in favor of easier northeast improvements.

### Phase 4: source compression to `GPCP(3)`

1. Express the `M₄(4)` suffix-phase decoder as a finite transducer.
2. Attempt to internalize its phase into word residual markers.
3. Prove total decoding before proving any intended simulation.
4. Use the [HH11](references/halava-holub-2011-binary-gpcp-reduction-tree.md)
   reduction-tree machinery to falsify accidental binary reductions.
5. If three-letter GPCP resists, search for another universal source with
   three active morphism roles.

Success gives `M₃(4)` and `M₉(2)`.

### Phase 5: only then attack tighter generator fusions

After rank-two punctuation and `GPCP(3)` have been exhausted:

- attack `Z₄(2)` and `M₄(3)`;
- attack `Z₃(2)` and `M₃(3)`;
- consider direct pair compilers only at dimensions not dominated by a
  stronger source result.

## 12. Research discipline

### 12.1 Positive results

Every claimed undecidability reduction must provide:

1. a computable map on encoded instances;
2. exact generator count and dimension;
3. a nonempty source and mortality witness;
4. completeness for intended witnesses;
5. an arbitrary-word converse;
6. integrality or an explicit denominator-clearing argument;
7. preservation of every stated structural promise;
8. the exact external universality dependency;
9. formal theorem names corresponding to each paper claim;
10. a qualified prior-art record.

### 12.2 Obstruction results

Every no-go theorem must state:

1. the architecture quantified over;
2. whether it preserves values, zeros, support, or mortality;
3. whether similarity, restriction, quotient, rescaling, or code changes are
   allowed;
4. the explicit surviving escape routes;
5. that it changes no table cell unless it proves decidability.

### 12.3 Computational searches

Finite-field and bounded-word experiments are discovery and
transcription-checking tools. They become mathematical evidence only after
one of:

- an exact symbolic identity;
- a nonzero determinant certificate;
- a formally checked exhaustive finite theorem;
- a rigorously lifted algebraic obstruction.

Absence of a short counterexample is never a correctness argument.

## 13. Ranked portfolio

The campaign should not use one scalar priority ordering for incomparable
goals.

### Best immediate positive target

```text
M₅(3)
```

It is adjacent to proved machinery, has a precise rank-two ansatz, and yields
`M₁₀(2)`.

### Highest completion leverage

```text
M₂(3) and M₃(2)
```

They are the two minimal unknown kernels. Either may be decidable rather than
undecidable.

### Cleanest source-theoretic target

```text
GPCP(3) → M₃(4).
```

This is the exact boundary between the newly established four-letter source
and decidable two-letter GPCP.

### Lowest-value direct targets

```text
M₁₁(2) and isolated pair dimensions.
```

They should be pursued only when they expose a reusable compiler. A successful
`M₅(3)` result leaps directly to `M₁₀(2)`.

## 14. Theorem ledger

| Status | Statement |
| --- | --- |
| checked | Four-role fixed-boundary equality is equivalent to restricted tag halting under the stated arithmetic hypotheses |
| checked | Corrected binary five-pair PCP, `GPCP(4)`, and the exact five-matrix instance are equivalent to that source |
| checked | The four ordinary matrices are nonsingular upper triangular; the separator is nonzero rank one |
| external | Neary's restricted-tag universality theorem and the final computability wrapper |
| external | CHHN's `Z`, `R`, padding, and generator–dimension propagation |
| provisional theorem | Paired-role semantic-agreement compression from four roles in dimension three to three controls in dimension four |
| provisional theorem | Structured `Z₄(3)` and `M₄(4)` for the explicit Neary specialization |
| provisional theorem | Every placement of the specialized literal CHHN packing has coefficient-series Hankel rank exactly six |
| conditional obstruction | Exact common-line phase fusion forces a one-sided plane |
| conditional obstruction | Rank-one punctuation with a finite one-sided bridge normal form has a decidable zero language |
| open | `M₅(3)`, rank-two punctuation, and `Z₅(2)` |
| open | `GPCP(3)`, `M₃(4)`, `M₄(3)`, and `M₃(3)` |
| open | `M₃(2)` and the unresolved pair band |
| open | `M₂(3)` and the general two-dimensional row |

## 15. Central judgment

The table is not one homogeneous problem.

The northeast frontier is a compiler problem: reduce source roles, exploit
semantic agreement, and make punctuation share generators and states.

The southwest frontier is an arithmetic-dynamics problem: classify
low-rank products and decide projective orbit incidence.

The two discoveries change the campaign because they expose reusable
structure that generic packing had erased:

```text
fixed boundaries reduce active source letters;
agreement subspaces reduce state dimension;
total decoders eliminate malformed control words;
zero-set preservation is weaker than exact realization.
```

Further northeast progress should come from these principles. Completion of
the table will likely require them to meet independent decidability theorems
at `M₂(3)` and `M₃(2)`.

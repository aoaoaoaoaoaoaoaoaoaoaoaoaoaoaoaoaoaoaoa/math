# M₉(2) run-length transfer-Hankel audit

Date: 2026-08-31
Record: `MM-O23`
Evidence: formalized core; audited six-order certificates

## Hypotheses and boundary

This obstruction applies to a binary pair `(A,B)` over `ℚ` with a rank-four cut

```text
B=UV,     U : ℚ⁴ → ℚⁿ,     V : ℚⁿ → ℚ⁴,
Mᵣ=VAʳU.
```

It assumes that three consecutive transfer moments are nonzero rescalings of the paired
benchmark roles `T,D_b,D_c`, in any order, and every later moment is the absorbed rank-one
separator `P′`. It does not assume direct-sum parser fibres, a prefix tree, common images, or a
deterministic state transition. It does not apply to a merely same-zero transfer series, changed
role values, nonconsecutive exceptional moments, a nonconstant safe tail, or a nonlinear
boundary interpretation.

## Cross-path fracture

Every word containing at least two cuts has the exact form

```text
Aʳ⁰ B Aʳ¹ B ⋯ B Aʳᵏ
= Aʳ⁰ U Mᵣ¹ Mᵣ² ⋯ Mᵣᵏ⁻¹ V Aʳᵏ.
```

All intermediate paths therefore occupy the same ambient space and may interfere. This is the
overlapping-fibre architecture left open by `MM-O19`, not a disguised direct-sum face. A total
mortality compiler would additionally need safe no-cut and exterior-run behavior; the theorem
below is a necessary dimension bound and does not assert those obligations.

For arbitrary finite selectors `(p,i)` and `(q,j)`, the transfer Hankel entry factors as

```text
(VAᵖ⁺ᑫU)ᵢⱼ = (VAᵖ)ᵢ,− (AᑫU)−,ⱼ.
```

Thus every finite transfer Hankel section has rank at most `n`. Lean checks this identity over an
arbitrary semiring, arbitrary interface, and arbitrary row and column selectors.

## Benchmark

At deletion width three and body `bb`, the exact matrices are

```text
T  = [[1,0,0,0], [0,0,0,1], [0,0,1,0], [0,1,0,0]],
P′ = [[67,0,0,0], [0,0,0,0], [81,0,0,0], [-1,0,0,0]],
D_b= [[1,25,203,1], [0,0,0,0], [0,0,243,0], [0,27,0,3]],
D_c= [[1,1508677,2,1], [0,0,0,0], [0,0,3,0], [0,1594323,0,3]].
```

Let the first three moments be `aX,bY,cZ`, where `XYZ` is one permutation of `Tbc`, and let
every moment from index three onward equal `P′`. Form the `16 × 16` block Hankel matrix
`Hᵢⱼ=Mᵢ₊ⱼ`, `0≤i,j<4`. Rows and columns below use flattened indices `4·block+coordinate`.

| order | rows | columns | determinant |
|---|---|---|---|
| `Tbc` | `0,1,2,3,4,6,7,8,11,14` | `1,2,3,4,5,7,8,9,10,11` | `539434878888077814219552 a c⁷` |
| `Tcb` | `0,1,2,3,4,6,7,10,11,12` | `0,1,2,3,4,5,7,9,10,11` | `246112452864 a b c⁶` |
| `bTc` | `0,1,2,3,4,5,7,8,11,14` | `1,2,3,4,6,7,8,9,10,11` | `−4543214987860848 b² c⁶` |
| `bcT` | `0,1,2,3,6,7,9,10,11,14` | `0,2,3,4,5,7,8,9,11,12` | `−531441 b c⁵` |
| `cTb` | `0,1,2,3,4,5,6,10,11,15` | `1,2,3,5,6,7,8,9,10,11` | `−464904586800 b² c⁷` |
| `cbT` | `1,2,3,4,5,6,7,9,11,15` | `1,2,3,4,5,6,7,8,10,11` | `−5481 b² c⁶` |

Every determinant is nonzero when `a,b,c` are nonzero. Hence every such exact transfer system
has `n≥10`, for all six assignments of the three roles to the consecutive run lengths.

`tools/audit_m92_run_length_hankel.py` reconstructs the four matrices, all six block Hankel
matrices, the listed minors, and their determinants with exact SymPy arithmetic. It is part of
`scripts/check.sh`. Lean independently checks the `Tbc` certificate by sparse kernel
elimination. Its retained row and column order is a permutation of the sorted certificate above;
only nonsingularity is used.

## Formal boundary

`MatrixMortality/RunLengthHankel.lean` checks:

- the displayed `T,D_b,D_c` values against the paired source at `β=3`, body `bb`;
- generic finite transfer-Hankel factorization;
- the expanded `10 × 10` `Tbc` minor;
- triviality of its kernel for `a≠0` and `c≠0`, even without assuming `b≠0`;
- nonzero determinant and the ambient bound `10≤n`.

The other five determinant certificates are exact audited computation, not Lean theorems. The
result does not exclude history-sensitive same-zero behavior whose internal moments differ from
the source matrices, nor a transfer tail that moves through several safe source-semigroup
values. Those are the surviving seams.

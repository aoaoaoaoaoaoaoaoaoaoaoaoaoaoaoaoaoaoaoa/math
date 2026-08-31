# M₉(2) geometric-tail transfer-Hankel audit

Date: 2026-08-31
Record: `MM-O26`
Evidence: formalized core; audited six-order certificates

## Hypotheses

Place nonzero rescalings of the paired benchmark roles `T,D_b,D_c` at consecutive transfer
times `0,1,2`, in any order. For a nonzero scalar `τ`, set

```text
Mᵣ = τ^(r-2) P′,     r≥3,
```

where `P′` is the absorbed rank-one separator. The tail is nonconstant when `τ≠1` and has a
one-state exact linear realization. The claim is that every exact transfer realization
`Mᵣ=VAʳU` has ambient dimension at least ten.

This is precisely the consecutive one-state moving-tail seam left open by `MM-O25`. It does not
cover zero tail ratio, a sum of several tail modes, changed role values preserving only zeros,
or nonlinear boundary semantics.

## Certificates

Use the same six `10 × 10` row and column selections as `MM-O23`. Exact symbolic determinants
for the geometric tail are:

| order | determinant |
|---|---|
| `Tbc` | `539434878888077814219552 a c⁷ τ³` |
| `Tcb` | `246112452864 a b c⁶ τ²` |
| `bTc` | `−4543214987860848 b² c⁶ τ³` |
| `bcT` | `−531441 b c⁵ τ⁴` |
| `cTb` | `−464904586800 b² c⁷ τ³` |
| `cbT` | `−5481 b² c⁶ τ³` |

Every determinant is nonzero when the three role scales and `τ` are nonzero. Hence all six
orders require at least ten states.

Lean checks the `Tbc` order by an explicit sparse kernel elimination. Its result is stronger
than the stated application: the data-`b` scale is unrestricted, while the toggle, data-`c`, and
tail scales must be nonzero. The exact minor factors through every proposed ambient transfer
system, giving the cardinal lower bound.

`tools/audit_m92_run_length_hankel.py` reconstructs the six geometric block-Hankel matrices and
the displayed determinants with exact SymPy arithmetic. The program also retains the six
constant-tail certificates of `MM-O23`, so the geometric extension cannot silently weaken the
earlier audit.

## Formal boundary

`MatrixMortality/GeometricTailHankel.lean` checks:

- the exact `T,D_b,D_c,τP′,τ²P′,…` moment sequence;
- one expanded sparse `10 × 10` minor;
- triviality of its kernel for nonzero toggle, data-`c`, and tail scales;
- nonzero determinant and the ambient bound `10≤n` for every exact realization.

The other five orders remain exact audited computation. This record closes scalar one-state
separator motion, not arbitrary independently realized tails. A multi-mode consecutive tail or
same-zero change to the internal moments remains open.

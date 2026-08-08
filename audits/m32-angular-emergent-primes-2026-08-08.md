# M₃(2) Angular Emergent-Primes Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The fixed reset geodesic suggested a compactness proof using only endpoint determinant factors,
complementary contents, Smith labels, finitely many congruences, and the product formula. This
audit reconstructs the angular extension class and tests that proposal against a genuine
first-hit terminal word.

The support-only route is false. Terminality leaves the angular lift free, actual terminal words
create new primes outside every coefficient and branch-cyclotomic factor, and the moving wait
gauge has nontrivial directional height. The only surviving compactness target is the special
additive continuant of the actual guard recurrence.

## Angular Boundary

In primitive endpoint bases, each transfer is upper triangular:

```text
T_i=[[x_i,b_i],[0,y_i]],
x_i=q_i^s h_i,   y_i=−k_i.
```

Their product is `T=[[X,β],[0,Y]]`, where

```text
X=p^Ω ∏h_i,   Y=(−1)^n ∏k_i.
```

Changing the complement at endpoint `i` by `m_i` changes the local shear by
`b_i ↦ b_i+x_i m_i−y_i m_(i+1)`. The internal terms telescope, so the
complement-independent extension class is exactly

```text
[β] ∈ ℤ/gcd(X,Y)ℤ.
```

In the physical terminal bases the full endpoint product has the unique form

```text
M_w=[[Y,−RY],[c,X−Rc]],   c=−β.
```

The endpoint equation `M_w(R,1)ᵀ=X(0,1)ᵀ` and `det M_w=XY` determine `X,Y` but leave
`c ∈ ℤ` arbitrary. The fixed mod-`p` flag only prescribes one nonzero residue of `c`; it
does not select even the finite extension class. Thus terminality and the full radial kernel
cannot bound the primitive pole

```text
((Rc−X)/g,c/g),   g=gcd(X,c).
```

Varying one abstract local shear by a multiple of all retained moduli preserves every diagonal
factor, valuation, Smith first divisor, and finite label while making the final shear unbounded.
This proves a precise scope statement: a proof that forgets the actual off-diagonal recurrence
has forgotten the only datum that could control the angle.

## Genuine Emergent Primes

For the already checked lawful first-hit execution

```text
(p,s,A,D,L)=(3,2,467,−35,124),   waits=[3,1],   reset=(308,1),
```

Lean now verifies

```text
M_w=[[−789880,243283040],[−25420,−306280]],
M_w(308,1)ᵀ=(0,−8135640)ᵀ,
gcd(8135640,25420)=620.
```

The primitive pole vector is therefore `(494,−41)`, with `494=2·13·19`. Neither `19`
nor `41` divides

```text
3·467·35·124·343·308·(3³−1)·(3¹−1),
```

which contains all coefficient, reset, and branch-cyclotomic support for this word. The
complementary content allocation is exact; these primes are created by addition in the angular
continuant, not omitted from the determinant bookkeeping.

## Directional Gauge Cost

At depth two the checked wait-frame gauge is conjugate to

```text
diag(1,p^(2(b−a))).
```

Its projective adelic sup-height is `p^(2|b−a|)`: for positive exponent the Archimedean
maximum pays, and for negative exponent the `p`-adic maximum pays. The product formula removes a
common scalar, not an eigenvalue ratio. Every family of local operator norms has at least this
product by the spectral-radius bound. For waits `3 → 1` the cost is `3⁴=81`.

This does not contradict scalar adelic continued-fraction theorems. It rejects assigning neutral
matrix height to the gauge before proving a scalar, path-dependent conjugacy that follows the
actual carried direction.

## Surviving Recurrence

Restoring the exact endpoint matrices gives the additive continuant

```text
c₀=0,   c₁=1,
c_(i+2)=(A+Dq_i^s−Lq_(i+1))c_(i+1)
        +DLq_i^s(q_i−1)c_i.
```

This coefficient agrees with the checked cumulative endpoint recurrence; no parallel Lean API
is retained. Any decision proof must give a coefficient-effective upper bound for the primitive
pole along legal terminal solutions, or control `gcd(X_n,c_n)` there. A support theorem alone
cannot do so.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| extension class is `β mod gcd(X,Y)` | promotion | independently reconstructed by complement coboundaries |
| terminal boundary leaves the angular lift free | promotion | exact two-by-two calculation |
| diagonal, Smith, valuation, and finite-label data cannot bound angle | promotion | valid abstract no-go with explicit recurrence scope |
| lawful terminal pole has primes outside determinant support | formalized | exact first-hit example checked by Lean |
| pure-`p` wait gauge is adelically neutral | rejected | projective height is `p^(2|b−a|)` |
| every angular compactness theorem is impossible | rejected as overbroad | a recurrence-sensitive theorem remains open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: endpoint-only compactness; fixed S-unit support for the primitive pole; direction-free product-formula cancellation of the wait gauge
REMAINS: a coefficient-effective bound or gcd theorem for the actual additive continuant, opposed by an exact aperiodic reset orbit with moving support
DISTANCE: the enemy is now additive prime creation in one recurrence, not missing multiplicative determinant allocation
```

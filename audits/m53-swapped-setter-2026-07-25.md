# Swapped-Digit Setter Audit

**Date:** 2026-07-25
**Target:** three `5 × 5` matrices
**Verdict:** the mixed separator survives the digit swap; every integral
valuation-one pole now belongs to a finite set of primitive slopes

This audit changes only the numerical embedding of binary strings.  The
ordinary setter uses ternary digits

```text
0 ↦ 1,       1 ↦ 2.
```

Here they are interchanged:

```text
0 ↦ 2,       1 ↦ 1.                         (1)
```

Both digits remain nonzero, so length and concatenation are still represented
exactly and the code remains injective.  Every PCP equality is therefore
unchanged.  The gain is geometric: the projective center becomes negative,
whereas every pole remains positive.

Nothing below proves projective avoidance or `M₅(3)`.

## Exact Five-State Candidate

Put

```text
ρ=3^β,       μ=[10^β]₃=2ρ−1,       t=3ρ,
r=t/μ.
```

For the distinguished upper letter `c`,

```text
U_c=1,       A_c=3,
H=μ+t=5ρ−1,       R=H−3μ=2−ρ.
```

Since `β≥3`,

```text
1<r<2,       H>0,       R<0.
```

Retain the side-normal rule and erasure matrices

```text
R_x=[[1,V_x^R,U_x],[0,B_x^R,0],[0,0,A_x]],
D_x=[[1,V_x^D,U_x],[0,B_x^D,0],[0,0,A_x]],
```

but evaluate their binary words with (1).  Put

```text
δ_x=(V_x^R−V_x^D,B_x^R−B_x^D,0)ᵀ,
f=(1,0,r)ᵀ,
p=(0,−1,0)ᵀ,
q=(0,0,r(2−r))ᵀ,
B=[f p q].
```

The basis is invertible because `r(2−r)≠0`.  Let

```text
α=1+r=H/μ,       λ=α/μ,
R̄_x=B⁻¹R_xB,       δ̄_x=B⁻¹δ_x,

A_x =
[[R̄_x, δ̄_x, 0],
 [0_(2×3), 0, 0]].
```

Use the same delimiter shape as the ordinary setter:

```text
S =
[[1,0,0, 0, 0],
 [0,1,0,−1, λ],
 [0,0,1, 0,−1],
 [0,1,0,−1, λ],
 [0,0,1, 0,−1]].
```

Finally,

```text
C̃=(μ,1,0,1,0)ᵀ,       L̃=(1,0,0,0,0).
```

The regular rule/erasure decoder is unchanged.  Indeed, `B(μ,1,0)ᵀ` is the
side boundary `(μ,−1,t)ᵀ`, one delimiter copies the lower coordinate into the
marker channel, and every data matrix clears that channel.

Direct multiplication gives

```text
rank S=3,       rank S²=2,       rank S³=1,
Sⁿ=S³  for n≥3,
S²A_cS³=λC̃L̃.                               (2)
```

The last identity uses

```text
R_cf=D_cf=(1+r)f+q.
```

Thus the internal physical word `S²A_cS³` is again the exact rank-one
separator.  Every regular physical word has the same total suffix decoder as
in `MM-M03`, and source halting still implies mortality.

## Orientation-Preserving Transfer

For a regular role block with side product

```text
M_z=[[1,V,U],[0,B,0],[0,0,A]],
```

the square-run transfer on the two-plane `im S²` is

```text
F_z =
[[1+rU,                  −V],
 [κ(A−1−rU),             κV]],

κ=α/(μ(2−r))>0.                           (3)
```

Hence

```text
det F_z=κVA>0.                              (4)
```

All projective transfers are now orientation preserving.  In the scaled
coordinate `y=μx`, put

```text
P_z=μ+tU_z,       h=H/R<0.
```

Then

```text
Ψ_z(y)=h(1−μA_z/(P_z−V_zy)),
π_z=P_z/V_z>0.                              (5)
```

The pole `π_z` is always positive, while the common center `h` is negative.
The single `c` block still maps the ordinary reset to the distinguished
boundary:

```text
Ψ_c(0)=1.
```

Equations (2)–(5) give the same complete malformed-word reduction as the
ordinary setter: the only missing theorem is avoidance of the poles under
arbitrary iterations of (5).

## One-Sided Centered Carry

Put

```text
C_z=RP_z−HV_z,       K=RHμ.
```

The centered integer recurrence remains

```text
X'=A_zY,
Y'=C_zY+KV_zX.                              (6)
```

The digit swap changes its order structure:

```text
C_z<0,       K<0                            (7)
```

for every nonempty role block, because `R<0` and `H,P_z,V_z>0`.

The valuation shells are unchanged.  Modulo `9`, every punctuated upper code
is `8`.  A rule lower code is `5`, while a multi-role erasure lower code is
`8`.  Since `R≡2` and `H≡8`, respectively,

```text
C_z≡3 or 6 (mod 9).
```

Thus every block other than a single erasure has `v₃(C_z)=1`.  Direct
calculation for the exceptional blocks gives

```text
C_Dc=−ρH,
C_Db=−ρ(18ρ²−40ρ+17),
```

whose cofactors are `3`-adic units.  Either single erasure therefore has
`v₃(C_z)=β`.  At the distinguished boundary, a nonterminal block `v` again
yields

```text
d=|U(v)|−lcs(U(v)10^β,V(v)),
Δ=(P_v−V_v)/3^lcs(U(v)10^β,V(v)).
```

If the next pole block lies in the valuation-one shell, (6) requires

```text
C_zΔ+3HμV_z=0.                              (8)
```

By (7), equation (8) forces

```text
0<Δ<3μ.                                     (9)
```

The unbounded negative divisor rays of the ordinary digit order have
disappeared.

There is a stronger finite-slope normal form.  Write `D=ρ−2=−R` and reduce

```text
P_z=gp,       V_z=gv,       gcd(p,v)=1.
```

Let

```text
q=gcd(D,v),       D=qd,       v=qv₀.
```

Then an integral solution of (8) satisfies

```text
Δ(dp+Hv₀)=3Hμv₀.                            (10)
```

Since

```text
gcd(dp+Hv₀,v₀)=gcd(d,v₀)=1,
```

equation (10) implies

```text
dp+Hv₀ ∣ 3Hμ.                               (11)
```

Thus `q`, `p`, and `v₀` all range over finite, effectively enumerable sets:

```text
q∣D,       v₀<3μ,       p≤3Hμ/d.           (12)
```

Every integral valuation-one pole belongs to one of finitely many primitive
slopes `p/(qv₀)`.  This is stronger than the ordinary setter's divisor rays,
where the reduced denominator remained unbounded.

The distinguished value is rigid:

```text
Δ=H       ↔       P_z=V_z.                 (13)
```

Indeed, substituting `Δ=H` into (8) and using `H+D=3μ` gives
`DP_z=DV_z`; the converse is immediate.

## Remaining β-Shell

The single `b` erasure would require

```text
Δ_b =
2(2ρ−1)(5ρ−1)/(18ρ²−40ρ+17).
```

For `ρ≥27`,

```text
1<Δ_b<2,
```

so an integer boundary discrepancy cannot reach it.

The single `c` erasure requires

```text
Δ_c=2μ.                                     (14)
```

Equation (14) has not yet been excluded for every source block.  It is the
only surviving distinguished-boundary β-shell obligation.

## Bounded Diagnostics

[`tools/explore_setter_projective.py`](../tools/explore_setter_projective.py)
accepts `--swapped-digits` and evaluates (5) exactly.  At `β=3`, body `bbcc`,
it found:

```text
role-block length ≤3, three transfers:
    670235 distinct projective states, no collision

target-block length ≤12:
    no nonterminal integral valuation-one pole
```

The same target search through length `12` found no false integral pole for
bodies `bb`, `bc`, `cb`, or `cc`.  These are finite computations, not theorem
evidence.

## Promotion Boundary

The swapped five-state matrices, internal separator, projective transfer,
strict sign (7), finite-slope reduction (10)–(12), and rigidity (13) are
audited mathematics.  The bounded searches are computational diagnostics.

No finite-slope exclusion theorem is known.  A fixed nonterminal slope still
defines an asynchronous correspondence equation, and the terminal slope
`1` is the original undecidable equality.  Arbitrary-depth projective
avoidance also remains open.

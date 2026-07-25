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

## Elimination of the β-Shell

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

Equation (14) is impossible.  Let

```text
m=|U(v)|,       k=lcs(U(v)10^β,V(v)).
```

In the `d=β` shell, `k=m−β`, so deleting the common suffix leaves an upper
prefix `A` of length `2β+1`.  Equation (14) is

```text
[A]₃−[B]₃=2μ=4ρ−2,                         (15)
```

where `B` is the corresponding lower prefix.  Since `β≥3`, subtracting
`2μ` cannot change the `2β+1`-digit length, so `A` and `B` have equal length.

The base-three expansion of `2μ` is

```text
1·0·2^(β−1)·1.
```

Adding it to `B` from right to left, while requiring every digit of both
summands to remain `1` or `2`, determines the complete carry pattern.  In
binary notation it gives

```text
A=T·00·z·10,
B=T·11·z·01,                                (16)
|T|=β−1,       |z|=β−2.
```

Now classify the upper prefix.  The two zeros at positions `β−1,β` of `A`
belong to the first `b` codeword.  If `s` initial `c` letters precede it,
then the final `10` of `A` must begin the next `b` codeword or the terminal
marker.  Hence

```text
0≤s≤β−3
```

and the upper data spelling starts

```text
c^s·b·c^(β−s−3)
```

before that next `b` or the end marker.  Consequently (16) fixes the lower
prefix as

```text
B=
1^(s+1)·0^(β−s−2)·11·0^s·1^(β−s−2)·01.    (17)
```

If `s=0`, the first tile carries `b`.  Its lower word is either `0` or `110`,
neither of which begins the right side of (17), which starts `10`.

If `s>0`, the first tile carries `c`.  It must be the rule tile, since the
erasure lower word starts with `0`.  After the rule's initial `1`, equation
(17) requires the continuation `1^s0`.  The body therefore begins
`c^(s−1)b`, unless the zero comes from the final `10` after the body.  The
latter would force `|body|=s−1<β−1`, contrary to the source envelope.  In the
former case the selected `b` contributes `β` consecutive zeros, but (17)
allows only `β−s−2<β` zeros before the next `1`.  This is also impossible.

Thus no distinguished-boundary discrepancy in the `β` shell can reach either
single-erasure pole.

## Canonical Valuation-One Residue

The word `D_c^(β+1)` always gives

```text
d=1,       Δ₀=(9ρ−5)/2.                    (18)
```

This residue cannot meet a valuation-one pole when `β≥4`.  Substituting
`Δ₀` into (8) gives the target-ratio equation

```text
D(9ρ−5)P=H(3ρ−1)V.                         (19)
```

Reduce (19) modulo `ρ`.  Since

```text
D≡−2,       H≡−1,       P≡μ≡−1 (mod ρ),
```

equation (19) forces

```text
V≡−10≡ρ−10 (mod ρ).                        (20)
```

The `β` base-three digits of `ρ−10` are

```text
2^(β−3)·1·2·2.
```

Under the swapped digit embedding, (20) says that the target lower word ends
in

```text
0^(β−3)100.                                 (21)
```

Every admissible target block ends in an erasure role.  If its entire lower
word consists of erasures, it has no `1`.  Otherwise, let the last rule be
followed by `n` erasures.  Its lower spelling ends in `1·0^(n+1)`.  Pattern
(21) forces `n=1`; but the digit immediately preceding the final `10` of
either rule word is `1`, so the actual four-bit suffix is `1100`, not `0100`.
For `β≥4`, this contradicts (21).

The Neary compiler emits `β=10·period`, hence always lies in this range.
Thus the canonical positive valuation-one residue cannot create a false pole
in any emitted source.

## Target Suffix Sieve

The target side admits a stronger congruence than (20).  Suppose a positive
`3`-adic unit `Δ` meets a valuation-one target pole.  Equation (8) is
equivalent to

```text
ΔDP=H(3μ−Δ)V.                               (22)
```

Every nonempty upper role word ends in binary `1`.  Therefore `P`, modulo

```text
9ρ=3^(β+2),
```

is the swapped code of `11·0^β`, namely `H`.  Both cancellands are units
modulo `3`, so (22) gives

```text
V ≡ σ_Δ := ΔD(3μ−Δ)⁻¹ (mod 9ρ).           (23)
```

This fixes the target residue on its final `β+2` positions.  If the lower
word has at least `β+2` letters, every fixed-width digit of `σ_Δ` must be
nonzero and its swapped binary decoding must be a suffix of a concatenation
of the four lower role words.  If the lower word is shorter, then
`V=σ_Δ`; the leading zero padding is not a word digit, and only the canonical
base-three expansion is constrained to use `1,2`.  In particular, an
internal zero digit is impossible, whereas a shorter all-nonzero residue
survives only as the single exact candidate `V=σ_Δ`.

The recurrent value

```text
Δ=ρ−1
```

is excluded uniformly.  Direct multiplication gives

```text
(5ρ−2)(8ρ−1) ≡ (ρ−1)(ρ−2) (mod 9ρ),
```

so (23) becomes

```text
V≡8ρ−1 (mod 9ρ).
```

The `β+2` ternary digits of `8ρ−1` are `21·2^β`; under the swapped embedding
the target lower word must end in

```text
01·0^β.                                     (24)
```

This factor cannot occur.  Inside `R_b=110`, the only `1` followed by a zero
is preceded by `1`.  Inside `R_c=1·H(body)·10`, every `b` code and the final
`10` are likewise preceded by `1`.  Across a role boundary, an erasure
followed by a rule gives `011`, not `010`.  Hence every occurrence of
`1·0^β` in a lower spelling is preceded by `1`, contradicting (24).

The distinction between positivity and pole compatibility is essential.  At
`β=4`, body `ccccbb`, the source queue has the exact nonhalting cycle

```text
bbbccccbbb ↔ cccbbbb.
```

Nevertheless `R_cD_b^3` has `d=1` and `Δ=364`.  Its suffix residue from (23)
is base-three `1012`, containing a forbidden zero digit.  Thus positive
near-matches alone do not imply source halting; the target-suffix sieve is the
correct intermediate invariant.

## Bounded Diagnostics

[`tools/explore_setter_projective.py`](../tools/explore_setter_projective.py)
accepts `--swapped-digits` and evaluates (5) exactly.  At `β=3`, body `bbcc`,
it found:

```text
role-block length ≤3, three transfers:
    670235 distinct projective states, no collision

role-block length ≤3, false-pole words of length ≤6:
    forward layers 2, 95, 7979, 670235
    backward layers 84, 7056, 592704
    no collision

target-block length ≤12:
    no nonterminal integral valuation-one pole

role-word length ≤10:
    no distinguished-boundary β-shell hit
```

The six-block result uses exact rational Möbius inversion and intersects the
three-step forward orbit with the two-step preimage tree rooted at every pole.
It covers all `84⁶` block sequences without enumerating them individually.

The same target search through length `12` found no false integral pole for
bodies `bb`, `bc`, `cb`, or `cc`.  These are finite computations, not theorem
evidence.

## Promotion Boundary

The swapped five-state matrices, internal separator, projective transfer,
strict sign (7), finite-slope reduction (10)–(12), rigidity (13),
β-shell exclusion (15)–(17), canonical-residue exclusion (18)–(21), and the
target-suffix sieve (22)–(24) are audited mathematics.  The bounded searches
are computational diagnostics.

No finite-slope exclusion theorem is known.  A fixed nonterminal slope still
defines an asynchronous correspondence equation, and the terminal slope
`1` is the original undecidable equality.  Arbitrary-depth projective
avoidance also remains open.

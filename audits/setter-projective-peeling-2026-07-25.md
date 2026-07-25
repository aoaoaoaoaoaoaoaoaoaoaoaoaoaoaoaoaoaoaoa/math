# Setter Projective Peeling Audit

**Date:** 2026-07-25
**Target:** the first malformed square-run transition in the five-state setter candidate
**Verdict:** reset-zero orbits survive one transfer; the resonant carry is an exact
word-valued suffix discrepancy, not an ordinary finite pulse state

This audit sharpens the projective obligation in `MM-S01`. It proves that a false pole cannot
occur immediately after one transfer from the ordinary rank-one reset. It does not settle
arbitrary projective orbits and therefore does not prove `M₅(3)`.

## Scaled Transfer

Put

```text
ρ=3^β,          μ=(5ρ−1)/2,       t=3ρ,
h=(17ρ−1)/(2(ρ+1)).
```

Scale the affine projective coordinate of `MM-S01` by `y=μx`. For a nonempty role block `z`,
write

```text
X_z=spell(nearyUpper,z),       Y_z=spell(nearyLower,z),
U_z=[X_z]₃,                    V_z=[Y_z]₃,
A_z=3^|X_z|,
P_z=μ+tU_z=[X_z·10^β]₃,
q_z=P_z−μA_z.
```

The square-run transfer and its pole become

```text
Ψ_z(y)=h(1−μA_z/(P_z−V_zy)),              (1)
π_z=P_z/V_z.                              (2)
```

Every one-letter upper contribution has positive `q`: for `c`, `q_c=ρ+1`; for `b`,
`q_b=(17ρ−1)/2`. Concatenation satisfies

```text
q_{uv}=A_vq_u+q_v.
```

Thus `q_z>0` for every nonempty block.

## Pole Shells

Every `P_z` and `V_z` is a `3`-adic unit. The setter constant is

```text
h=P_c/q_c,
P_c=(17ρ−1)/2,       q_c=ρ+1.
```

Hence

```text
π_z−h=(q_cP_z−P_cV_z)/(q_cV_z).           (3)
```

The possible valuations are exactly

```text
v₃(π_z−h)=
  β,  if z is one erasure role;
  1,  otherwise.                           (4)
```

For the second case, `P_z≡4 mod 9` because the appended marker ends in two encoded zero
digits. If the last role is a rule, `V_z≡7 mod 9` because every rule lower word ends in `10`;
if it is an erasure and another role precedes it, `V_z≡4 mod 9` because the lower spelling
ends in `00`. Since `q_c≡1` and `P_c≡4 mod 9`, the numerator in (3) is respectively `3` or
`6 mod 9`.

For the two exceptional single erasures, direct calculation gives

```text
q_cP_{D_c}−P_c = ρ(17ρ−1)/2,

q_cP_{D_b}−P_c = ρ(45ρ²+53ρ−10)/2.
```

The factors following `ρ` are `3`-adic units.

## Reset-Zero Peeling

At the ordinary reset `y=0`, equation (1) gives

```text
Ψ_u(0)=h q_u/P_u,
Ψ_u(0)−h=−h μA_u/P_u.
```

Therefore

```text
0<Ψ_u(0)<h,
v₃(Ψ_u(0)−h)=|X_u|.                       (5)
```

Suppose `Ψ_u(0)=π_z`. Equations (4) and (5) force `|X_u|∈{1,β}`.

If `|X_u|=1`, then `u` consists of one `c` role. Since `h=P_c/q_c`,

```text
Ψ_u(0)=1.
```

The equality `π_z=1` is `P_z=V_z`, exactly the original terminal-match equation. It is not a
malformed pole.

If `|X_u|=β`, no `b` role can occur because its upper word has length `β+2`. Thus `u` consists
of `β` many `c` roles. But

```text
Ψ_u(0)<h<P_c≤P_{D_b},P_{D_c},
```

whereas (4) says that a pole in the `β`-shell must be one of those two single-erasure poles.
Equality is impossible.

Consequently:

> **Reset-zero one-transfer theorem.** For `β≥3`, a projective orbit beginning at the ordinary
> reset `0` cannot hit a pole after one preceding square-run transfer, except at `1`, where
> the next pole is a genuine terminal match.

Any false projective orbit must therefore survive at least two nontrivial transfers, or begin
from the distinguished boundary value `1`.

## Centered Integer Carry

The valuation calculation extends to an exact two-coordinate recurrence. Put

```text
H=(17ρ−1)/2,      R=ρ+1,      K=RHμ,
C_z=RP_z−HV_z,    m_z=|X_z|.
```

Represent a finite projective state by nonzero integers `X,Y` through

```text
y−h=−HμX/Y.
```

Substitution in equation (1) gives

```text
X'=A_zY,
Y'=C_zY+KV_zX.                              (6)
```

The two resets have particularly small representatives:

```text
y=0:  (X,Y)=(1,Rμ),
y=1:  (X,Y)=(3,RH).
```

The denominator in (6) vanishes exactly when the current projective state is
the pole `π_z`. Thus projective avoidance is an integer carry problem, not
merely an analogy with one.

Let

```text
d=v₃(X)−v₃(Y),      s_z=v₃(C_z)∈{1,β}.
```

If `d≠s_z`, the two summands defining `Y'` have distinct valuations, so no
cancellation is possible and

```text
d'=m_z−min(d,s_z).                           (7)
```

If `d=s_z` and the denominator is nonzero, let `δ≥0` be the extra valuation
created when the two unit parts are added. Then

```text
d'=m_z−s_z−δ.                                (8)
```

An infinite valuation increase is precisely a pole. For an admissible block,
which ends in an erasure role, the first unit test is also explicit:

```text
C_z/3 ≡ 2 (mod 3)       for every block of at least two roles,
C_z/3^β ≡ 1 (mod 3)     for either single erasure,
V_z ≡ K ≡ 1 (mod 3).
```

Consequently a pole in the valuation-one shell requires the normalized
`X/Y` unit to be `1 mod 3`, while a single-erasure pole requires it to be
`2 mod 3`. Residue alone does not remain separating at greater depth, but it
settles the only equal-valuation branch needed below.

## Two-Transfer Gate

After the first transfer from reset zero, equation (6) reduces projectively to

```text
(X₁,Y₁)=(A_u,RP_u).
```

Hence `d₁=m_u`, and its normalized unit is `1 mod 3`. If `u` is the single
`c` erasure, the state is exactly `1`; this is the distinguished-boundary
branch. Otherwise a state after the second transfer can lie in a pole shell
only in one of the following cases:

1. the next pole belongs to a block of at least two roles, and the second
   block `v` consists of exactly two `c` roles;
2. the next pole is a single erasure, and `v` consists of exactly `β+1`
   `c` roles;
3. the next pole is a single erasure, `u` consists of exactly two `c` roles,
   and `v` is the single `b` erasure.

Here “consists of `c` roles” permits either rule phase or erasure phase at
each nonfinal position; admissibility forces the final role to be an erasure.

To prove the list, first suppose `v` has at least two roles. Then `s_v=1`.
Outside the distinguished-boundary branch, `m_u>1`, so equation (7) gives

```text
d₂=m_v−1.
```

Thus `d₂=1` forces `m_v=2`, while `d₂=β` forces `m_v=β+1`. A `b` role costs
`β+2` upper bits, so both blocks contain only `c` roles. If `v` is one
erasure, `D_c` gives no positive pole shell. For `D_b`, equation (7) gives

```text
d₂=β+2−min(m_u,β).
```

The only value in `{1,β}` is `β`, attained at `m_u=2`. Finally, the apparent
resonance `m_u=β` has normalized unit `1 mod 3`, whereas either
single-erasure pole requires unit `2 mod 3`; equation (8) therefore has
`δ=0` and produces no omitted case.

This is a necessary shape theorem, not avoidance. It collapses an arbitrary
second block to three rigid families; the first block and the prospective
pole block remain unbounded.

## Distinguished-Boundary Suffix Gate

Starting from `y=1`, equation (6) simplifies even further:

```text
(X₁,Y₁)=(A_v,R(P_v−V_v)).                    (9)
```

Indeed `H−R=3μ`, so the two terms in `Y₁` combine exactly. If `P_v=V_v`,
the current block is already a genuine terminal match. Otherwise put

```text
k=v₃(P_v−V_v).
```

Because ternary encoding uses only the nonzero digits `1,2`, `k` is exactly
the length of the longest common binary suffix of

```text
X_v·10^β       and       Y_v.
```

Equation (9) gives

```text
d₁=m_v−k.
```

Therefore a false pole after one completed transfer from the distinguished
boundary is possible only when

```text
k=m_v−1       or       k=m_v−β.              (10)
```

This is the precise seam between the projective carry and the Neary pulse
theorem. Ordinary valuation sees only the number in (10); a successful
avoidance proof must retain the suffix alignment that produced `k`.

## Reverse Suffix-Discrepancy Queue

The suffix alignment in (10) has an exact operational form. Let `M=10^β`.
For a processed role suffix `s`, reverse both terminal words and cancel their
common prefix:

```text
rev(U(s)M)=q·u_s,       rev(V(s))=q·v_s,
```

where `q` is longest possible. Until the first mismatch, at least one of
`u_s,v_s` is empty. If a role `r` is prepended, then

```text
rev(U(rs)M)=rev(U(s)M)·rev(U(r)),
rev(V(rs)) =rev(V(s)) ·rev(V(r)).
```

The next state is therefore obtained by appending the two reversed role
images to `u_s,v_s` and cancelling their common prefix. Induction on the
processed suffix proves that the cancelled length is exactly

```text
k=lcs(U(z)M,V(z)).
```

Once both residuals are nonempty, their first bits differ. No role still to
the left can alter this first mismatch, so the scan stops. This is the usual
PCP discrepancy mechanism, read from the terminal boundary.

The dangerous valuation gaps nevertheless leave a bounded front fringe.
Suppose the first mismatch appears while processing a suffix `q`, and write
`z=pq`. Put

```text
m=|U(z)|,       d=m−k.
```

Since the matched suffix lies inside `U(q)M`,

```text
k≤|U(q)|+|M|.
```

Consequently

```text
|U(p)|=m−|U(q)|=d+k−|U(q)|≤d+|M|.          (11)
```

For the two resonant gaps in (10), the unprocessed left prefix therefore has
upper length at most

```text
d=1:  β+2,          d=β:  2β+1.            (12)
```

If the scan reaches the left boundary without a mismatch and `d>0`, the lower
word is a suffix of the upper boundary word. The remaining upper residual has
exact length

```text
d+|M|,
```

giving the same two bounds.

This is not a finite-state avoidance theorem. The exact pre-mismatch state is
the residual word `u_s` or `v_s`; nothing above bounds that queue before the
terminal fringe is exposed. Any finite invariant must therefore quotient the
discrepancy semantically while preserving the two bounded target families.
Discarding the residual and retaining only pulse phase, length, valuation, or
a fixed congruence modulus does not preserve the exact terminal-match
recurrence. The bounded diagnostics below additionally show saturation of the
tested residue-only quotients.

## Elimination of the Beta Shell

One of the two distinguished-boundary resonances can be closed outright.
Suppose a block `v` does not itself give a terminal match. Retain

```text
m=|U(v)|,       k=lcs(U(v)M,V(v)),       d=m−k
```

and put

```text
Δ=(P_v−V_v)/3^k.
```

The exactness of `k` makes `Δ` a `3`-adic unit. Equation (9), divided by
`3^k`, represents the resulting projective state by

```text
(X,Y)=(3^d,RΔ).                              (13)
```

If the next block `z` is a pole, equation (6) gives

```text
C_zΔ+HμV_z3^d=0.                             (14)
```

For `d=β`, valuation equality forces `v₃(C_z)=β`. By the pole-shell theorem,
`z` must be one of the two single erasures.

For the `b` erasure, direct substitution gives

```text
P_{D_b}=(45ρ²+8ρ−1)/2,
C_{D_b}=ρ(45ρ²+53ρ−10)/2.
```

The required discrepancy is therefore

```text
Δ_b=−2Hμ/(45ρ²+53ρ−10).
```

It lies strictly between `−1` and `0`, because

```text
(45ρ²+53ρ−10)−2Hμ=(5ρ²+128ρ−21)/2>0.
```

It cannot equal the integer `Δ`.

For the `c` erasure,

```text
P_{D_c}=H,       C_{D_c}=Hρ,
```

so (14) would require

```text
Δ=−μ.                                          (15)
```

Equation (15) is forbidden by the self-synchronizing upper code. Since
`k=m−β`, it says

```text
V_v=P_v+μ3^{m−β}.                              (16)
```

Write the base-three digits from least significant upward. The digits of `μ`
are `1^β2`, while every digit of `P_v` and `V_v` is `1` or `2`. At the lowest
added position in (16), no carry arrives. To keep the output digit nonzero,
the next `β` digits of `P_v` must all be `1`. At the top digit of the shifted
`μ`, adding `2` forces the digit of `P_v` to be `2` and emits one carry. The
following digit of `P_v` must then be `1` to absorb that carry without
producing a zero.

Reading those positions in word order forces the binary factor

```text
0·1·0^β
```

inside `tagEncode β (v.map letter)·M`. This factor does not occur. Every
`1·0^β` begins either a `b` codeword or the final marker; in both cases its
preceding bit, when present, is the terminal `1` of another codeword. Hence
it is never preceded by `0`.

Thus (15) is impossible.

> **Distinguished-boundary β-shell theorem.** From projective boundary `1`, no
> finite nonterminal block in the `d=β` resonance can be followed by a pole.

Only the valuation-one discrepancy remains at this boundary. This theorem
does not constrain β-shell states reached later from the ordinary reset or
after several malformed transfers.

## Valuation-One Divisor Normal Form

The surviving target poles admit a finite-divisor parameterization. Let `z`
be a multi-role target block, abbreviate its positive ternary codes by `P,V`,
and suppose

```text
C=RP−HV,       v₃(C)=1.
```

An integral projective discrepancy `Δ`, with `3∤Δ`, reaches this pole exactly
when

```text
CΔ+3HμV=0.                                   (17)
```

Put

```text
g=gcd(P,V),       P=gp,       V=gv,       gcd(p,v)=1,
a=(Rp−Hv)/3.
```

The common factor `g` is a `3`-adic unit, so `a` is an integer not divisible
by `3`, and (17) reduces to

```text
aΔ=−Hμv.                                     (18)
```

Now set

```text
q=gcd(a,v).
```

Because `3` and `v` are coprime,

```text
q=gcd(3a,v)
 =gcd(Rp−Hv,v)
 =gcd(Rp,v)
 =gcd(R,v).
```

In particular, `q∣R`. Write

```text
a=qa₀,       v=qv₀,       r=R/q.
```

Then

```text
gcd(a₀,v₀)=gcd(r,v₀)=1,
a₀Δ=−Hμv₀,                                  (19)
rp=Hv₀+3a₀.                                  (20)
```

Consequently

```text
a₀∣Hμ,       v₀∣Δ.                          (21)
```

Thus every integral pole lies on one of finitely many divisor rays selected
by `q∣R` and `a₀∣Hμ`; only the positive parameter `v₀` remains unbounded.
This is an arithmetic normal form, not yet an exclusion theorem.

The distinguished value is completely rigid:

```text
Δ=H       ↔       P=V.                       (22)
```

For the forward implication, (19) and coprimality force
`v₀=1,a₀=−μ`. Equation (20), together with `H−3μ=R`, gives `rp=R=qr`;
hence `p=q`. Since `p` is coprime to `v=qv₀`, one gets `p=q=1`, and therefore
`P=V`. The converse follows by direct substitution in (17).

Equation (22) identifies one integral pole family exactly: `Δ=H` is not a
malformed target but the original terminal-match equation. The remaining
question is whether a Neary block can realize any of the other divisor rays.

The positive boundary branch is finite before any target analysis. When
`d=1`, deleting the common suffix leaves exactly `β+2` ternary digits on the
upper side. Thus

```text
Δ>0       ⇒       0<Δ<3^(β+2)=9ρ.           (23)
```

The corresponding projective value is

```text
y=h(1−3μ/Δ).
```

Every pole is positive, so `0<Δ≤3μ` is automatically safe. Only the finite
integer interval

```text
3μ<Δ<9ρ                                  (24)
```

can contribute a positive false pole. Negative `Δ` remains unbounded and is
the harder divisor-ray branch.

## Bounded Diagnostics

[`tools/explore_setter_projective.py`](../tools/explore_setter_projective.py) performs exact
bounded orbit search and finite-field shadowing. At `β=3`, body `bbcc`, it found:

```text
role-block length ≤10, one transfer before a pole: no collision
role-block length ≤3, three transfers:          677376 distinct states, no collision
role-block length ≤2, five transfers:           4160000 distinct states, no collision
target-block length ≤14, false integral unit pole: none
```

These are finite searches, not theorem evidence.

The same benchmark rejects a residue-only proof. With role-block length at most two, the
reachable states in the pole shells exhaust every unit class modulo `3⁴` after four transfers;
the valuation-one shell also exhausts every unit class modulo `3⁵`. Ordinary reductions modulo
the tested odd primes are still weaker: some exact side products make both pole coefficients
zero modulo each prime, so the projective shadow becomes indeterminate. A successful invariant
must retain pulse or suffix history, not merely the current projective residue.

The executable audit also checks equation (6), both reset representatives, and the
nonresonant valuation update (7) on every benchmark role block of length at most three. On
every arbitrary role word of length at most five, it independently compares the reverse
discrepancy scan with direct suffix cancellation and checks the bounds (11)–(12). It checks
the forbidden-factor consequence of (16) on the same words and verifies the two single-erasure
formulas symbolically for `3≤β≤8`. A streaming exact search checks the last diagnostic without
retaining all `4^12` target words.

## Promotion Boundary

The scaled transfer, pole-shell theorem, reset-zero peeling argument, integer carry recurrence,
two-transfer gate, distinguished-boundary suffix gate, reverse-discrepancy recurrence, and
bounded-fringe theorem, β-shell theorem, and divisor normal form are audited mathematics. The
bounded searches are computational diagnostics. No finite semantic quotient of the discrepancy
queue is known, no nonterminal divisor ray has been excluded uniformly, and arbitrary-depth
avoidance remains open.

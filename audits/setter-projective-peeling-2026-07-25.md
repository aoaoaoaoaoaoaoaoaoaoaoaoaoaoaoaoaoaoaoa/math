# Setter Projective Peeling Audit

**Date:** 2026-07-25
**Target:** the first malformed square-run transition in the five-state setter candidate
**Verdict:** reset-zero orbits survive one transfer; residue-only invariants saturate quickly

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

## Bounded Diagnostics

[`tools/explore_setter_projective.py`](../tools/explore_setter_projective.py) performs exact
bounded orbit search and finite-field shadowing. At `β=3`, body `bbcc`, it found:

```text
role-block length ≤10, one transfer before a pole: no collision
role-block length ≤3, three transfers:          677376 distinct states, no collision
role-block length ≤2, five transfers:           4160000 distinct states, no collision
```

These are finite searches, not theorem evidence.

The same benchmark rejects a residue-only proof. With role-block length at most two, the
reachable states in the pole shells exhaust every unit class modulo `3⁴` after four transfers;
the valuation-one shell also exhausts every unit class modulo `3⁵`. Ordinary reductions modulo
the tested odd primes are still weaker: some exact side products make both pole coefficients
zero modulo each prime, so the projective shadow becomes indeterminate. A successful invariant
must retain pulse or suffix history, not merely the current projective residue.

## Promotion Boundary

The scaled transfer, pole-shell theorem, and reset-zero peeling argument are audited
mathematics. The bounded searches are computational diagnostics. Arbitrary-depth avoidance
remains open.

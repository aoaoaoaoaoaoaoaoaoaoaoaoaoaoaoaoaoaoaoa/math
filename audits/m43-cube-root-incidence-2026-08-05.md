# M₄(3) cube-root incidence audit

**Date:** 5 August 2026

**Status:** exact algebra plus bounded symbolic computation; no `M₄(3)` theorem

**Target:** replace the toggle and rank-one separator of the paired four-state construction by
one generator without introducing a malformed zero word

## Reduction seam

The paired scalar construction has data matrices `G_b,G_c`, toggle `T`, terminal column `C`,
and boundary row `L`. Its coefficient-zero problem is undecidable. Mortality follows after
adjoining `CL`, but this gives four generators. The cube-root lane seeks one rational matrix
`S` and one mixed word `P(G_b,G_c,S)` such that

```text
S³ = T,                 rank P = 1,
im P = span(C),         row(P) has the source zero set,
```

and every zero product over `{G_b,G_c,S}` factors through the intended scalar witness.
Clearing denominators would then give three `4 × 4` integer matrices.

Use

```text
B = [[1,0,0,0], [0,0,1,1], [0,1,0,0], [0,0,1,-1]],
J = [[1,0,0], [0,1,0], [0,0,1], [0,0,-1]].
```

For either data letter, write

```text
G = [[1,l,u,e], [0,0,0,0], [0,0,a,0], [0,m,0,n]],
B⁻¹GB = JF,
F = [[1,u,e+l,l-e], [0,a,0,0], [0,0,(m+n)/2,(m-n)/2]].
```

In this basis `T = diag(I₃,-1)`. A rational order-three matrix `A` therefore gives a cube
root `S = B diag(A,-1) B⁻¹`.

## Universal monomial blade

Assume

```text
a u (l+e) (m-n) (m+n) (em-ln) ≠ 0.
```

Put

```text
p = 2(em-ln)/(m+n),
r = u(m-n)/(2a(l+e)),
q = 1/(pr),
A = [[0,0,p], [q,0,0], [0,r,0]].
```

Then `A³=I₃`. For `D=diag(A,-1)` and `Q=FDJ`, direct elimination gives

```text
det Q = 0,              e₂(Q) = 0,
rank Q = 2,             rank Q² = 1.
```

Consequently

```text
S³ = T,
B⁻¹(GSGSG)B = JQ²F,
rank(GSGSG) = 1.
```

This closes the bare incidence problem uniformly for every nondegenerate paired data matrix.
It does not align the resulting rank-one column and row with the source boundaries.

For the diagnostic instance `β=3`, body `bb`, ternary digits `1,2`, and desynchronizing word
`10`, the `b` data matrix gives

```text
A = [[0, 0, -7252/365],
     [-918088242345/8363202087968, 0, 0],
     [0, 1153226984/2515310253, 0]].
```

Normalizing the reduced punctuation column to third coordinate `-1` gives

```text
[159800529787471/591830317260,
 234325395142478667/761051390005088,
 -1],
```

whereas the required reduced terminal column is

```text
[8448548, 9565938, -1].
```

The physical punctuation row, normalized at its first coordinate, is

```text
[1,
 67561840204/3597075,
 427873228206925288/34003268235,
 41475852304/2622267675].
```

The rule-side desynchronization seam requires `b=9c+7a`; the normalized defect is

```text
-156147836563313239853/1379021433975.
```

The row has the safe length sign and nonzero self-incidence, and the core does not annihilate
the terminal column. Thus the failure is boundary alignment rather than degeneration.

An exact breadth-first orbit check found no target column and no safe seam row after at most
four additional data contexts, allowing every residue modulo six. An independent resultant
scan found no nonzero pair of rational digit weights that aligns the monomial `b` column for
any ternary-style desynchronizing word of length at most twelve and any radix from 3 through
100. These are bounded computational exclusions, not uniform impossibility theorems.

## Incidence census

The same diagnostic instance was used to classify every three-data pattern

```text
G_z S^s G_y S^r G_x,
```

with `x,y,z∈{b,c}` and `r,s∈{1,2,4,5}`. The order-three condition, target-column incidence,
rule seam, nonzero row, and nonzero self-incidence were imposed exactly over `ℚ`.

All patterns containing two distinct `(letter,residue)` core types were either empty over the
algebraic closure or zero-dimensional with no rational solution. A rational solution would
give a rational saturation coordinate; exact modular root sieves excluded that coordinate in
every zero-dimensional case. Only literal repetitions `Q_{x,r}²` left positive-dimensional
components.

For `Q_{b,2}²`, the rationally parametrized cubic component is the annihilator branch

```text
Q_{b,2} C = 0.
```

A right context produced exact rank-one, column-aligned, seam-aligned points on this component,
including one with the safe length sign. They are invalid: if `P` has image `span(C)`, then

```text
Q_{b,2}P = 0,
```

so the physical family is mortal independently of the source instance. Self-incidence
`P²≠0` does not detect this defect.

After saturating by `Q_{b,2}C≠0`, all 44 four-data patterns formed by two copies of
`(b,2)` and one additional core type, in every placement and with either terminal letter,
had no rational point on the exact slice `A₃₂=0`. The zero-dimensional degrees ranged from 7
to 38. The unsliced nonannihilating varieties remain open.

## Mandatory converse guard

For any proposed punctuation `P=CL`, every legal context must satisfy

```text
UC ≠ 0,                 LV ≠ 0
```

unless that context is itself proved to encode a valid source witness. Otherwise `UP=0` or
`PV=0` is an unconditional mortality witness. Candidate screening must therefore precede the
all-word proof with the twelve one-step tests `Q_{x,r}C≠0` and their row-dual analogues for
`x∈{b,c}` and `r mod 6`, then classify longer rank-dropping fragments.

## Exact frontier

The live matrix problem is no longer rank-one existence. It is to align both boundaries of
the universal monomial blade, uniformly in the varying Neary body, while retaining all local
nonannihilation guards; or to prove that this blade cannot do so and replace it with another
open-residue macro. Any successful candidate still owes an arbitrary-word normal form over
`{G_b,G_c,S}`. The diagnostic computations alone support no undecidability claim.

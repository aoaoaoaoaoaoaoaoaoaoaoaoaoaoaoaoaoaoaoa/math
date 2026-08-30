# Congruence-Blind Free Orbit Audit

Date: 2026-08-30

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

There is an explicit free subgroup of `GL₂(ℤ)` with a trivial-stabilizer rational projective
orbit and a rational target outside that orbit, although the target lies in the orbit modulo
every positive integer. Thus no family of ordinary integral congruence quotients decides even
this free, generic projective-incidence no-instance.

This is an obstruction to congruence separation, not a decision or undecidability theorem for
`GPI₂`, `M₂(3)`, or `M₃(2)`.

## Rational No-Instance

Let

```text
A=[[1,3],[0,1]],       B=[[1,0],[3,1]],
p=[1:1],               q=[10:13].
```

In the affine coordinate `t=x/y`, use the disjoint ping-pong chambers

```text
U={∞}∪{t:|t|>1},       L={t:|t|<2/3}.
```

For every nonzero integer `e`,

```text
A^e(L)⊆U,              B^e(U)⊆L.
```

The source `p=1` and target `q=10/13` lie in the gap outside both chambers. A reduced nonempty
word sends `p` into the chamber of its first factor, so it cannot fix `p` and cannot send `p`
to `q`. Therefore

```text
⟨A,B⟩≅F₂,       Stab(p)=1,       q∉⟨A,B⟩p.             (1)
```

`CongruenceBlindOrbit.upper_maps_lower` and `lower_maps_upper` check the chamber estimates.
`reducedWord_maps_source` lifts them through the free-product normal form.
`shearRepresentation_injective`, `sourcePoint_stabilizer_trivial`, and
`targetPoint_not_reachable` prove all three conclusions in (1).

## Universal Congruence Witness

For a modulus `N≥1`, write

```text
N=3^k m,       gcd(m,3)=1.
```

Put

```text
r=1                       if k=0,
r=3^(k−1)                 if k>0,
c=3r.
```

Choose integers `d,n` satisfying

```text
cd≡1 (mod m),
n=0                       if k=0,
13n≡−1 (mod 3^(k−1))      if k>0.
```

Both inverses exist. Set `x=cd` and `a=1+3n`. Then

```text
x≡1 (mod m),       x≡0 (mod 3^k),
13a≡10 (mod 3^k).                                  (2)
```

The five-factor word

```text
w_N=B^(rd) A^(3rd) B^(2rd) A^(−3rdn) A^n           (3)
```

has bridge matrix

```text
H(x,n)=L(x)U(3x)L(2x)U(−3xn)U(3n).
```

On the `m` component, `x=1` and direct multiplication gives

```text
H(1,n)p=q.                                           (4)
```

On the `3^k` component, `x=0` and

```text
H(0,n)p=[a:1]=[10:13]                                (5)
```

by (2). Chinese remaindering (4) and (5) gives a unit `u_N` modulo `N` such that

```text
w_N p=u_N q (mod N).                                 (6)
```

Hence `q` lies in the projective orbit of `p` modulo every `N`.

## Checked CRT Algebra

The finite-modulus calculation is isolated from number-theory bookkeeping. For an idempotent
selector `x` in any commutative ring, Lean proves

```text
H(x,n)p=xq+(1−x)[1+3n:1].                            (7)
```

This is `bridgeMatrix_idempotent_mulVec_source`. If a scalar `u` is one on the `x` component
and equals `13⁻¹` on its complement, while `13(1+3n)=10` there, then
`bridgeMatrix_idempotent_projective_target` turns (7) into `H(x,n)p=uq`.

`bridgeWord` is the literal free-product word (3), and
`shearRepresentation_bridgeWord` checks that its rational matrix is `H(3rd,n)`. The existence
of `d`, `n`, and the CRT scalar for each `N` is the elementary audited assembly above; it is not
yet quantified by one end-to-end `ZMod N` Lean declaration.

## Scope

The theorem says that one explicit orbit no-instance is invisible to all integral congruence
quotients, with the witnessing word allowed to depend on the modulus. It does not say that the
whole orbit is dense in any `p`-adic projective line, nor that arbitrary `GPI₂` instances are
congruence-blind. It also does not obstruct representations that preserve positive syntax,
Archimedean order, heights, or unbounded carry data.

The consequence for the joint `M₂(3)`/rank-`(2,2)` artery of `M₃(2)` is exact: a decision proof
cannot rely on eventual separation of every no-instance by ordinary reductions modulo `N`, even
after restricting to a free group action with trivial source stabilizer.

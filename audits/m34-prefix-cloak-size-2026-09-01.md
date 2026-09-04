# M₃(4) Prefix-Cloak Size Obstruction Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `ea4301c` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimePrefixCloakNoGo.lean`](../MatrixMortality/MixedPrimePrefixCloakNoGo.lean)
**Certificate:**
[`certify_mixed_prime_prefix_cloaks.py`](../tools/certify_mixed_prime_prefix_cloaks.py)

## Verdict

The prefix-cloaked comparator from `G3-S21` cannot occupy an arbitrarily deep address suffix of
one fixed physical `bcbc` fork. If

```text
yzxyx = L·expandAddress(u),       xzyxy = R·expandAddress(u),
```

then exact endpoint semantics forces

```text
2|u| < |x|+|y| < |L|.
```

The first inequality is a terminal-overlap obstruction. If the common address suffix were at
least `|x|+|y|` letters long, it would contain both final data blocks `yx` and `xy`. They are
equal-length suffixes of one word, hence `yx=xy`. Lean independently proves that the physical
data macros of an exact endpoint code cannot commute: commutation makes each fix the other's
unique rational fixed point, contrary to their forced fixed-point separation.

The second inequality follows from the exact length equation

```text
2|x|+2|y|+|z| = |L|+2|u|
```

and the formally forced nonemptiness of the toggle `z`. Thus every fixed prefix cloak admits
only finitely many physical address depths. A source-uniform construction must lengthen or vary
the cloak with the encoded source, or abandon this literal prefix form.

The exact finite certificate then rejects all `23` base pump cloaks from `G3-S16`, in both branch
orientations. The formal size gate leaves `77,280` positive length geometries and maximum address
depth `14`. Each geometry is a finite parity-equation system for the letters of `x,y,z` and the
binary address digits. Every system contains a contradiction; none has a witness.

## Formal Chain

Lean proves four reusable statements.

1. Two equal-length suffixes of one common word are equal. Applied to the fork endings, any common
   suffix of length at least `|x|+|y|` forces `xy=yx`.
2. Exact endpoint semantics forces `x` and `y` nonempty with distinct fixed points. Literal
   commutation would make `y` fix the unique fixed point of `x`, then uniqueness for `y` would
   identify the two fixed points.
3. The common aligned address therefore has raw length strictly below `|x|+|y|`.
4. The reduced-word length identity and `|z|>0` force `|x|+|y|<|L|`.

No affine-kernel presentation, pump schema, or finite search enters the formal theorem.

## Certificate Boundary

The certificate uses the `23` exact base relations already certified by
`certify_mixed_prime_pump_families.py`. For each base pair and its swap it enumerates every
positive triple `( |x|,|y|,|z| )` and address depth satisfying both the formal strict bound and
the physical length equation. It then solves the literal fork equations by parity union-find:
`D=0`, `T=1`, and an address macro is `(b,b⊕1)`. The canonical payload digest is

```text
d9767d3c18b5dfab2fe6add1c0735f347f001df8d221336331c1fa639e1bda0a
```

This is a complete rejection of the `23` base **prefix** cloaks only. The computation does not
reject their pumped descendants, the explicit odd family, suffix cloaks, unequal address
interiors, interleaved addresses, source-varying cloaks, or a separate two-offset terminal
channel. The universal Lean size bound applies to every prefix cloak, but does not itself forbid
a cloak family whose length grows with the address.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Exact endpoint data words commute | rejected | Lean fixed-point uniqueness |
| A common prefix-cloak address may reach the final data boundary | rejected | Lean suffix overlap |
| Every physical prefix cloak obeys `2|u|<|x|+|y|<|L|` | promotion | Lean |
| One fixed prefix cloak carries unbounded address depth | rejected | formal strict bound |
| Any of the `23` base pump pairs realizes a prefix-cloaked fork | rejected | exact complete certificate |
| Every pumped or source-varying prefix cloak is impossible | open | outside the finite certificate |
| A suffix cloak is impossible | open | the terminal overlap is asymmetric |
| `M₃(4)` follows | rejected | pumped/source-varying and suffix realizations, then converse, remain |

## Master Delta

```text
DEAD: every fixed prefix cloak as an unbounded address carrier.
DEAD: all 23 base pump cloaks as physical prefix-cloaked forks.
MANDATORY PREFIX ESCAPE: a source-varying cloak longer than the address boundary.
OTHER SURVIVORS: suffix cloak, unequal/interleaved interiors, or separate two-offset routing.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, exact certificate replay, Ruff, ty, and forbidden-aperture scan pass. The
formal source SHA-256 is recorded after the final checked build.

```text
89f2c01fc7b3916eac3ecccc2005b29d6e52ee2ef03ed221e8d8650b166a4e1d  MixedPrimePrefixCloakNoGo.lean
```

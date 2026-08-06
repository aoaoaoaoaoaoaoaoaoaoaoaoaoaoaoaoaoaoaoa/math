# Rational Phase-Fracture Audit

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a74b64e-5054-83ea-989c-cbfac7f6fae8)

## Enemy Lock

```text
MASTER: prove M₃(4) undecidable.
VICTORY: a computable four-generator 3 × 3 mortality reduction with an arbitrary-word converse.
LIVE OBSTRUCTION: construct or exclude a history-sensitive three-state same-zero realization of
                  the paired scalar zero language.
KILLED LANES: exact three-state realization; nonerasing three-letter role macros; rational maps
              from the checked phase-local suffix point to the compressed suffix point.
```

## Verdict

The external argument is mathematically sound at its stated boundary:

> On a paired instance with a zero, no three-state same-zero realization can have its compressed
> suffix point rationally determined by the checked local suffix point and phase.

The statement permits nonlinear rational maps, singular target generators, curve or line images,
and arbitrary malformed control words. It does not exclude a representation whose target suffix
point retains word history absent from the checked four-state suffix vector.

Lean now checks the finite and zero-language-critical spine. It does not yet check the complete
arbitrary-rational-map theorem. The unformalized boundary is stated explicitly below; the broad
result therefore remains `audited`, not `formalized`.

## Reconstructed Algebra

Use local coordinates `(z,x,h)` obtained by swapping the two payload coordinates of the
side-normal Neary representation. The erase and rule roles are

```text
E_b = [[1,u, 1], [0,a,0], [0,0, 3]],
R_b = [[1,u,25], [0,a,0], [0,0,27]],
E_c = [[1,2, 1], [0,3,0], [0,0, 3]],
R_c = [[1,2, v], [0,3,0], [0,0,3ρ]].
```

Here `a=3^(β+2)`, `u=ternaryCode(tagCode β b)`,
`ρ=3^(|tagEncode β body|+2)`, and

```text
v = 18·3^|tagEncode β body| + 9·ternaryCode(tagEncode β body) + 7.
```

The declarations `PhaseRigidity.localRole_eq`, `ruleCRho_eq`, and
`nearySideLowerC_eq_encoded` check these normal forms against the existing compiler.

On the affine chart

```text
r=h/x,             t=(z-x-h/2)/x,
d=u+1-a=(3-q)/2,   q=3^(β+1),
```

Lean checks

```text
E_c(t,r) = (t/3,r),
E_b(t,r) = ((t+d)/a,(3/a)r),
d ≠ 0 for β≥3.
```

The exact discrepancy matrices are

```text
E_b⁻¹R_b = [[1,0,16], [0,1,0], [0,0,9]],
E_c⁻¹R_c = [[1,0,v-ρ], [0,1,0], [0,0,ρ]].
```

Their quotient scales the private direction by `ρ/9=3^N≠1`. The coefficient mixing that
direction back under `E_c` has numerator

```text
3ρ+23-2v = 9(1-3^N-2w) < 0.
```

These identities are checked by `erase_inverses`, `phase_discrepancies`,
`discrepancy_quotient`, `ruleCRho_div_nine_ne_one`, and `ruleCMixing_ne_zero`.

## Dense-Orbit Audit

The terminal point has `r₀≠0`. Under repeated `E_b`,

```text
r_m=(3/a)^m r₀,
t_m=t_*+a^(-m)(t₀-t_*),   t_*=d/(a-1)≠0.
```

Thus the `r_m` are distinct and at most one `t_m` vanishes. For every other `m`, repeated `E_c`
gives `(3^(-n)t_m,r_m)`. A polynomial vanishing on the whole grid first vanishes identically in
`t` at infinitely many `r_m`, then has every coefficient vanish identically in `r`. The
erase-phase suffix orbit is therefore Zariski dense. A trailing toggle supplies the initial erase
phase without changing the local terminal vector; a leading toggle supplies the rule phase.

This validates extending every reachable-point equivariance equation to a rational-map identity.
No ordering reversal or intended-word assumption is used.

## Image Branches

If the erase image is not contained in a line, singular `H_b` or `H_c` would force it into a
line. Both target matrices are therefore invertible, and cancellation gives invariance under the
discrepancy quotient. In coordinates diagonalizing that quotient, every component ratio is
invariant under `(U,W)↦(U,3^N W)`, hence lies in `ℚ(U)`. The nonzero `E_c` mixing coefficient then
forces the projective map to be constant, contradicting the branch hypothesis.

If the image is a line, its target actions are Möbius transformations. The two source
commutators are exactly

```text
CBC⁻¹B⁻¹ : (t,r) ↦ (t-2d/(3a),r),
CPC⁻¹P⁻¹ : (t,r) ↦ (t-(8/9)r,r).
```

The declarations `erase_commutator` and `discrepancy_commutator` check both signs and
multiplication order. For a linear-fractional phase map, Lean proves the rigidity directly:
after equivariance is translated into preservation of its two-dimensional numerator-denominator
pencil, `neary_commutator_pencil_forgets_t` proves that the pencil forgets `t`. If one form had a
nonzero `t` coefficient, the two translation differences would put both `1` and `r` in the
pencil, exhausting its dimension and excluding that `t` term.

For an arbitrary rational line map, the audited proof uses the stronger two-translation lemma.
A rational function semiconjugating a nonzero constant translation to a Möbius map is either
independent of `t` or, after a target conjugacy, affine in `t`. The radial translation rules out
the affine case because its target translation would have the nonconstant parameter `cr`.
Therefore every line or point image forgets `t`, and `Φ_E∘E_c=Φ_E`.

## Terminal Fracture

Lean checks the step that consumes all geometric rigidity. Prefixing a toggle preserves the
paired coefficient and can normalize any suffix to erase phase. Prefixing `c` then decodes an
erase-`c` role. Its upper and lower words begin respectively with `true` and `false`, so its
coefficient cannot vanish, even on malformed controls.

Consequently, a same-zero representation cannot make the target columns before and after that
erase-`c` prefix proportional. The dimension-free theorem is

```text
no_zero_of_erase_c_projective_identification
```

and directly contradicts a zero of the paired series. This removes empty-word, toggle-only,
zero-column, and intended-language loopholes from the final implication.

## Formal Boundary

The following parts are kernel-checked:

- the four local role matrices and all scale identities;
- both affine erase actions and the nonzero translation defect;
- both discrepancy matrices, their quotient, and its nontrivial scale and mixing;
- both exact commutators;
- two-translation rigidity for invariant two-dimensional pencils of affine forms;
- phase normalization, erase-`c` nonvanishing, and the final same-zero contradiction.

The following parts remain pen-and-paper audited:

- the Zariski-density theorem for the reachable phase orbit;
- extension from reachable-point equality to rational-map equality;
- the fixed-field calculation for arbitrary rational functions under `W↦3^N W`;
- two-translation rigidity for arbitrary rational, rather than linear-fractional, line maps;
- their assembly into the full no-rational-state-map theorem.

No publication or formalization ledger may describe that last theorem as Lean-checked until these
four function-field steps are formalized or replaced by a finite algebraic certificate.

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: every same-zero compression whose suffix point is a rational function of the checked
         phase-local suffix state; the invariant-pencil rigidity core and terminal consumer are
         additionally kernel-checked.
REMAINS: a genuinely history-sensitive three-state realization, equivalently a phase graph
         closure that is not the graph of a rational map; or a different direct/source compiler.
DISTANCE: prove that every three-state same-zero phase correspondence is generically
          single-valued, or construct and mortality-lift a valid multivalued survivor.
```

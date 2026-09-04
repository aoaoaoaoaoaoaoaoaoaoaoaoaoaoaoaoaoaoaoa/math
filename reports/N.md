Verdict: obstructed

Cells affected: `M₂(3)` and the rank-`(2,2)` artery of `M₃(2)` remain open; the proposed additive mixed-radix tape encoding is closed.

Lean: `MixedRadixTape.unequalTailScaling_matrix_eq_zero`: `[propext, Classical.choice, Quot.sound]`. `AxiomAudit.lean` adds exactly this `#print axioms` entry against `verification/axioms.txt`.

Statement: Let `Realizes M z z′` mean that `M=[[a,b],[c,d]]` obeys `az+b=z′(cz+d)`. Fix source and target markers `s,t`, nonzero tail perturbations `x,y`, and scales `λ,μ` with `λ≠0` and `λ≠μ`. If one matrix realizes `s↦t`, `s+x↦t+λx`, `s+2x↦t+2λx`, and `s+y↦t+μy`, then `M=0`. In the additive balanced mixed-radix code `E_q(L,R)=s_q+L+R`, a right head move rescales the independently variable binary and ternary tails by `(λ,μ)=(2,3)`; a left move uses `(1/2,1/3)`. Taking `x=2^k` and `y=3^−ℓ` beyond any prescribed finite window proves that no nonzero `PGL₂(ℚ)` letter acts locally. Signed redundancy cannot help: these witnesses use only digits `0,1`.

If obstructed: the four cross-multiplied constraints have coefficient determinant

```text
2 λ x³ y (λ−μ) ≠ 0.
```

Thus unequal-radix boundary motion necessarily propagates through an unbounded digit region. Its aggregate manifestation is K's unbounded carry, which blocks a fixed-carry decision automaton; its local manifestation blocks N's digit-rewrite Turing tape. This is the common structural obstruction met by both routes through `GPI₂`/`M₂(3)`, not a decision or undecidability theorem.

DAG metadata: `N-O01` unequal-radix projective locality wall — obstruction / N from `K-O01` and `R32-S41` / exact symbolic elimination plus Lean / active.

Next (max 3 bullets)

- Any successor must exploit intrinsically nonlocal carry dynamics or abandon the additive one-coordinate tape boundary.

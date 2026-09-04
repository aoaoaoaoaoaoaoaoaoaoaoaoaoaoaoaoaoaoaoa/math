# K. Two-dilation pointed expansion

Verdict: obstructed

Cells affected: none closed. The proposed bounded-carry decision of `GPI₂`, `M₂(3)`, and the rank-`(2,2)` artery of `M₃(2)` fails; all remain open.

Lean: none, as required after the unbounded-carry falsifier fired; hence there are no declarations or `#print axioms` lines. No new Lean was run after the stop instruction.

Statement: Let `A(z)=2z`, `B(z)=(2z−1)/3`, `P={A,B}*`, and `K=Stab_Γ₆(1)`. In the established normal form `w(z)=(2ⁿz−m_w)/3ᵏ`, the letter recursion is `m↦2m` for `A` and `m↦2m+3ᵏ` for `B`. Put `kᵢ=max{j:3ʲ≤2ⁱ}` and choose the `i`th letter to be `B` exactly when `kᵢ=k_(i−1)+1`. Then `kₙ≥⌊n/2⌋`, and a `B` at position `i` contributes `tᵢ=2^(n−i)3^(k_(i−1))` to `m_w`, with `2^(n−1)/3<tᵢ<2^(n−1)`. After clearing `3^kₙ` to denominator `6^kₙ`, let `L` be least with `6^L≥2^(n−1+kₙ)`. Every scaled summand lies below digit `L`, but their carry into that digit is

```text
Cₙ = ⌊2^kₙ m_w / 6^L⌋ ≥ ⌊kₙ/18⌋ → ∞.
```

If obstructed: **the `2`/`3` carry is UNBOUNDED**, already on this monotone, `1`-thin family in `P⊂PK`. CCZ's fixed-arity componentwise-addition step therefore does not extend to two dilations with one bounded carry. This proves neither undecidability nor nonexistence of a richer redundant, asynchronous, or spatially distributed representation; the `PK` membership problem remains open. The growing carry is a candidate information store, not yet a known undecidability mechanism.

DAG metadata: `K-O01` balanced mixed-radix carry blow-up — obstruction / `R32-S41` and CCZ20 / exact symbolic computation / active.

Next:
- Test redundant signed expansions whose finite annotation cannot project to the failed aggregate carry.
- Prove decidable emptiness separately for any genuinely two-dimensional local model; it is not automatically Presburger.
- Test whether the growing carry supports a sound all-word computation encoding.

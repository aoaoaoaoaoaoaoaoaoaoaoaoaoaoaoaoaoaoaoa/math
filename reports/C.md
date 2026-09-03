Verdict: discovered

Cells affected: `M₄(2)^(4,2)` reduced, not decided; upward closures remain open. `(4,1)` reduces to external order-four Skolem decision.

Lean: `ReturnFamily.rankOnePair_isMortal_iff`; `FourModeArtery.fourModePair_isMortal_iff_returnFamily`; `FourModeArtery.railbreakerCut_rank`; `FourModeArtery.railbreakerAmbient_isUnit`; `FourModeArtery.railbreakerReturn_eq`; `FourModeArtery.railbreaker_affineWait`; `FourModeArtery.railbreaker_orbit_injective`. Each `#print axioms`: `[propext, Classical.choice, Quot.sound]`; axiom diff: seven entries.

Statement: For unit `A : M₄(ℚ)` and compatible `U,V`, `{A,UV}` is mortal iff `n↦VAⁿU` is mortal. For nonzero `r,q`, the formalized rank-two cut with `A=diag(1,1,q,rq)` has `VAⁿU=[[r,-r(rq)ⁿ],[0,1-qⁿ]]`; if `qⁿ≠1`, it sends `[rⁿ:1]` to `[rⁿ⁺¹:1]`, injectively when `r>1`.

| Record | Three-mode hypothesis | Status |
|---|---|---|
| R32-O06 | Univariate transfer/divisibility | Fourth modes break it. |
| R32-O15 | Five-term Laurent support/common reduction | Fourth modes break it. |
| R32-O18 | Reciprocal ready-tail identity | Fourth modes break it. |

If discovered: finite modes plus one rational projective state do not imply the `M₃(2)` periodic wall.

DAG metadata: reduction / MM-C06 / Lean / validated; railbreaker / C / Lean / discovered; register tests / C / exact algebra / obstructed.

Next (max 3 bullets)

- Find a center-preserving zero test.

## C2

Verdict: obstructed

Cells affected: `M₄(2)^(4,2)` only; no closure.

Lean: `AlternatingReaderPoison.integralAffine_negative_hasValue`; `AlternatingReaderPoison.integralAffine_negative_forward`. Each `#print axioms`: `[propext, Classical.choice, Quot.sound]`; axiom diff: two entries.

Statement: For prime `π`, if the leading and denominator coefficients of `(az+b)/d` are `π`-units, `b=0` or `vπ(b)≥0`, and `vπ(z)<0`, then the output has valuation `vπ(z)<0`. The poison chamber is forward-invariant.

If obstructed: Over `ℤ₍₃₎`, write `Mₙ=[[aₙ,bₙ],[cₙ,dₙ]]`. For modes `λᵢ`, fixing infinity requires `cₙ=ΣᵢV₁ᵢUᵢ₀λᵢⁿ∈3ℤ₍₃₎`; unit determinant then requires `dₙ=ΣᵢV₁ᵢUᵢ₁λᵢⁿ∈ℤ₍₃₎×`. A pole `x=2ⁿ` instead gives `dₙ=-cₙx` and `det Mₙ=-cₙ(aₙx+bₙ)`. Since `x` is a 3-unit, `3∣cₙ` forces `3∣dₙ`, contradiction. Thus the `a`-reader fails before mode selection; tasks 2–3 do not open. Repair requires a non-pole exact zero test or storing `b` away from infinity.

DAG metadata: poison / C2 / Lean / validated; affine-pole incompatibility / C2 / exact algebra / obstructed.

Next (max 3 bullets)

- Restrict future searches to zero tests stabilizing infinity in `GL₂(ℤ₍₃₎)`.

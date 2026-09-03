import MatrixMortality.ReturnGuard

/-!
# Two-vertex plane mode obstruction

Embedding a two-coordinate ReturnGuard transfer in the projective plane adds a spectator
coordinate. The reciprocal and expanding coefficients remain rank one, but the constant
coefficient has a nonzero `2 × 2` minor and therefore cannot pass through one diagonal mode.

For the proposed unscaled two-reader allocation, the four nonconstant modes
`2⁻¹, 2^(d-1), 3⁻¹, 3^(e-1)` are distinct. They each consume one ambient coordinate, while
the shared constant eigenvalue consumes at least two. Thus the prescribed pair of embedded
readers requires ambient dimension at least six before any cross edge is imposed.
-/

namespace MatrixMortality.TwoVertexPlaneNoGo

open scoped Matrix

/-- An `x`-reader in `[x : y : z]`, with `y` carried as a spectator. -/
def xReaderTransfer
    (center reset low high : ℚ) : Square (Fin 3) ℚ :=
  !![center * low + ReturnGuard.drift center reset * high, 0,
      -center - ReturnGuard.drift center reset * high;
     0, 1, 0;
     low, 0, -1]

/-- Coefficient of the constant exponential in an embedded `x`-reader. -/
def xReaderConstant (center : ℚ) : Square (Fin 3) ℚ :=
  !![0, 0, -center;
     0, 1, 0;
     0, 0, -1]

/-- Exact reciprocal/expanding/constant decomposition of the embedded reader. -/
theorem xReaderTransfer_eq_modes
    (center reset low high : ℚ) :
    xReaderTransfer center reset low high =
      low • !![center, 0, 0;
               0, 0, 0;
               1, 0, 0] +
      high • !![ReturnGuard.drift center reset, 0,
                  -ReturnGuard.drift center reset;
                 0, 0, 0;
                 0, 0, 0] +
      xReaderConstant center := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xReaderTransfer, xReaderConstant]
  all_goals ring

/-- One diagonal mode contributes an outer product, but the constant reader coefficient has
minor `[[1, 0], [0, -1]]`. Hence one constant mode cannot carry an embedded reader. -/
theorem xReaderConstant_ne_vecMulVec
    (center : ℚ) (column row : Fin 3 → ℚ) :
    xReaderConstant center ≠ Matrix.vecMulVec column row := by
  intro equality
  have entry_one_one := congrFun (congrFun equality 1) 1
  have entry_one_two := congrFun (congrFun equality 1) 2
  have entry_two_two := congrFun (congrFun equality 2) 2
  simp [xReaderConstant, Matrix.vecMulVec_apply] at entry_one_one
  simp [xReaderConstant, Matrix.vecMulVec_apply] at entry_one_two
  simp [xReaderConstant, Matrix.vecMulVec_apply] at entry_two_two
  rcases entry_one_two with column_zero | row_zero
  · rw [column_zero] at entry_one_one
    norm_num at entry_one_one
  · rw [row_zero] at entry_two_two
    norm_num at entry_two_two

end MatrixMortality.TwoVertexPlaneNoGo

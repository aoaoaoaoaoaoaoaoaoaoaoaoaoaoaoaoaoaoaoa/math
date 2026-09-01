import MatrixMortality.ParabolicFirstBOneClosure

/-!
# The bounded valuation-density funnel at outer wait 211

This module records the exact 3-adic and density envelopes used in the unresolved
first-`b`-after-one-`c` chamber.  Its finite certificate proves that the envelopes leave
exactly the ten triples already extinguished by `ParabolicFirstBOneClosure`, all with the
tail's first `b` at position zero.
-/

namespace MatrixMortality.ParabolicBlade

/-- Exact divisibility by a power of `3`, but not by the next power. -/
def ExactThreeOrder (value : ℤ) (order : Nat) : Prop :=
  (3 : ℤ) ^ order ∣ value ∧ ¬(3 : ℤ) ^ (order + 1) ∣ value

/-- The six universal `U`-coordinate roots for trailing runs of length at most five. -/
def firstBOneX211RootResidue (h : Nat) : ℤ :=
  match h with
  | 0 => 36
  | 1 => 1746
  | 2 => 315
  | 3 => 15705
  | 4 => 2826
  | _ => 141336

/-- The exact bounded 3-adic allocation forced by the SFFT product equation. -/
def FirstBOneX211ValuationEnvelope (h y z : Nat) : Prop :=
  ∃ uOrder vOrder : Nat,
    h + 3 ≤ uOrder ∧ uOrder + vOrder = h + 16 ∧ vOrder ≤ 13 ∧
      ((uOrder < h + 7 ∧
          ExactThreeOrder ((y : ℤ) - firstBOneX211RootResidue h) uOrder) ∨
        (h + 7 ≤ uOrder ∧
          (3 : ℤ) ^ (h + 7) ∣ (y : ℤ) - firstBOneX211RootResidue h)) ∧
      ((vOrder = 13 ∧ z = 420724) ∨
        (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))

/-- Positive affine `z` factor in the x=211 rest-core equation. -/
def firstBOneX211Q (z : Nat) : ℤ :=
  465621956 * z + 42879529

/-- Positive bilinear coefficient of the suffix complement at x=211. -/
def firstBOneX211J (y z : Nat) : ℤ :=
  620717828832 * y * z + 58005064872 * y +
    133690369309176 * z + 12496984445436

/-- Scale coefficient in the normalized x=211 rest-core equation. -/
def firstBOneX211A (y z : Nat) : ℤ :=
  729 * (72 * y - 9) * firstBOneX211Q z

/-- Finite-scale correction in the normalized x=211 rest-core equation. -/
def firstBOneX211B (y z : Nat) : ℤ :=
  (8 * y - 9) * firstBOneX211Q z

/-- Cleared exact density inequalities for first-`b` position `j` and trailing run `h`. -/
def FirstBOneX211DensityEnvelope (h j y z : Nat) : Prop :=
  let p : ℤ := 3 ^ j
  let T : ℤ := 3 ^ (j + 5 + h)
  (39 * (81 * p) + 13) * firstBOneX211J y z ≤
      81 * p * firstBOneX211A y z ∧
    242 * p * (T * firstBOneX211A y z - firstBOneX211B y z) ≤
      T * (39 * (242 * p) + 39) * firstBOneX211J y z

private theorem firstBOneX211_z_order_twelve (z : Nat) (bound : z < 3 ^ 13)
    (shell : ExactThreeOrder ((z : ℤ) - 420724) 12) :
    z = 952165 ∨ z = 1483606
    := by
  norm_num [ExactThreeOrder] at shell
  omega

private theorem firstBOneX211_z_order_eleven (z : Nat) (bound : z < 3 ^ 13)
    (shell : ExactThreeOrder ((z : ℤ) - 420724) 11) :
    z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    := by
  norm_num [ExactThreeOrder] at shell
  omega

private def FirstBOneX211ZTenA (z : Nat) : Prop :=
  z = 7381 ∨ z = 125479 ∨ z = 184528 ∨ z = 302626 ∨ z = 361675 ∨ z = 479773

private def FirstBOneX211ZTenB (z : Nat) : Prop :=
  z = 538822 ∨ z = 656920 ∨ z = 715969 ∨ z = 834067 ∨ z = 893116 ∨ z = 1011214

private def FirstBOneX211ZTenC (z : Nat) : Prop :=
  z = 1070263 ∨ z = 1188361 ∨ z = 1247410 ∨ z = 1365508 ∨ z = 1424557 ∨ z = 1542655

private theorem firstBOneX211_z_order_ten (z : Nat) (bound : z < 3 ^ 13)
    (shell : ExactThreeOrder ((z : ℤ) - 420724) 10) :
    FirstBOneX211ZTenA z ∨ FirstBOneX211ZTenB z ∨ FirstBOneX211ZTenC z := by
  norm_num [ExactThreeOrder, FirstBOneX211ZTenA, FirstBOneX211ZTenB,
    FirstBOneX211ZTenC] at shell ⊢
  omega

private theorem firstBOneX211_shallow_h0_v13
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 36) 3)
    (z_cases :
      z = 420724
    )
    (density : FirstBOneX211DensityEnvelope 0 j y z) :
    FirstBOneX211Candidate 0 y z ∧ j = 0 := by
  rcases z_cases with rfl
  interval_cases j <;>
  norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
  omega

private theorem firstBOneX211_shallow_h0_v12
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 36) 4)
    (z_cases :
      z = 952165 ∨ z = 1483606
    )
    (density : FirstBOneX211DensityEnvelope 0 j y z) :
    FirstBOneX211Candidate 0 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h0_v11
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 36) 5)
    (z_cases :
      z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    )
    (density : FirstBOneX211DensityEnvelope 0 j y z) :
    FirstBOneX211Candidate 0 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h0_v10_a
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 36) 6)
    (z_cases : FirstBOneX211ZTenA z)
    (density : FirstBOneX211DensityEnvelope 0 j y z) :
    FirstBOneX211Candidate 0 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenA at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h0_v10_b
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 36) 6)
    (z_cases : FirstBOneX211ZTenB z)
    (density : FirstBOneX211DensityEnvelope 0 j y z) :
    FirstBOneX211Candidate 0 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenB at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h0_v10_c
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 36) 6)
    (z_cases : FirstBOneX211ZTenC z)
    (density : FirstBOneX211DensityEnvelope 0 j y z) :
    FirstBOneX211Candidate 0 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenC at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h1_v13
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 1746) 4)
    (z_cases :
      z = 420724
    )
    (density : FirstBOneX211DensityEnvelope 1 j y z) :
    FirstBOneX211Candidate 1 y z ∧ j = 0 := by
  rcases z_cases with rfl
  interval_cases j <;>
  norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
  omega

private theorem firstBOneX211_shallow_h1_v12
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 1746) 5)
    (z_cases :
      z = 952165 ∨ z = 1483606
    )
    (density : FirstBOneX211DensityEnvelope 1 j y z) :
    FirstBOneX211Candidate 1 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h1_v11
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 1746) 6)
    (z_cases :
      z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    )
    (density : FirstBOneX211DensityEnvelope 1 j y z) :
    FirstBOneX211Candidate 1 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h1_v10_a
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 1746) 7)
    (z_cases : FirstBOneX211ZTenA z)
    (density : FirstBOneX211DensityEnvelope 1 j y z) :
    FirstBOneX211Candidate 1 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenA at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h1_v10_b
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 1746) 7)
    (z_cases : FirstBOneX211ZTenB z)
    (density : FirstBOneX211DensityEnvelope 1 j y z) :
    FirstBOneX211Candidate 1 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenB at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h1_v10_c
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 1746) 7)
    (z_cases : FirstBOneX211ZTenC z)
    (density : FirstBOneX211DensityEnvelope 1 j y z) :
    FirstBOneX211Candidate 1 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenC at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h2_v13
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 315) 5)
    (z_cases :
      z = 420724
    )
    (density : FirstBOneX211DensityEnvelope 2 j y z) :
    FirstBOneX211Candidate 2 y z ∧ j = 0 := by
  rcases z_cases with rfl
  interval_cases j <;>
  norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
  omega

private theorem firstBOneX211_shallow_h2_v12
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 315) 6)
    (z_cases :
      z = 952165 ∨ z = 1483606
    )
    (density : FirstBOneX211DensityEnvelope 2 j y z) :
    FirstBOneX211Candidate 2 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h2_v11
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 315) 7)
    (z_cases :
      z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    )
    (density : FirstBOneX211DensityEnvelope 2 j y z) :
    FirstBOneX211Candidate 2 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h2_v10_a
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 315) 8)
    (z_cases : FirstBOneX211ZTenA z)
    (density : FirstBOneX211DensityEnvelope 2 j y z) :
    FirstBOneX211Candidate 2 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenA at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h2_v10_b
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 315) 8)
    (z_cases : FirstBOneX211ZTenB z)
    (density : FirstBOneX211DensityEnvelope 2 j y z) :
    FirstBOneX211Candidate 2 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenB at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h2_v10_c
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 315) 8)
    (z_cases : FirstBOneX211ZTenC z)
    (density : FirstBOneX211DensityEnvelope 2 j y z) :
    FirstBOneX211Candidate 2 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenC at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h3_v13
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 15705) 6)
    (z_cases :
      z = 420724
    )
    (density : FirstBOneX211DensityEnvelope 3 j y z) :
    FirstBOneX211Candidate 3 y z ∧ j = 0 := by
  rcases z_cases with rfl
  interval_cases j <;>
  norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
  omega

private theorem firstBOneX211_shallow_h3_v12
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 15705) 7)
    (z_cases :
      z = 952165 ∨ z = 1483606
    )
    (density : FirstBOneX211DensityEnvelope 3 j y z) :
    FirstBOneX211Candidate 3 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h3_v11
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 15705) 8)
    (z_cases :
      z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    )
    (density : FirstBOneX211DensityEnvelope 3 j y z) :
    FirstBOneX211Candidate 3 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h3_v10_a
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 15705) 9)
    (z_cases : FirstBOneX211ZTenA z)
    (density : FirstBOneX211DensityEnvelope 3 j y z) :
    FirstBOneX211Candidate 3 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenA at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h3_v10_b
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 15705) 9)
    (z_cases : FirstBOneX211ZTenB z)
    (density : FirstBOneX211DensityEnvelope 3 j y z) :
    FirstBOneX211Candidate 3 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenB at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h3_v10_c
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 15705) 9)
    (z_cases : FirstBOneX211ZTenC z)
    (density : FirstBOneX211DensityEnvelope 3 j y z) :
    FirstBOneX211Candidate 3 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenC at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h4_v13
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 2826) 7)
    (z_cases :
      z = 420724
    )
    (density : FirstBOneX211DensityEnvelope 4 j y z) :
    FirstBOneX211Candidate 4 y z ∧ j = 0 := by
  rcases z_cases with rfl
  interval_cases j <;>
  norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
  omega

private theorem firstBOneX211_shallow_h4_v12
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 2826) 8)
    (z_cases :
      z = 952165 ∨ z = 1483606
    )
    (density : FirstBOneX211DensityEnvelope 4 j y z) :
    FirstBOneX211Candidate 4 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h4_v11
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 2826) 9)
    (z_cases :
      z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    )
    (density : FirstBOneX211DensityEnvelope 4 j y z) :
    FirstBOneX211Candidate 4 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h4_v10_a
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 2826) 10)
    (z_cases : FirstBOneX211ZTenA z)
    (density : FirstBOneX211DensityEnvelope 4 j y z) :
    FirstBOneX211Candidate 4 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenA at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h4_v10_b
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 2826) 10)
    (z_cases : FirstBOneX211ZTenB z)
    (density : FirstBOneX211DensityEnvelope 4 j y z) :
    FirstBOneX211Candidate 4 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenB at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h4_v10_c
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 2826) 10)
    (z_cases : FirstBOneX211ZTenC z)
    (density : FirstBOneX211DensityEnvelope 4 j y z) :
    FirstBOneX211Candidate 4 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenC at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h5_v13
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 141336) 8)
    (z_cases :
      z = 420724
    )
    (density : FirstBOneX211DensityEnvelope 5 j y z) :
    FirstBOneX211Candidate 5 y z ∧ j = 0 := by
  rcases z_cases with rfl
  interval_cases j <;>
  norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
  omega

private theorem firstBOneX211_shallow_h5_v12
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 141336) 9)
    (z_cases :
      z = 952165 ∨ z = 1483606
    )
    (density : FirstBOneX211DensityEnvelope 5 j y z) :
    FirstBOneX211Candidate 5 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h5_v11
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 141336) 10)
    (z_cases :
      z = 66430 ∨ z = 243577 ∨ z = 597871 ∨ z = 775018 ∨ z = 1129312 ∨ z = 1306459
    )
    (density : FirstBOneX211DensityEnvelope 5 j y z) :
    FirstBOneX211Candidate 5 y z ∧ j = 0 := by
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h5_v10_a
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 141336) 11)
    (z_cases : FirstBOneX211ZTenA z)
    (density : FirstBOneX211DensityEnvelope 5 j y z) :
    FirstBOneX211Candidate 5 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenA at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h5_v10_b
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 141336) 11)
    (z_cases : FirstBOneX211ZTenB z)
    (density : FirstBOneX211DensityEnvelope 5 j y z) :
    FirstBOneX211Candidate 5 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenB at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_shallow_h5_v10_c
    (j y z : Nat) (j_le : j ≤ 13) (y_lower : 22529 ≤ y)
    (y_upper : y ≤ 51767)
    (u_exact : ExactThreeOrder ((y : ℤ) - 141336) 11)
    (z_cases : FirstBOneX211ZTenC z)
    (density : FirstBOneX211DensityEnvelope 5 j y z) :
    FirstBOneX211Candidate 5 y z ∧ j = 0 := by
  unfold FirstBOneX211ZTenC at z_cases
  rcases z_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J, ExactThreeOrder, FirstBOneX211Candidate] at density u_exact ⊢ <;>
    omega

private theorem firstBOneX211_of_shallow_orders
    (h j y z uOrder vOrder : Nat) (h_le : h ≤ 5) (j_le : j ≤ 13)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767) (z_upper : z < 3 ^ 13)
    (u_lower : h + 3 ≤ uOrder) (order_sum : uOrder + vOrder = h + 16)
    (u_shallow : uOrder < h + 7)
    (u_exact : ExactThreeOrder ((y : ℤ) - firstBOneX211RootResidue h) uOrder)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope h j y z) :
    FirstBOneX211Candidate h y z ∧ j = 0 := by
  have order_cases :
      (uOrder = h + 3 ∧ vOrder = 13) ∨
        (uOrder = h + 4 ∧ vOrder = 12) ∨
        (uOrder = h + 5 ∧ vOrder = 11) ∨
        (uOrder = h + 6 ∧ vOrder = 10) := by
    omega
  rcases order_cases with first | second | third | fourth
  · rcases first with ⟨rfl, rfl⟩
    rcases v_shell with top | small
    · rcases top with ⟨_, z_eq⟩
      interval_cases h
      · exact firstBOneX211_shallow_h0_v13 j y z j_le y_lower y_upper
          u_exact z_eq density
      · exact firstBOneX211_shallow_h1_v13 j y z j_le y_lower y_upper
          u_exact z_eq density
      · exact firstBOneX211_shallow_h2_v13 j y z j_le y_lower y_upper
          u_exact z_eq density
      · exact firstBOneX211_shallow_h3_v13 j y z j_le y_lower y_upper
          u_exact z_eq density
      · exact firstBOneX211_shallow_h4_v13 j y z j_le y_lower y_upper
          u_exact z_eq density
      · exact firstBOneX211_shallow_h5_v13 j y z j_le y_lower y_upper
          u_exact z_eq density
    · omega
  · rcases second with ⟨rfl, rfl⟩
    rcases v_shell with top | shell
    · omega
    · rcases shell with ⟨_, v_exact⟩
      have z_cases := firstBOneX211_z_order_twelve z z_upper v_exact
      interval_cases h
      · exact firstBOneX211_shallow_h0_v12 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h1_v12 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h2_v12 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h3_v12 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h4_v12 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h5_v12 j y z j_le y_lower y_upper
          u_exact z_cases density
  · rcases third with ⟨rfl, rfl⟩
    rcases v_shell with top | shell
    · omega
    · rcases shell with ⟨_, v_exact⟩
      have z_cases := firstBOneX211_z_order_eleven z z_upper v_exact
      interval_cases h
      · exact firstBOneX211_shallow_h0_v11 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h1_v11 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h2_v11 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h3_v11 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h4_v11 j y z j_le y_lower y_upper
          u_exact z_cases density
      · exact firstBOneX211_shallow_h5_v11 j y z j_le y_lower y_upper
          u_exact z_cases density
  · rcases fourth with ⟨rfl, rfl⟩
    rcases v_shell with top | shell
    · omega
    · rcases shell with ⟨_, v_exact⟩
      rcases firstBOneX211_z_order_ten z z_upper v_exact with
        group_a | group_b | group_c
      · interval_cases h
        · exact firstBOneX211_shallow_h0_v10_a j y z j_le y_lower y_upper
            u_exact group_a density
        · exact firstBOneX211_shallow_h1_v10_a j y z j_le y_lower y_upper
            u_exact group_a density
        · exact firstBOneX211_shallow_h2_v10_a j y z j_le y_lower y_upper
            u_exact group_a density
        · exact firstBOneX211_shallow_h3_v10_a j y z j_le y_lower y_upper
            u_exact group_a density
        · exact firstBOneX211_shallow_h4_v10_a j y z j_le y_lower y_upper
            u_exact group_a density
        · exact firstBOneX211_shallow_h5_v10_a j y z j_le y_lower y_upper
            u_exact group_a density
      · interval_cases h
        · exact firstBOneX211_shallow_h0_v10_b j y z j_le y_lower y_upper
            u_exact group_b density
        · exact firstBOneX211_shallow_h1_v10_b j y z j_le y_lower y_upper
            u_exact group_b density
        · exact firstBOneX211_shallow_h2_v10_b j y z j_le y_lower y_upper
            u_exact group_b density
        · exact firstBOneX211_shallow_h3_v10_b j y z j_le y_lower y_upper
            u_exact group_b density
        · exact firstBOneX211_shallow_h4_v10_b j y z j_le y_lower y_upper
            u_exact group_b density
        · exact firstBOneX211_shallow_h5_v10_b j y z j_le y_lower y_upper
            u_exact group_b density
      · interval_cases h
        · exact firstBOneX211_shallow_h0_v10_c j y z j_le y_lower y_upper
            u_exact group_c density
        · exact firstBOneX211_shallow_h1_v10_c j y z j_le y_lower y_upper
            u_exact group_c density
        · exact firstBOneX211_shallow_h2_v10_c j y z j_le y_lower y_upper
            u_exact group_c density
        · exact firstBOneX211_shallow_h3_v10_c j y z j_le y_lower y_upper
            u_exact group_c density
        · exact firstBOneX211_shallow_h4_v10_c j y z j_le y_lower y_upper
            u_exact group_c density
        · exact firstBOneX211_shallow_h5_v10_c j y z j_le y_lower y_upper
            u_exact group_c density

private def FirstBOneX211DeepY (h y : Nat) : Prop :=
  (h = 0 ∧ y = 24093) ∨
  (h = 0 ∧ y = 26280) ∨
  (h = 0 ∧ y = 28467) ∨
  (h = 0 ∧ y = 30654) ∨
  (h = 0 ∧ y = 32841) ∨
  (h = 0 ∧ y = 35028) ∨
  (h = 0 ∧ y = 37215) ∨
  (h = 0 ∧ y = 39402) ∨
  (h = 0 ∧ y = 41589) ∨
  (h = 0 ∧ y = 43776) ∨
  (h = 0 ∧ y = 45963) ∨
  (h = 0 ∧ y = 48150) ∨
  (h = 0 ∧ y = 50337) ∨
  (h = 1 ∧ y = 27990) ∨
  (h = 1 ∧ y = 34551) ∨
  (h = 1 ∧ y = 41112) ∨
  (h = 1 ∧ y = 47673) ∨
  (h = 2 ∧ y = 39681)

private theorem firstBOneX211_deep_y_cases (h y : Nat) (h_le : h ≤ 5)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767)
    (divisible : (3 : ℤ) ^ (h + 7) ∣ (y : ℤ) - firstBOneX211RootResidue h) :
    FirstBOneX211DeepY h y := by
  interval_cases h <;>
    norm_num [firstBOneX211RootResidue, FirstBOneX211DeepY] at divisible ⊢ <;>
    omega

private theorem firstBOneX211_deep_h0_y24093_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 24093 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y24093_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 24093 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y24093
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 24093 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y24093_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y24093_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y26280_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 26280 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y26280_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 26280 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y26280
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 26280 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y26280_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y26280_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y28467_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 28467 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y28467_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 28467 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y28467
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 28467 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y28467_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y28467_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y30654_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 30654 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y30654_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 30654 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y30654
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 30654 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y30654_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y30654_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y32841_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 32841 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y32841_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 32841 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y32841
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 32841 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y32841_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y32841_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y35028_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 35028 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y35028_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 35028 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y35028
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 35028 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y35028_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y35028_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y37215_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 37215 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y37215_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 37215 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y37215
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 37215 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y37215_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y37215_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y39402_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 39402 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y39402_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 39402 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y39402
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 39402 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y39402_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y39402_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y41589_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 41589 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y41589_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 41589 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y41589
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 41589 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y41589_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y41589_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y43776_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 43776 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y43776_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 43776 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y43776
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 43776 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y43776_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y43776_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y45963_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 45963 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y45963_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 45963 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y45963
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 45963 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y45963_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y45963_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y48150_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 48150 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y48150_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 48150 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y48150
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 48150 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y48150_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y48150_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h0_y50337_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 50337 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y50337_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 0 j 50337 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h0_y50337
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 0 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 0 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 0 j 50337 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h0_y50337_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h0_y50337_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h1_y27990_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 27990 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y27990_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 27990 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y27990
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 1 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 1 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 1 j 27990 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h1_y27990_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h1_y27990_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h1_y34551_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 34551 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y34551_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 34551 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y34551
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 1 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 1 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 1 j 34551 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h1_y34551_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h1_y34551_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h1_y41112_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 41112 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y41112_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 41112 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y41112
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 1 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 1 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 1 j 41112 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h1_y41112_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h1_y41112_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h1_y47673_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 47673 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y47673_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 1 j 47673 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h1_y47673
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 1 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 1 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 1 j 47673 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h1_y47673_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h1_y47673_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_deep_h2_y39681_low
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_upper : vOrder ≤ 4)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 2 j 39681 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h2_y39681_high
    (j z vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (v_lower : 5 ≤ vOrder) (v_upper : vOrder ≤ 9)
    (v_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder)
    (density : FirstBOneX211DensityEnvelope 2 j 39681 z) : False := by
  interval_cases vOrder <;> interval_cases j <;>
    norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
      firstBOneX211Q, firstBOneX211J, ExactThreeOrder] at density v_exact <;>
    omega

private theorem firstBOneX211_deep_h2_y39681
    (j z uOrder vOrder : Nat) (j_le : j ≤ 13) (z_upper : z < 3 ^ 13)
    (u_deep : 2 + 7 ≤ uOrder) (order_sum : uOrder + vOrder = 2 + 16)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope 2 j 39681 z) : False := by
  rcases v_shell with top | shell
  · omega
  · rcases shell with ⟨_, v_exact⟩
    have v_at_most_nine : vOrder ≤ 9 := by omega
    by_cases v_low : vOrder ≤ 4
    · exact firstBOneX211_deep_h2_y39681_low j z vOrder j_le z_upper v_low v_exact density
    · have v_high : 5 ≤ vOrder := by omega
      exact firstBOneX211_deep_h2_y39681_high j z vOrder j_le z_upper v_high v_at_most_nine
        v_exact density

private theorem firstBOneX211_of_deep_orders
    (h j y z uOrder vOrder : Nat) (h_le : h ≤ 5) (j_le : j ≤ 13)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767) (z_upper : z < 3 ^ 13)
    (u_deep : h + 7 ≤ uOrder) (order_sum : uOrder + vOrder = h + 16)
    (y_divisible :
      (3 : ℤ) ^ (h + 7) ∣ (y : ℤ) - firstBOneX211RootResidue h)
    (v_shell : (vOrder = 13 ∧ z = 420724) ∨
      (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder))
    (density : FirstBOneX211DensityEnvelope h j y z) :
    FirstBOneX211Candidate h y z ∧ j = 0 := by
  have y_cases := firstBOneX211_deep_y_cases h y h_le y_lower y_upper y_divisible
  unfold FirstBOneX211DeepY at y_cases
  rcases y_cases with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim (firstBOneX211_deep_h0_y24093 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y26280 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y28467 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y30654 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y32841 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y35028 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y37215 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y39402 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y41589 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y43776 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y45963 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y48150 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h0_y50337 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h1_y27990 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h1_y34551 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h1_y41112 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h1_y47673 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)
  · exact False.elim (firstBOneX211_deep_h2_y39681 j z uOrder vOrder j_le
      z_upper u_deep order_sum v_shell density)

/-- The bounded valuation and density envelopes leave exactly the ten terminal candidates,
and force the tail's first `b` to occur at position zero. -/
theorem firstBOneX211Candidate_of_envelopes
    (h j y z : Nat) (h_le : h ≤ 5) (j_le : j ≤ 13)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767) (z_upper : z < 3 ^ 13)
    (valuation : FirstBOneX211ValuationEnvelope h y z)
    (density : FirstBOneX211DensityEnvelope h j y z) :
    FirstBOneX211Candidate h y z ∧ j = 0 := by
  rcases valuation with
    ⟨uOrder, vOrder, u_lower, order_sum, v_upper, u_shell, v_shell⟩
  rcases u_shell with shallow | deep
  · rcases shallow with ⟨u_shallow, u_exact⟩
    exact firstBOneX211_of_shallow_orders h j y z uOrder vOrder h_le j_le y_lower
      y_upper z_upper u_lower order_sum u_shallow u_exact v_shell density
  · rcases deep with ⟨u_deep, y_divisible⟩
    exact firstBOneX211_of_deep_orders h j y z uOrder vOrder h_le j_le y_lower
      y_upper z_upper u_deep order_sum y_divisible v_shell density

end MatrixMortality.ParabolicBlade

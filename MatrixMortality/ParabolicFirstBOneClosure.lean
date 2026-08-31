import MatrixMortality.ParabolicFirstBOneSFFT

/-!
# Terminal certificate for the first-`b`-after-one-`c` chamber

At outer wait `211`, the trailing-run and divisor analysis reduces every possible zero in the
bounded chamber to ten triples `(h, y, z)`.  This file checks those ten cases directly against
the exact tag-word density grammar.  It also exposes the remaining upstream obligation as
`FirstBOneX211ZeroFunnel`: once the divisor analysis supplies that funnel, no zero survives.
-/

namespace MatrixMortality.ParabolicBlade

/-- The ten triples left by the bounded `3`-adic and density calculation at outer wait `211`. -/
def FirstBOneX211Candidate (h y z : Nat) : Prop :=
  (h = 0 ∧ y = 39726 ∧ z = 952165) ∨
    (h = 0 ∧ y = 39726 ∧ z = 1483606) ∨
    (h = 0 ∧ y = 39753 ∧ z = 420724) ∨
    (h = 0 ∧ y = 39780 ∧ z = 420724) ∨
    (h = 0 ∧ y = 39807 ∧ z = 952165) ∨
    (h = 0 ∧ y = 39807 ∧ z = 1483606) ∨
    (h = 1 ∧ y = 39735 ∧ z = 420724) ∨
    (h = 1 ∧ y = 39816 ∧ z = 420724) ∨
    (h = 3 ∧ y = 39762 ∧ z = 952165) ∨
    (h = 3 ∧ y = 39762 ∧ z = 1483606)

/-- The outer-wait core after writing a physical body as `cbb ++ rest`, with suffix scale `R`
and suffix complement `G`. -/
def firstBOneX211RestCore (R G y z : ℤ) : ℤ :=
  let Q := 465621956 * z + 42879529
  let J := 620717828832 * y * z + 58005064872 * y +
    133690369309176 * z + 12496984445436
  R * (9516 * J - 177147 * (72 * y - 9) * Q) + G * J + (8 * y - 9) * Q

theorem bZeroBDefectCOneCodeCore_x211_rest_normal_form (R G y z : ℤ) :
    bZeroBDefectCOneCodeCore (177147 * R)
      (177147 * R - 1 - (9516 * R + G)) 211 y z =
        firstBOneX211RestCore R G y z := by
  unfold bZeroBDefectCOneCodeCore firstBOneX211RestCore
  ring

private theorem x211_low_gap_39726_952165 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39726 952165 = 0) :
    39 * R < 2178 * G ∧ 243 * G < 13 * R := by
  change (R : ℤ) * (-775058771174361513561) +
    (G : ℤ) * 23606388200024103285828 + 140895860147842073931 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 2178 * G := by linarith
    exact_mod_cast gap
  · have gap : (243 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_low_gap_39726_1483606 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39726 1483606 = 0) :
    39 * R < 2178 * G ∧ 243 * G < 13 * R := by
  change (R : ℤ) * (-1207828501607877133869) +
    (G : ℤ) * 36782047166866205474556 + 219535412715773964135 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 2178 * G := by linarith
    exact_mod_cast gap
  · have gap : (243 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39753_420724 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39753 420724 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-706515667678680907437) +
    (G : ℤ) * 10437780308719210736580 + 62298621628844449095 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39780_420724 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39780 420724 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-1070742294616515921621) +
    (G : ℤ) * 10444831384256420376060 + 62340935677778714463 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39807_952165 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39807 952165 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-3247966798227973383345) +
    (G : ℤ) * 23654261293833189064140 + 141183150282096120243 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39807_1483606 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39807 1483606 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-5060964674901595830885) +
    (G : ℤ) * 36856640127872748112740 + 219983050837479260655 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_low_gap_39735_420724 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39735 420724 = 0) :
    39 * R < 2178 * G ∧ 243 * G < 13 * R := by
  change (R : ℤ) * (-463697916386790897981) +
    (G : ℤ) * 10433079591694404310260 + 62270412262888272183 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 2178 * G := by linarith
    exact_mod_cast gap
  · have gap : (243 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39816_420724 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39816 420724 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-1556377797200295940533) +
    (G : ℤ) * 10454232818306033228700 + 62397354409691068287 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39762_952165 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39762 952165 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-1874129005420411233465) +
    (G : ℤ) * 23627665130605919187300 + 141023544651954983403 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

private theorem x211_high_gap_39762_1483606 (R G : Nat) (scale_pos : 1 ≤ R)
    (core_zero : firstBOneX211RestCore R G 39762 1483606 = 0) :
    39 * R < 726 * G ∧ 81 * G < 13 * R := by
  change (R : ℤ) * (-2920333467516196554765) +
    (G : ℤ) * 36815199593980224424860 + 219734362992087429255 = 0 at core_zero
  have scale_pos_int : (1 : ℤ) ≤ R := by exact_mod_cast scale_pos
  constructor
  · have gap : (39 : ℤ) * R < 726 * G := by linarith
    exact_mod_cast gap
  · have gap : (81 : ℤ) * G < 13 * R := by linarith
    exact_mod_cast gap

/-- Every candidate zero forces the suffix density into one of two open intervals. -/
theorem firstBOneX211Candidate_rest_gap (R G h y z : Nat) (scale_pos : 1 ≤ R)
    (candidate : FirstBOneX211Candidate h y z)
    (core_zero :
      bZeroBDefectCOneCodeCore (177147 * (R : ℤ))
        (177147 * R - 1 - (9516 * R + G)) 211 y z = 0) :
    (39 * R < 2178 * G ∧ 243 * G < 13 * R) ∨
      (39 * R < 726 * G ∧ 81 * G < 13 * R) := by
  rw [bZeroBDefectCOneCodeCore_x211_rest_normal_form] at core_zero
  rcases candidate with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl (x211_low_gap_39726_952165 R G scale_pos core_zero)
  · exact Or.inl (x211_low_gap_39726_1483606 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39753_420724 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39780_420724 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39807_952165 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39807_1483606 R G scale_pos core_zero)
  · exact Or.inl (x211_low_gap_39735_420724 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39816_420724 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39762_952165 R G scale_pos core_zero)
  · exact Or.inr (x211_high_gap_39762_1483606 R G scale_pos core_zero)

private theorem cbb_scale (rest : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .b, .b] ++ rest)).length =
      177147 * 3 ^ (tagEncode 3 rest).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem cbb_complement (rest : List TagLetter) :
    tagComplementCode ([.c, .b, .b] ++ rest) =
      9516 * 3 ^ (tagEncode 3 rest).length + tagComplementCode rest := by
  rw [tagComplementCode_append]
  have stem_complement : tagComplementCode [.c, .b, .b] = 9516 := by decide
  rw [stem_complement]

/-- None of the ten candidate triples can vanish on a physical `cbb` body. -/
theorem firstBOneX211Candidate_core_ne_zero (rest : List TagLetter) (h y z : Nat)
    (candidate : FirstBOneX211Candidate h y z) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b, .b] ++ rest)).length)
      (ternaryCode (tagEncode 3 ([.c, .b, .b] ++ rest))) 211 y z ≠ 0 := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let body := [.c, .b, .b] ++ rest
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_pos : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by norm_num)
  have scale_eq : S = 177147 * R := by
    dsimp [S, R, body]
    exact cbb_scale rest
  have complement_eq : D = 9516 * R + G := by
    dsimp [D, R, G, body]
    exact cbb_complement rest
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length (tagEncode 3 ([.c, .b, .b] ++ rest))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have scale_eq_int : (S : ℤ) = 177147 * R := by exact_mod_cast scale_eq
  have complement_eq_int : (D : ℤ) = 9516 * R + G := by exact_mod_cast complement_eq
  have coordinate_sum_int : (C : ℤ) + D + 1 = S := by exact_mod_cast coordinate_sum
  have code_eq_int :
      (C : ℤ) = 177147 * R - 1 - (9516 * R + G) := by
    omega
  intro core_zero
  have scale_cast :
      (S : ℚ) = (3 : ℚ) ^ (tagEncode 3 ([.c, .b, .b] ++ rest)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) 211 y z = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 211 y z = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  rw [scale_eq_int, code_eq_int] at core_zero_int
  rcases firstBOneX211Candidate_rest_gap R G h y z scale_pos candidate core_zero_int with
    low_gap | high_gap
  · rcases tagComplementCode_first_b_position_gap 1 rest with lower | upper
    · omega
    · omega
  · rcases tagComplementCode_first_b_position_gap 0 rest with lower | upper
    · omega
    · omega

/-- The precise remaining input from the trailing-run/divisor classification.  Its premises
record the bounded chamber and the physical tail-density hypothesis rather than hiding them in
an opaque candidate assertion. -/
def FirstBOneX211ZeroFunnel (tail stem : List TagLetter) (h y z : Nat) : Prop :=
  tail = stem ++ .b :: List.replicate h .c →
    h ≤ 5 →
    22529 ≤ y →
    y ≤ 51767 →
    z < 3 ^ 13 →
    242 * tagComplementCode tail ≤
      39 * (3 ^ (tagEncode 3 tail).length - 1) →
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z = 0 →
    FirstBOneX211Candidate h y z ∧ ∃ rest, tail = .b :: rest

/-- Terminal extinction of the `x = 211` chamber, conditional only on the explicit upstream
zero funnel supplied by the trailing-run/divisor calculation. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_funnel
    (tail stem : List TagLetter) (h y z : Nat)
    (tail_trailing : tail = stem ++ .b :: List.replicate h .c)
    (run_bound : h ≤ 5) (wait_lower : 22529 ≤ y) (wait_upper : y ≤ 51767)
    (inner_bound : z < 3 ^ 13)
    (tail_density :
      242 * tagComplementCode tail ≤
        39 * (3 ^ (tagEncode 3 tail).length - 1))
    (zero_funnel : FirstBOneX211ZeroFunnel tail stem h y z) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  rcases zero_funnel tail_trailing run_bound wait_lower wait_upper inner_bound tail_density
      core_zero with ⟨candidate, rest, tail_eq⟩
  rw [tail_eq] at core_zero
  have candidate_nonzero := firstBOneX211Candidate_core_ne_zero rest h y z candidate
  exact candidate_nonzero (by simpa using core_zero)

end MatrixMortality.ParabolicBlade

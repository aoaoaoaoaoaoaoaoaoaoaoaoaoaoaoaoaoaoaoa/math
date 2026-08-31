import MatrixMortality.SwappedSetterCylinder

/-!
# Long all-erasure extinction for the swapped setter

The compiler cylinder leaves one long all-erasure middle block before a singleton target.
Its exact normalized discrepancy is greater than twelve, while either singleton pole requires
a discrepancy below twelve. This removes `D_c^(β+1)` from the first multi-transfer frontier.
-/

namespace MatrixMortality.SwappedSetterMultitransfer

private theorem two_mul_code_false (count : Nat) :
    2 * ternaryCode (List.replicate count false) = 3 ^ count - 1 := by
  induction count with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, ternaryCode_cons, List.length_replicate, pow_succ]
      simp only [ternaryDigit]
      have power_pos : 0 < 3 ^ count := pow_pos (by omega) count
      omega

private theorem code_true (count : Nat) :
    ternaryCode (List.replicate count true) = 3 ^ count - 1 := by
  induction count with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, ternaryCode_cons, List.length_replicate, induction,
        pow_succ]
      simp only [ternaryDigit]
      have power_pos : 0 < 3 ^ count := pow_pos (by omega) count
      omega

private theorem upper_word_all_deletion_c (width count : Nat) :
    spell (nearyUpper width)
        (List.replicate count (.erase .c)) =
      List.replicate count true := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp only [spell, List.flatMap_cons, nearyUpper, tagCode, List.singleton_append]
      exact congrArg (true :: ·) induction

private theorem lower_word_all_deletion_c (width : Nat) (body : List TagLetter)
    (count : Nat) :
    spell (nearyLower width body)
        (List.replicate count (.erase .c)) =
      List.replicate count false := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp only [spell, List.flatMap_cons, nearyLower, List.singleton_append]
      exact congrArg (false :: ·) induction

/-- An all-`D_c` block has one upper digit per role. -/
theorem allDeletionC_upperLength (width count : Nat) :
    upperLength width (List.replicate count (.erase .c)) = count := by
  rw [upperLength, upper_word_all_deletion_c, List.length_replicate]

/-- The swapped lower code of `D_c^n` is `3^n-1`. -/
theorem allDeletionC_lowerCode (width : Nat) (body : List TagLetter)
    (count : Nat) :
    swappedLowerCode width body (List.replicate count (.erase .c)) =
      3 ^ count - 1 := by
  rw [swappedLowerCode, lower_word_all_deletion_c, List.map_replicate]
  simp only [Bool.not_false]
  have power_pos : 0 < 3 ^ count := pow_pos (by omega) count
  calc
    (ternaryCode (List.replicate count true) : ℤ) =
        ((3 ^ count - 1 : Nat) : ℤ) := by exact_mod_cast code_true count
    _ = (3 : ℤ) ^ count - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num

/-- At length `β+1`, twice the punctuated upper code is `9ρ²+ρ-2`. -/
theorem allDeletionC_long_upperCode (width : Nat) :
    2 * swappedUpperCode width
          (List.replicate (width + 1) (.erase .c)) =
      9 * widthScale width ^ 2 + widthScale width - 2 := by
  rw [swappedUpperCode, upper_word_all_deletion_c, List.map_append,
    List.map_replicate, ternaryCode_append, List.length_map]
  simp only [Bool.not_true, nearyMarker, List.map_cons,
    List.length_cons, List.length_replicate]
  have prefix_eq := two_mul_code_false (width + 1)
  have marker_eq := swappedCode_nearyMarker width
  have prefix_cast :
      2 * (ternaryCode (List.replicate (width + 1) false) : ℤ) =
        (3 : ℤ) ^ (width + 1) - 1 := by
    have power_pos : 0 < 3 ^ (width + 1) := pow_pos (by omega) (width + 1)
    calc
      2 * (ternaryCode (List.replicate (width + 1) false) : ℤ) =
          ((2 * ternaryCode (List.replicate (width + 1) false) : Nat) : ℤ) := by
            norm_num
      _ = ((3 ^ (width + 1) - 1 : Nat) : ℤ) := by rw [prefix_eq]
      _ = (3 : ℤ) ^ (width + 1) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  have marker_cast :
      (ternaryCode (false :: List.map not (List.replicate width false)) : ℤ) =
        2 * (3 : ℤ) ^ width - 1 := by
    have marker_nat :
        ternaryCode (false :: List.map not (List.replicate width false)) =
          2 * 3 ^ width - 1 := by
      simpa [nearyMarker] using marker_eq
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    calc
      (ternaryCode (false :: List.map not (List.replicate width false)) : ℤ) =
          ((2 * 3 ^ width - 1 : Nat) : ℤ) := by exact_mod_cast marker_nat
      _ = 2 * (3 : ℤ) ^ width - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  calc
    2 *
          (↑(3 ^ (width + 1) * ternaryCode (List.replicate (width + 1) false) +
            ternaryCode (false :: List.map not (List.replicate width false))) : ℤ) =
        (3 : ℤ) ^ (width + 1) *
            (2 * (ternaryCode (List.replicate (width + 1) false) : ℤ)) +
          2 * (ternaryCode
            (false :: List.map not (List.replicate width false)) : ℤ) := by
              push_cast
              ring
    _ = 9 * widthScale width ^ 2 + widthScale width - 2 := by
      rw [prefix_cast, marker_cast]
      simp only [widthScale]
      rw [pow_add, pow_one]
      ring

private theorem firstMismatch_lt_one
    {width : Nat} (width_pos : 0 < width) (first : List NearyTile) :
    firstMismatch width first < 1 := by
  obtain ⟨first_lower, _⟩ := swappedUpperCode_cylinder width_pos first
  have scale_pos : (0 : ℤ) < widthScale width := by simp [widthScale]
  have power_pos : (0 : ℤ) < upperPower width first := by simp [upperPower]
  have first_pos_int : (0 : ℤ) < swappedUpperCode width first :=
    lt_of_lt_of_le (mul_pos scale_pos power_pos) first_lower
  have first_pos : (0 : ℚ) < swappedUpperCode width first := by
    exact_mod_cast first_pos_int
  have lower_rat :
      (widthScale width : ℚ) * upperPower width first ≤
        swappedUpperCode width first := by
    exact_mod_cast first_lower
  have marker_lt :
      (setterMarker width : ℚ) < 2 * widthScale width := by
    rw [setterMarker]
    push_cast
    linarith
  rw [firstMismatch]
  apply (div_lt_iff₀ first_pos).2
  nlinarith [mul_lt_mul_of_pos_right marker_lt
    (show (0 : ℚ) < upperPower width first by exact_mod_cast power_pos)]

/-- Exact normalized discrepancy of the `D_c^(β+1)` transfer. -/
theorem allDeletionC_long_transferDiscrepancy
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) :
    transferDiscrepancy width body first
        (List.replicate (width + 1) (.erase .c)) =
      (9 * (widthScale width : ℚ) ^ 2 + widthScale width - 2) /
          (2 * widthScale width) -
        terminalDiscrepancy width * (3 * widthScale width - 1) *
            firstMismatch width first /
          ((widthScale width - 2) * widthScale width) := by
  have discrepancy_eq := transferDiscrepancy_eq width_large body first
    (List.replicate (width + 1) (.erase .c))
  rw [allDeletionC_upperLength] at discrepancy_eq
  have upper_twice := allDeletionC_long_upperCode width
  have upper_eq :
      (swappedUpperCode width
          (List.replicate (width + 1) (.erase .c)) : ℚ) =
        (9 * (widthScale width : ℚ) ^ 2 + widthScale width - 2) / 2 := by
    have upper_twice_rat :
        2 * (swappedUpperCode width
          (List.replicate (width + 1) (.erase .c)) : ℚ) =
          9 * (widthScale width : ℚ) ^ 2 + widthScale width - 2 := by
      exact_mod_cast upper_twice
    linarith
  have lower_eq := allDeletionC_lowerCode width body (width + 1)
  have scale_cast : (widthScale width : ℚ) = (3 : ℚ) ^ width := by
    norm_num [widthScale]
  have lower_eq_rat :
      (swappedLowerCode width body
          (List.replicate (width + 1) (.erase .c)) : ℚ) =
        3 * widthScale width - 1 := by
    rw [lower_eq]
    push_cast
    rw [pow_add, pow_one, ← scale_cast]
    ring
  have scale_pos : (0 : ℚ) < widthScale width := by
    rw [scale_cast]
    positivity
  have difference_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by
    have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
      have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
        exact_mod_cast scale_ge_nat
      simpa [widthScale] using casted
    have difference_pos_int : (0 : ℤ) < widthScale width - 2 := by omega
    exact_mod_cast difference_pos_int
  rw [discrepancy_eq, upper_eq, lower_eq_rat]
  push_cast
  simp only [← scale_cast]
  field_simp [ne_of_gt scale_pos, ne_of_gt difference_pos]

private theorem longDiscrepancy_gt_twelve
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) :
    12 < transferDiscrepancy width body first
      (List.replicate (width + 1) (.erase .c)) := by
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (27 : ℚ) ≤ widthScale width := by exact_mod_cast scale_ge_int
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have divisor_pos :
      (0 : ℚ) < ((widthScale width : ℚ) - 2) * widthScale width := by
    exact mul_pos (by linarith) scale_pos
  have mismatch_lt := firstMismatch_lt_one (show 0 < width by omega) first
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    rw [terminalDiscrepancy]
    push_cast
    linarith
  have long_lower_pos : (0 : ℚ) < 3 * widthScale width - 1 := by linarith
  have quotient_lt :
      terminalDiscrepancy width * (3 * widthScale width - 1) *
            firstMismatch width first /
          ((widthScale width - 2) * widthScale width) <
        terminalDiscrepancy width * (3 * widthScale width - 1) /
          ((widthScale width - 2) * widthScale width) := by
    apply (div_lt_div_iff₀ divisor_pos divisor_pos).2
    have coefficient_pos := mul_pos terminal_pos long_lower_pos
    have scaled := mul_lt_mul_of_pos_left mismatch_lt
      (mul_pos coefficient_pos divisor_pos)
    nlinarith
  have arithmetic :
      12 <
        (9 * (widthScale width : ℚ) ^ 2 + widthScale width - 2) /
            (2 * widthScale width) -
          terminalDiscrepancy width * (3 * widthScale width - 1) /
            ((widthScale width - 2) * widthScale width) := by
    rw [terminalDiscrepancy]
    push_cast
    have difference_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by linarith
    field_simp [ne_of_gt scale_pos, ne_of_gt difference_pos]
    have shifted_pos :
        (0 : ℚ) <
          9 * ((widthScale width : ℚ) - 27) ^ 3 +
            658 * ((widthScale width : ℚ) - 27) ^ 2 +
            15909 * ((widthScale width : ℚ) - 27) + 127010 := by
      positivity
    nlinarith [shifted_pos]
  rw [allDeletionC_long_transferDiscrepancy width_large body first]
  linarith

/-- The literal `D_c^(β+1)` survivor cannot reach either singleton pole. -/
theorem longDeletion_avoids_singleton_pole
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) (target : TagLetter)
    (pole :
      (singletonCoefficient width target : ℚ) *
          nextY
            (blockCoefficient width body
              (List.replicate (width + 1) (.erase .c)))
            (centeredCoupling width)
            (swappedLowerCode width body
              (List.replicate (width + 1) (.erase .c)))
            (upperPower width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * 2 *
          nextX
            (3 ^ upperLength width
              (List.replicate (width + 1) (.erase .c)))
            (centeredCoefficient width * swappedUpperCode width first) = 0) : False := by
  have normalized := transferDiscrepancy_pole_equation width_large body first
    (middle := List.replicate (width + 1) (.erase .c))
    (target := [.erase target]) (by simp) (by
      simpa [blockCoefficient_singleton, swappedLowerCode_singleton] using pole)
  rw [blockCoefficient_singleton, swappedLowerCode_singleton] at normalized
  have discrepancy_large := longDiscrepancy_gt_twelve width_large body first
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (27 : ℚ) ≤ widthScale width := by exact_mod_cast scale_ge_int
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    rw [setterMarker]
    push_cast
    linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    rw [terminalDiscrepancy]
    push_cast
    linarith
  cases target with
  | c =>
      rw [singletonCoefficient] at normalized
      push_cast at normalized
      have normalized_factor :
          (terminalDiscrepancy width : ℚ) *
              (-(widthScale width : ℚ) *
                  transferDiscrepancy width body first
                    (List.replicate (width + 1) (.erase .c)) +
                6 * setterMarker width) = 0 := by
        calc
          (terminalDiscrepancy width : ℚ) *
                (-(widthScale width : ℚ) *
                    transferDiscrepancy width body first
                      (List.replicate (width + 1) (.erase .c)) +
                  6 * setterMarker width) =
              (-(widthScale width : ℚ) * terminalDiscrepancy width) *
                    transferDiscrepancy width body first
                      (List.replicate (width + 1) (.erase .c)) +
                3 * terminalDiscrepancy width * setterMarker width * 2 := by ring
          _ = 0 := normalized
      have normalized_core :
          -(widthScale width : ℚ) *
                transferDiscrepancy width body first
                  (List.replicate (width + 1) (.erase .c)) +
              6 * setterMarker width = 0 :=
        (mul_eq_zero.mp normalized_factor).resolve_left (ne_of_gt terminal_pos)
      have discrepancy_eq :
          transferDiscrepancy width body first
              (List.replicate (width + 1) (.erase .c)) =
            6 * setterMarker width / widthScale width := by
        apply (eq_div_iff (ne_of_gt scale_pos)).2
        linarith
      have target_lt :
          6 * (setterMarker width : ℚ) / widthScale width < 12 := by
        rw [setterMarker]
        push_cast
        apply (div_lt_iff₀ scale_pos).2
        linarith
      linarith
  | b =>
      rw [singletonCoefficient] at normalized
      push_cast at normalized
      have cofactor_pos : (0 : ℚ) < singletonBCofactor width := by
        rw [singletonBCofactor]
        push_cast
        nlinarith [sq_nonneg ((widthScale width : ℚ) - 27)]
      have discrepancy_eq :
          transferDiscrepancy width body first
              (List.replicate (width + 1) (.erase .c)) =
            6 * terminalDiscrepancy width * setterMarker width /
              (widthScale width * singletonBCofactor width) := by
        have normalized_factor :
            (widthScale width : ℚ) * singletonBCofactor width *
                  transferDiscrepancy width body first
                    (List.replicate (width + 1) (.erase .c)) =
                6 * terminalDiscrepancy width * setterMarker width := by
          linarith
        apply (eq_div_iff (mul_ne_zero (ne_of_gt scale_pos)
          (ne_of_gt cofactor_pos))).2
        simpa [mul_assoc, mul_comm, mul_left_comm] using normalized_factor
      have cofactor_gt_terminal :
          (terminalDiscrepancy width : ℚ) < singletonBCofactor width := by
        rw [terminalDiscrepancy, singletonBCofactor]
        push_cast
        nlinarith [sq_nonneg ((widthScale width : ℚ) - 27)]
      have target_lt :
          6 * (terminalDiscrepancy width : ℚ) * setterMarker width /
              (widthScale width * singletonBCofactor width) < 12 := by
        have denominator_pos :
            (0 : ℚ) < widthScale width * singletonBCofactor width :=
          mul_pos scale_pos cofactor_pos
        apply (div_lt_iff₀ denominator_pos).2
        have first_cut := mul_lt_mul_of_pos_right cofactor_gt_terminal marker_pos
        have marker_lt :
            (setterMarker width : ℚ) < 2 * widthScale width := by
          rw [setterMarker]
          push_cast
          linarith
        have second_cut := mul_lt_mul_of_pos_left marker_lt cofactor_pos
        have six_cut := mul_lt_mul_of_pos_left (first_cut.trans second_cut)
          (show (0 : ℚ) < 6 by norm_num)
        nlinarith
      linarith

/-- Under the compiler envelope, a physical expected-shell first multi-transfer pole can only
use the literal middle `D_c²` and must target a depth-one role block. -/
theorem firstMultiTransfer_pole_forces_doubleDeletion
    {width firstDepth middleDepth targetDepth : Nat}
    (width_large : 3 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {first middle target : List NearyTile}
    (first_block : IsRoleBlock first)
    (middle_shell : HasPoleShell width middle middleDepth)
    (target_shell : HasPoleShell width target targetDepth)
    (first_nontrivial : 1 < firstDepth)
    (firstDepth_eq : firstDepth = upperLength width first)
    (middleCoefficient_shell :
      MatrixMortality.PadicValuation.HasValue 3
        (blockCoefficient width body middle : ℚ) middleDepth)
    (middleLower_unit :
      MatrixMortality.PadicValuation.IsUnit 3
        (swappedLowerCode width body middle : ℚ))
    (targetCoefficient_shell :
      MatrixMortality.PadicValuation.HasValue 3
        (blockCoefficient width body target : ℚ) targetDepth)
    (targetLower_unit :
      MatrixMortality.PadicValuation.IsUnit 3
        (swappedLowerCode width body target : ℚ))
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) ((3 : ℚ) ^ upperLength width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) :
    middle = [.erase .c, .erase .c] ∧ targetDepth = 1 := by
  have survivors := firstMultiTransfer_pole_forces_all_erasure width_large body_long
    body_head first_block middle_shell target_shell first_nontrivial firstDepth_eq
    middleCoefficient_shell middleLower_unit targetCoefficient_shell targetLower_unit pole
  rcases survivors with double_deletion | long_deletion
  · exact double_deletion
  · obtain ⟨middle_eq, targetDepth_width⟩ := long_deletion
    have target_singleton : ∃ letter, target = [.erase letter] := by
      rcases target_shell with ⟨target_block, target_single | target_multi⟩
      · obtain ⟨target_length, _⟩ := target_single
        obtain ⟨front, letter, target_eq⟩ := target_block
        have front_nil : front = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa [target_eq] using target_length
        subst front
        exact ⟨letter, target_eq⟩
      · obtain ⟨_, targetDepth_one⟩ := target_multi
        omega
    obtain ⟨letter, target_eq⟩ := target_singleton
    subst middle
    subst target
    exact False.elim <| longDeletion_avoids_singleton_pole width_large body first letter <| by
      simpa [upperPower, blockCoefficient_singleton, swappedLowerCode_singleton] using pole

end MatrixMortality.SwappedSetterMultitransfer

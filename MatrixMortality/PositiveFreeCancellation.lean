import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Positive free cancellation and quotient-blind boundaries

Three positive letters generate the binary free group as a monoid, so positivity alone does not
exclude free cancellation. Quotient-blind fixed boundaries nevertheless fail: accepting one group
element and its square forces acceptance of a nonempty positive identity spelling.
-/

namespace MatrixMortality

namespace PositiveFreeCancellation

/-! ## A three-positive-letter cover of the binary free group -/

/-- Positive generators `x`, `y`, and the formal inverse of `xy`. -/
inductive TriangleLetter
  | x
  | y
  | z
  deriving DecidableEq

/-- Group value of a positive triangle letter. -/
def triangleGenerator : TriangleLetter → FreeGroup Bool
  | .x => FreeGroup.of false
  | .y => FreeGroup.of true
  | .z => (FreeGroup.of true)⁻¹ * (FreeGroup.of false)⁻¹

/-- Evaluation of a positive triangle word in the binary free group. -/
def triangleEvaluate (word : List TriangleLetter) : FreeGroup Bool :=
  (word.map triangleGenerator).prod

@[simp]
theorem triangleEvaluate_nil : triangleEvaluate [] = 1 := by
  simp [triangleEvaluate]

@[simp]
theorem triangleEvaluate_cons (letter : TriangleLetter) (word : List TriangleLetter) :
    triangleEvaluate (letter :: word) = triangleGenerator letter * triangleEvaluate word := by
  simp [triangleEvaluate]

@[simp]
theorem triangleEvaluate_append (left right : List TriangleLetter) :
    triangleEvaluate (left ++ right) = triangleEvaluate left * triangleEvaluate right := by
  simp [triangleEvaluate]

/-- Each cyclic positive triple is a nonempty spelling of the group identity. -/
theorem triangle_relations :
    triangleEvaluate [.x, .y, .z] = 1 ∧
      triangleEvaluate [.y, .z, .x] = 1 ∧
      triangleEvaluate [.z, .x, .y] = 1 := by
  simp [triangleEvaluate, triangleGenerator, mul_assoc]

/-- Every binary free-group element has a positive spelling over three letters. -/
theorem triangleEvaluate_surjective : Function.Surjective triangleEvaluate := by
  intro element
  induction element using FreeGroup.induction_on with
  | C1 => exact ⟨[], triangleEvaluate_nil⟩
  | Cp bit =>
      cases bit
      · refine ⟨[.x], ?_⟩
        change triangleEvaluate [.x] = FreeGroup.of false
        simp [triangleGenerator]
      · refine ⟨[.y], ?_⟩
        change triangleEvaluate [.y] = FreeGroup.of true
        simp [triangleGenerator]
  | Ci bit _ =>
      cases bit
      · refine ⟨[.y, .z], ?_⟩
        change triangleEvaluate [.y, .z] = (FreeGroup.of false)⁻¹
        simp [triangleGenerator, mul_assoc]
      · refine ⟨[.z, .x], ?_⟩
        change triangleEvaluate [.z, .x] = (FreeGroup.of true)⁻¹
        simp [triangleGenerator, mul_assoc]
  | Cm left right left_spelling right_spelling =>
      rcases left_spelling with ⟨left_word, left_eq⟩
      rcases right_spelling with ⟨right_word, right_eq⟩
      exact ⟨left_word ++ right_word, by simp [left_eq, right_eq]⟩

/-! ## Quotient-blind boundary collapse -/

/-- Evaluation of a positive word in an arbitrary monoid. -/
def positiveEvaluate {S G : Type*} [Monoid G] (generator : S → G) (word : List S) : G :=
  (word.map generator).prod

@[simp]
theorem positiveEvaluate_nil {S G : Type*} [Monoid G] (generator : S → G) :
    positiveEvaluate generator [] = 1 := by
  simp [positiveEvaluate]

@[simp]
theorem positiveEvaluate_cons {S G : Type*} [Monoid G] (generator : S → G)
    (letter : S) (word : List S) :
    positiveEvaluate generator (letter :: word) =
      generator letter * positiveEvaluate generator word := by
  simp [positiveEvaluate]

@[simp]
theorem positiveEvaluate_append {S G : Type*} [Monoid G] (generator : S → G)
    (left right : List S) :
    positiveEvaluate generator (left ++ right) =
      positiveEvaluate generator left * positiveEvaluate generator right := by
  simp [positiveEvaluate]

/-- A nonempty positive alphabet surjecting onto a group has a nonempty identity spelling. -/
theorem exists_nonempty_positive_identity {S G : Type*} [Nonempty S] [Group G]
    (generator : S → G) (surjective : Function.Surjective (positiveEvaluate generator)) :
    ∃ word : List S, word ≠ [] ∧ positiveEvaluate generator word = 1 := by
  let letter : S := Classical.choice (inferInstance : Nonempty S)
  obtain ⟨tail, tail_eq⟩ := surjective (generator letter)⁻¹
  refine ⟨letter :: tail, by simp, ?_⟩
  rw [positiveEvaluate_cons, tail_eq, mul_inv_cancel]

/-- If fixed group boundaries accept an element and its square, they accept the identity. -/
theorem boundary_eq_of_accept_element_and_square
    {G L : Type*} [Group G] [Group L]
    (upper lower : G →* L) (left right left' right' : L) (element : G)
    (accept_element :
      left * upper element * right = left' * lower element * right')
    (accept_square :
      left * upper (element * element) * right =
        left' * lower (element * element) * right') :
    left * right = left' * right' := by
  let U := upper element
  let V := lower element
  let A := left⁻¹ * left'
  let B := right' * right⁻¹
  have accept_element' : left * U * right = left' * V * right' := by
    exact accept_element
  have accept_square' :
      left * (U * U) * right = left' * (V * V) * right' := by
    simpa [U, V] using accept_square
  have first : U = A * V * B := by
    calc
      U = left⁻¹ * (left * U * right) * right⁻¹ := by group
      _ = left⁻¹ * (left' * V * right') * right⁻¹ := by
        rw [accept_element']
      _ = A * V * B := by simp [A, B]; group
  have second : U * U = A * (V * V) * B := by
    calc
      U * U = left⁻¹ * (left * (U * U) * right) * right⁻¹ := by group
      _ = left⁻¹ * (left' * (V * V) * right') * right⁻¹ := by
        rw [accept_square']
      _ = A * (V * V) * B := by simp [A, B]; group
  have middle : V * B * A * V = V * V := by
    calc
      V * B * A * V = A⁻¹ * ((A * V * B) * (A * V * B)) * B⁻¹ := by group
      _ = A⁻¹ * (U * U) * B⁻¹ := by rw [← first]
      _ = A⁻¹ * (A * (V * V) * B) * B⁻¹ := by rw [second]
      _ = V * V := by group
  have BA : B * A = 1 := by
    calc
      B * A = V⁻¹ * (V * B * A * V) * V⁻¹ := by group
      _ = V⁻¹ * (V * V) * V⁻¹ := by rw [middle]
      _ = 1 := by group
  have B_eq : B = A⁻¹ := by
    calc
      B = B * (A * A⁻¹) := by simp
      _ = (B * A) * A⁻¹ := by group
      _ = A⁻¹ := by rw [BA]; simp
  have AB : A * B = 1 := by rw [B_eq, mul_inv_cancel]
  calc
    left * right = left * (A * B) * right := by rw [AB]; simp
    _ = left' * right' := by simp [A, B]; group

/-- A quotient-blind boundary equation which accepts one element and its square necessarily has a
nonempty positive false witness whenever the positive evaluation surjects onto the group. -/
theorem exists_nonempty_identity_witness
    {S G L : Type*} [Nonempty S] [Group G] [Group L]
    (generator : S → G) (surjective : Function.Surjective (positiveEvaluate generator))
    (upper lower : G →* L) (left right left' right' : L) (element : G)
    (accept_element :
      left * upper element * right = left' * lower element * right')
    (accept_square :
      left * upper (element * element) * right =
        left' * lower (element * element) * right') :
    ∃ word : List S,
      word ≠ [] ∧
        positiveEvaluate generator word = 1 ∧
        left * upper (positiveEvaluate generator word) * right =
          left' * lower (positiveEvaluate generator word) * right' := by
  obtain ⟨word, word_ne, word_eq⟩ :=
    exists_nonempty_positive_identity generator surjective
  have boundary_eq := boundary_eq_of_accept_element_and_square
    upper lower left right left' right' element accept_element accept_square
  refine ⟨word, word_ne, word_eq, ?_⟩
  simp [word_eq, boundary_eq]

/-! ## Finite spelling fibres pump semantic identity loops -/

/-- An injective transition over a finite invariant semantic fibre eventually returns every
point of that fibre to itself. -/
theorem finiteFibre_identity_pumps
    {X Y : Type*} (project : X → Y) (transition : X → X) (semantic : Y → Y)
    (commutes : ∀ point, project (transition point) = semantic (project point))
    (transition_injective : Function.Injective transition) (value : Y)
    (semantic_fixed : semantic value = value) (point : X) (point_mem : project point = value)
    [Finite {candidate // project candidate = value}] :
    ∃ period : Nat, 0 < period ∧ transition^[period] point = point := by
  have orbit_mem : ∀ time : Nat, project (transition^[time] point) = value := by
    intro time
    induction time with
    | zero => simpa using point_mem
    | succ time induction =>
        have iterate_succ :
            transition^[time.succ] point = transition (transition^[time] point) := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using
            Function.iterate_add_apply transition 1 time point
        rw [iterate_succ, commutes, induction, semantic_fixed]
  let orbit : Nat → {candidate // project candidate = value} :=
    fun time => ⟨transition^[time] point, orbit_mem time⟩
  obtain ⟨first, second, distinct, collision⟩ :=
    Finite.exists_ne_map_eq_of_infinite orbit
  have collision_value :
      transition^[first] point = transition^[second] point :=
    congrArg Subtype.val collision
  rcases Nat.lt_or_gt_of_ne distinct with first_lt_second | second_lt_first
  · refine ⟨second - first, Nat.sub_pos_of_lt first_lt_second, ?_⟩
    apply (transition_injective.iterate first)
    calc
      transition^[first] (transition^[second - first] point) =
          transition^[first + (second - first)] point := by
        rw [Function.iterate_add_apply]
      _ = transition^[second] point := by rw [Nat.add_sub_of_le first_lt_second.le]
      _ = transition^[first] point := collision_value.symm
  · refine ⟨first - second, Nat.sub_pos_of_lt second_lt_first, ?_⟩
    apply (transition_injective.iterate second)
    calc
      transition^[second] (transition^[first - second] point) =
          transition^[second + (first - second)] point := by
        rw [Function.iterate_add_apply]
      _ = transition^[first] point := by rw [Nat.add_sub_of_le second_lt_first.le]
      _ = transition^[second] point := collision_value

/-! ## A singular one-coordinate lift absorbs quotient identities -/

/-- A noninjective lift of an injective quotient action with one-dimensional quotient kernel has
the same kernel as the quotient map. -/
theorem singularLift_kernel_eq_quotientKernel
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (quotient : V →ₗ[K] W) (lift : V →ₗ[K] V) (quotientAction : W →ₗ[K] W)
    (compatible : quotient.comp lift = quotientAction.comp quotient)
    (quotientAction_injective : Function.Injective quotientAction)
    (lift_singular : ¬Function.Injective lift)
    (kernel_one : FiniteDimensional.finrank K (LinearMap.ker quotient) = 1) :
    LinearMap.ker lift = LinearMap.ker quotient := by
  have kernel_le : LinearMap.ker lift ≤ LinearMap.ker quotient := by
    intro point point_mem
    have compatible_point :
        quotient (lift point) = quotientAction (quotient point) := by
      simpa using LinearMap.congr_fun compatible point
    have quotientAction_zero : quotientAction (quotient point) = 0 := by
      calc
        quotientAction (quotient point) = quotient (lift point) := compatible_point.symm
        _ = 0 := by rw [LinearMap.mem_ker.mp point_mem]; simp
    exact LinearMap.mem_ker.mpr <| quotientAction_injective (by simpa using quotientAction_zero)
  have lift_kernel_ne_bot : LinearMap.ker lift ≠ ⊥ := by
    intro kernel_bot
    exact lift_singular (LinearMap.ker_eq_bot.mp kernel_bot)
  apply FiniteDimensional.eq_of_le_of_finrank_le kernel_le
  rw [kernel_one]
  exact Submodule.one_le_finrank_iff.mpr lift_kernel_ne_bot

/-- After a singular one-coordinate lift, every later quotient-identity factor is absorbed as an
equality of complete linear maps. -/
theorem singularLift_absorbs_quotientIdentity
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (quotient : V →ₗ[K] W) (lift quotientIdentity : V →ₗ[K] V)
    (quotientAction : W →ₗ[K] W)
    (compatible : quotient.comp lift = quotientAction.comp quotient)
    (quotientAction_injective : Function.Injective quotientAction)
    (lift_singular : ¬Function.Injective lift)
    (kernel_one : FiniteDimensional.finrank K (LinearMap.ker quotient) = 1)
    (identity_downstairs : quotient.comp quotientIdentity = quotient) :
    lift.comp quotientIdentity = lift := by
  have kernel_eq := singularLift_kernel_eq_quotientKernel quotient lift quotientAction compatible
    quotientAction_injective lift_singular kernel_one
  ext point
  have identity_point : quotient (quotientIdentity point) = quotient point := by
    simpa using LinearMap.congr_fun identity_downstairs point
  have difference_mem : quotientIdentity point - point ∈ LinearMap.ker quotient := by
    apply LinearMap.mem_ker.mpr
    rw [quotient.map_sub, identity_point, sub_self]
  have difference_killed : lift (quotientIdentity point - point) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [kernel_eq]
    exact difference_mem
  exact sub_eq_zero.mp (by simpa only [lift.map_sub] using difference_killed)

/-! ## The forbidden-triple zero support has rank six -/

open scoped Matrix

/-- Forced Hankel shape for the language avoiding `xyz`, `yzx`, and `zxy`. The first three rows
are one-letter prefixes and the last three are two-letter prefixes; columns have the same order. -/
def forbiddenTripleSupportMatrix {K : Type*} [Zero K]
    (a b c d e f g h i : K) : Matrix (Fin 6) (Fin 6) K :=
  !![0, 0, 0, 0, a, 0;
     0, 0, 0, 0, 0, b;
     0, 0, 0, c, 0, 0;
     0, 0, d, 0, 0, e;
     f, 0, 0, g, 0, 0;
     0, h, 0, 0, i, 0]

/-- Six private support entries force the forbidden-triple Hankel rows to be independent over
every field; the three remaining nonzero slots are unrestricted. -/
theorem forbiddenTripleSupport_rows_linearIndependent
    {K : Type*} [Field K] (a b c d e f g h i : K)
    (a_ne : a ≠ 0) (b_ne : b ≠ 0) (c_ne : c ≠ 0)
    (d_ne : d ≠ 0) (f_ne : f ≠ 0) (h_ne : h ≠ 0) :
    LinearIndependent K (forbiddenTripleSupportMatrix a b c d e f g h i) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients combination_zero index
  have column_zero := congrFun combination_zero 0
  have column_one := congrFun combination_zero 1
  have column_two := congrFun combination_zero 2
  simp [forbiddenTripleSupportMatrix, Fin.sum_univ_succ] at column_zero
  simp [forbiddenTripleSupportMatrix, Fin.sum_univ_succ] at column_one
  simp [forbiddenTripleSupportMatrix, Fin.sum_univ_succ] at column_two
  have coefficient_four : coefficients 4 = 0 :=
    column_zero.resolve_right f_ne
  have coefficient_five : coefficients 5 = 0 :=
    column_one.resolve_right h_ne
  have coefficient_three : coefficients 3 = 0 :=
    column_two.resolve_right d_ne
  have column_three := congrFun combination_zero 3
  have column_four := congrFun combination_zero 4
  have column_five := congrFun combination_zero 5
  norm_num [forbiddenTripleSupportMatrix, Fin.sum_univ_succ, coefficient_three,
    coefficient_four, coefficient_five] at column_three
  norm_num [forbiddenTripleSupportMatrix, Fin.sum_univ_succ, coefficient_three,
    coefficient_four, coefficient_five] at column_four
  norm_num [forbiddenTripleSupportMatrix, Fin.sum_univ_succ, coefficient_three,
    coefficient_four, coefficient_five] at column_five
  have row_zero_five : ![(0 : K), 0, 0, 0, a, 0] (5 : Fin 6) = 0 := rfl
  have row_one_five : ![(0 : K), 0, 0, 0, 0, b] (5 : Fin 6) = b := rfl
  have row_two_five : ![(0 : K), 0, 0, c, 0, 0] (5 : Fin 6) = 0 := rfl
  have row_three_five : ![(0 : K), 0, d, 0, 0, e] (5 : Fin 6) = e := rfl
  have row_four_five : ![f, (0 : K), 0, g, 0, 0] (5 : Fin 6) = 0 := rfl
  have row_five_five : ![(0 : K), h, 0, 0, i, 0] (5 : Fin 6) = 0 := rfl
  rw [row_zero_five, row_one_five, row_two_five, row_three_five,
    row_four_five, row_five_five] at column_five
  simp only [mul_zero, zero_add, add_zero] at column_five
  change coefficients 2 * c + coefficients 4 * g = 0 at column_three
  change coefficients 0 * a + coefficients 5 * i = 0 at column_four
  change coefficients 1 * b + coefficients 3 * e = 0 at column_five
  simp [coefficient_three, coefficient_four, coefficient_five] at column_three
  simp [coefficient_three, coefficient_four, coefficient_five] at column_four
  simp [coefficient_three, coefficient_four, coefficient_five] at column_five
  have coefficient_two : coefficients 2 = 0 :=
    column_three.resolve_right c_ne
  have coefficient_zero : coefficients 0 = 0 :=
    column_four.resolve_right a_ne
  have coefficient_one : coefficients 1 = 0 :=
    column_five.resolve_right b_ne
  fin_cases index
  · exact coefficient_zero
  · exact coefficient_one
  · exact coefficient_two
  · exact coefficient_three
  · exact coefficient_four
  · exact coefficient_five

/-- Every exact representation of the forced forbidden-triple support has at least six states. -/
theorem six_le_card_of_forbiddenTripleSupport
    {K State : Type*} [Field K] [Fintype State]
    (rows : Fin 6 → State → K) (columns : Fin 6 → State → K)
    (a b c d e f g h i : K)
    (coefficient_eq :
      (fun row column => Matrix.dotProduct (rows row) (columns column)) =
        forbiddenTripleSupportMatrix a b c d e f g h i)
    (a_ne : a ≠ 0) (b_ne : b ≠ 0) (c_ne : c ≠ 0)
    (d_ne : d ≠ 0) (f_ne : f ≠ 0) (h_ne : h ≠ 0) :
    6 ≤ Fintype.card State := by
  let probe : (State → K) →ₗ[K] (Fin 6 → K) :=
    { toFun := fun vector column => Matrix.dotProduct vector (columns column)
      map_add' := by
        intro left right
        funext column
        exact Matrix.add_dotProduct left right (columns column)
      map_smul' := by
        intro scalar vector
        funext column
        exact Matrix.smul_dotProduct scalar vector (columns column) }
  have probe_row (row : Fin 6) :
      probe (rows row) = forbiddenTripleSupportMatrix a b c d e f g h i row := by
    funext column
    exact congrFun (congrFun coefficient_eq row) column
  have row_independent : LinearIndependent K rows := by
    rw [Fintype.linearIndependent_iff]
    intro coefficients combination_zero index
    have support_independent := forbiddenTripleSupport_rows_linearIndependent
      a b c d e f g h i a_ne b_ne c_ne d_ne f_ne h_ne
    rw [Fintype.linearIndependent_iff] at support_independent
    apply support_independent coefficients ?_ index
    calc
      ∑ row, coefficients row • forbiddenTripleSupportMatrix a b c d e f g h i row =
          ∑ row, coefficients row • probe (rows row) := by
        apply Finset.sum_congr rfl
        intro row _
        rw [probe_row]
      _ = probe (∑ row, coefficients row • rows row) := by
        simp
      _ = 0 := by rw [combination_zero]; exact probe.map_zero
  simpa [FiniteDimensional.finrank_fintype_fun_eq_card] using
    row_independent.fintype_card_le_finrank

end PositiveFreeCancellation

end MatrixMortality

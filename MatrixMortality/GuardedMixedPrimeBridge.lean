import MatrixMortality.GuardedTwoStateLift
import MatrixMortality.MixedPrimeKernel
import MatrixMortality.BranchingHistory

/-!
# Guarded mixed-prime endpoint bridge

The homogeneous integral model of the mixed-prime affine benchmark supplies every parity premise
of `GuardedTwoStateLift` from an odd source denominator. For arbitrary control macros, its scalar
gate is exactly fixed rational endpoint reachability. The `bcbc` fork separately forces three
distinct induced core matrices and endpoint actions, excluding every letterwise encoding into the
two raw benchmark letters.
-/

namespace MatrixMortality.GuardedMixedPrimeBridge

open scoped Matrix
open GuardedTwoStateLift
open MixedPrimeKernel

/-- Homogeneous integral matrices for `D(z)=(2/3)z` and `T(z)=(3/5)z+1`. -/
def benchmarkMatrix : Letter → CoreMatrix
  | .dilate => !![2, 0; 0, 3]
  | .translate => !![3, 5; 0, 5]

/-- Multiplier of the lower homogeneous coordinate for one benchmark letter. -/
def bottomScale : Letter → ℤ
  | .dilate => 3
  | .translate => 5

theorem wordProduct_bottom (word : List Letter) (state : CoreState) :
    (wordProduct benchmarkMatrix word *ᵥ state) 1 =
      (word.map bottomScale).prod * state 1 := by
  induction word with
  | nil => simp [wordProduct]
  | cons letter word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
      have induction_expanded :
          wordProduct benchmarkMatrix word 1 0 * state 0 +
              wordProduct benchmarkMatrix word 1 1 * state 1 =
            (word.map bottomScale).prod * state 1 := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using induction
      cases letter <;>
        simp [benchmarkMatrix, bottomScale, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, induction_expanded, mul_assoc]

theorem bottomScale_prod_ne_zero (word : List Letter) :
    (word.map bottomScale).prod ≠ 0 := by
  induction word with
  | nil => simp
  | cons letter word induction =>
      cases letter <;> simp [bottomScale, induction]

theorem wordProduct_bottom_ne_zero
    (word : List Letter) (state : CoreState) (state_bottom_ne : state 1 ≠ 0) :
    (wordProduct benchmarkMatrix word *ᵥ state) 1 ≠ 0 := by
  rw [wordProduct_bottom]
  exact mul_ne_zero (bottomScale_prod_ne_zero word) state_bottom_ne

/-- Affine ratio represented by a homogeneous two-state column. -/
def affineValue (state : CoreState) : ℚ := (state 0 : ℚ) / state 1

theorem affineValue_benchmarkMatrix_mulVec
    (letter : Letter) (state : CoreState) (state_bottom_ne : state 1 ≠ 0) :
    affineValue (benchmarkMatrix letter *ᵥ state) = action letter (affineValue state) := by
  cases letter <;>
    simp [affineValue, benchmarkMatrix, action, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    field_simp

theorem affineValue_wordProduct
    (word : List Letter) (state : CoreState) (state_bottom_ne : state 1 ≠ 0) :
    affineValue (wordProduct benchmarkMatrix word *ᵥ state) =
      wordAction word (affineValue state) := by
  induction word with
  | nil => simp [wordProduct, wordAction]
  | cons letter word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
      rw [affineValue_benchmarkMatrix_mulVec letter
        (wordProduct benchmarkMatrix word *ᵥ state)
        (wordProduct_bottom_ne_zero word state state_bottom_ne)]
      rw [induction]
      rfl

/-- Integral homogeneous representative of a rational source. -/
def endpointColumn (numerator denominator : ℤ) : CoreState :=
  ![numerator, denominator]

/-- Integral row whose kernel is the projective ray of the stated rational endpoint. -/
def endpointGate (numerator denominator : ℤ) : CoreState :=
  ![denominator, -numerator]

theorem endpointGate_dot_eq_zero_iff
    (source : CoreState) (source_bottom_ne : source 1 ≠ 0)
    (targetNumerator targetDenominator : ℤ) (target_denominator_ne : targetDenominator ≠ 0) :
    endpointGate targetNumerator targetDenominator ⬝ᵥ source = 0 ↔
      affineValue source = (targetNumerator : ℚ) / targetDenominator := by
  change endpointGate targetNumerator targetDenominator ⬝ᵥ source = 0 ↔
    (source 0 : ℚ) / source 1 = (targetNumerator : ℚ) / targetDenominator
  rw [div_eq_div_iff (Int.cast_ne_zero.mpr source_bottom_ne)
    (Int.cast_ne_zero.mpr target_denominator_ne)]
  simp only [endpointGate, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Fin.isValue]
  norm_cast
  constructor
  · intro zero
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg, mul_comm] using zero)
  · intro cross
    simpa [sub_eq_add_neg, mul_comm] using sub_eq_zero.mpr cross

/-- Concatenated benchmark macro attached to a raw paired-control word. -/
def encodedWord (code : PairedControl → List Letter) (word : List PairedControl) : List Letter :=
  word.flatMap code

/-- Integral two-state action induced by one benchmark macro. -/
def encodedGenerator (code : PairedControl → List Letter) (control : PairedControl) : CoreMatrix :=
  wordProduct benchmarkMatrix (code control)

theorem wordProduct_encodedGenerator
    (code : PairedControl → List Letter) (word : List PairedControl) :
    wordProduct (encodedGenerator code) word =
      wordProduct benchmarkMatrix (encodedWord code word) := by
  induction word with
  | nil => simp [encodedWord, wordProduct]
  | cons control word induction =>
      rw [wordProduct_cons, encodedWord, List.flatMap_cons, wordProduct_append,
        encodedGenerator, induction]
      rfl

/-- The mixed-prime benchmark as a guarded terminal core with fixed rational endpoints. -/
def benchmarkCore
    (code : PairedControl → List Letter)
    (sourceNumerator sourceDenominator targetNumerator targetDenominator : ℤ) : TerminalCore where
  generator := encodedGenerator code
  column := endpointColumn sourceNumerator sourceDenominator
  gate := endpointGate targetNumerator targetDenominator

theorem benchmarkCore_coreState
    (code : PairedControl → List Letter)
    (sourceNumerator sourceDenominator targetNumerator targetDenominator : ℤ)
    (word : List PairedControl) :
    coreState
        (benchmarkCore code sourceNumerator sourceDenominator targetNumerator targetDenominator)
        word =
      wordProduct benchmarkMatrix (encodedWord code word) *ᵥ
        endpointColumn sourceNumerator sourceDenominator := by
  rw [coreState, benchmarkCore, wordProduct_encodedGenerator]

theorem bottomScale_prod_odd (word : List Letter) :
    Odd (word.map bottomScale).prod := by
  induction word with
  | nil => simp
  | cons letter word induction =>
      cases letter with
      | dilate =>
          exact (by norm_num : Odd (3 : ℤ)).mul induction
      | translate =>
          exact (by norm_num : Odd (5 : ℤ)).mul induction

theorem benchmarkCore_coreState_second_odd
    (code : PairedControl → List Letter)
    (sourceNumerator sourceDenominator targetNumerator targetDenominator : ℤ)
    (source_denominator_odd : Odd sourceDenominator) (word : List PairedControl) :
    Odd
      (coreState
        (benchmarkCore code sourceNumerator sourceDenominator targetNumerator targetDenominator)
        word 1) := by
  rw [benchmarkCore_coreState, wordProduct_bottom]
  exact (bottomScale_prod_odd (encodedWord code word)).mul source_denominator_odd

/-- The guarded two-state gate is exactly fixed-endpoint reachability in the block-coded
mixed-prime benchmark. -/
theorem benchmarkCore_gate_eq_zero_iff
    (code : PairedControl → List Letter)
    (sourceNumerator sourceDenominator targetNumerator targetDenominator : ℤ)
    (source_denominator_ne : sourceDenominator ≠ 0)
    (target_denominator_ne : targetDenominator ≠ 0)
    (word : List PairedControl) :
    let core :=
      benchmarkCore code sourceNumerator sourceDenominator targetNumerator targetDenominator
    core.gate ⬝ᵥ coreState core word = 0 ↔
      wordAction (encodedWord code word)
          ((sourceNumerator : ℚ) / sourceDenominator) =
        (targetNumerator : ℚ) / targetDenominator := by
  dsimp only
  rw [benchmarkCore_coreState]
  change endpointGate targetNumerator targetDenominator ⬝ᵥ
      (wordProduct benchmarkMatrix (encodedWord code word) *ᵥ
        endpointColumn sourceNumerator sourceDenominator) = 0 ↔ _
  rw [endpointGate_dot_eq_zero_iff
    (wordProduct benchmarkMatrix (encodedWord code word) *ᵥ
      endpointColumn sourceNumerator sourceDenominator)
    (wordProduct_bottom_ne_zero (encodedWord code word)
      (endpointColumn sourceNumerator sourceDenominator) (by
        simpa [endpointColumn] using source_denominator_ne))
    targetNumerator targetDenominator target_denominator_ne]
  rw [affineValue_wordProduct (encodedWord code word)
    (endpointColumn sourceNumerator sourceDenominator) (by
      simpa [endpointColumn] using source_denominator_ne)]
  rfl

/-- For the benchmark specialization of the guarded lift, complete same-zero correctness is
equivalent to one fixed-endpoint query for every encoded suffix. -/
theorem benchmarkCore_allWords_sameZero_iff_endpoint
    (code : PairedControl → List Letter)
    (sourceNumerator sourceDenominator targetNumerator targetDenominator : ℤ)
    (source_denominator_odd : Odd sourceDenominator)
    (target_denominator_ne : targetDenominator ≠ 0)
    (beta : Nat) (body : List TagLetter) (beta_pos : 0 < beta) :
    let core :=
      benchmarkCore code sourceNumerator sourceDenominator targetNumerator targetDenominator
    (∀ word,
      coefficient core word = 0 ↔ pairedCoefficient ℚ beta body word = 0) ↔
    (∀ word,
      wordAction (encodedWord code word)
          ((sourceNumerator : ℚ) / sourceDenominator) =
          (targetNumerator : ℚ) / targetDenominator ↔
        pairedCoefficient ℚ beta body (.data .c :: word) = 0) := by
  dsimp only
  let core :=
    benchmarkCore code sourceNumerator sourceDenominator targetNumerator targetDenominator
  have source_denominator_ne : sourceDenominator ≠ 0 := by
    obtain ⟨half, denominator_eq⟩ := source_denominator_odd
    omega
  have core_odd : ∀ word, Odd (coreState core word 1) :=
    benchmarkCore_coreState_second_odd code sourceNumerator sourceDenominator
      targetNumerator targetDenominator source_denominator_odd
  rw [allWords_sameZero_iff_data_c_gate core core_odd beta body beta_pos]
  constructor
  · intro gate_exact word
    have gate_endpoint :
        core.gate ⬝ᵥ coreState core word = 0 ↔
          wordAction (encodedWord code word)
              ((sourceNumerator : ℚ) / sourceDenominator) =
            (targetNumerator : ℚ) / targetDenominator := by
      simpa only [core] using
        benchmarkCore_gate_eq_zero_iff code sourceNumerator sourceDenominator
          targetNumerator targetDenominator source_denominator_ne target_denominator_ne word
    exact gate_endpoint.symm.trans (gate_exact word)
  · intro endpoint_exact word
    have gate_endpoint :
        core.gate ⬝ᵥ coreState core word = 0 ↔
          wordAction (encodedWord code word)
              ((sourceNumerator : ℚ) / sourceDenominator) =
            (targetNumerator : ℚ) / targetDenominator := by
      simpa only [core] using
        benchmarkCore_gate_eq_zero_iff code sourceNumerator sourceDenominator
          targetNumerator targetDenominator source_denominator_ne target_denominator_ne word
    exact gate_endpoint.trans (endpoint_exact word)

/-- Source-family form of the mixed-prime endpoint reduction. A concrete computable choice of
the five function parameters is a uniform guarded compiler exactly when its encoded endpoint
queries realize all paired `c`-suffix zeros. -/
theorem benchmarkFamily_sameZero_iff_endpoint
    (code : Nat → List TagLetter → PairedControl → List Letter)
    (sourceNumerator sourceDenominator targetNumerator targetDenominator :
      Nat → List TagLetter → ℤ)
    (source_denominator_odd : ∀ beta body, Odd (sourceDenominator beta body))
    (target_denominator_ne : ∀ beta body, targetDenominator beta body ≠ 0) :
    (∀ beta body, 0 < beta → ∀ word,
      coefficient
          (benchmarkCore (code beta body)
            (sourceNumerator beta body) (sourceDenominator beta body)
            (targetNumerator beta body) (targetDenominator beta body))
          word = 0 ↔
        pairedCoefficient ℚ beta body word = 0) ↔
    (∀ beta body, 0 < beta → ∀ word,
      wordAction (encodedWord (code beta body) word)
          ((sourceNumerator beta body : ℚ) / sourceDenominator beta body) =
          (targetNumerator beta body : ℚ) / targetDenominator beta body ↔
        pairedCoefficient ℚ beta body (.data .c :: word) = 0) := by
  constructor
  · intro same_zero beta body beta_pos
    exact
      (benchmarkCore_allWords_sameZero_iff_endpoint
        (code beta body)
        (sourceNumerator beta body) (sourceDenominator beta body)
        (targetNumerator beta body) (targetDenominator beta body)
        (source_denominator_odd beta body) (target_denominator_ne beta body)
        beta body beta_pos).mp (same_zero beta body beta_pos)
  · intro endpoint_exact beta body beta_pos
    exact
      (benchmarkCore_allWords_sameZero_iff_endpoint
        (code beta body)
        (sourceNumerator beta body) (sourceDenominator beta body)
        (targetNumerator beta body) (targetDenominator beta body)
        (source_denominator_odd beta body) (target_denominator_ne beta body)
        beta body beta_pos).mpr (endpoint_exact beta body beta_pos)

/-- Suffix of the fixed accepted `bcbc` terminal control after its leading data `c`. -/
def terminalSuffix : List PairedControl :=
  [.toggle, .data .b, .data .c, .data .b, .toggle, .data .c, .data .b, .toggle]

/-- Rejected suffix colliding with `terminalSuffix` when the two data generators agree. -/
def dataBCollisionSuffix : List PairedControl :=
  [.toggle, .data .c, .data .c, .data .b, .toggle, .data .c, .data .b, .toggle]

/-- Rejected suffix colliding with `terminalSuffix` when data `b` equals the toggle. -/
def toggleBCollisionSuffix : List PairedControl :=
  [.data .b, .data .b, .data .c, .data .b, .toggle, .data .c, .data .b, .toggle]

/-- Rejected suffix colliding with `terminalSuffix` when data `c` equals the toggle. -/
def toggleCCollisionSuffix : List PairedControl :=
  [.data .c, .data .b, .data .c, .data .b, .toggle, .data .c, .data .b, .toggle]

theorem pairedCoefficient_terminalSuffix_eq_zero :
    pairedCoefficient ℚ 3 BranchingHistory.bcbcBody (.data .c :: terminalSuffix) = 0 := by
  simpa [terminalSuffix, BranchingHistory.bcbcTerminalControl] using
    BranchingHistory.bcbc_terminal_nearFork.1

private theorem pairedCoefficient_ne_zero_of_nonterminal
    (suffix : List PairedControl)
    (nonterminal :
      spell (nearyUpper 3) (decodePairedWord (.data .c :: suffix)) ++ nearyMarker 3 ≠
        spell (nearyLower 3 BranchingHistory.bcbcBody)
          (decodePairedWord (.data .c :: suffix))) :
    pairedCoefficient ℚ 3 BranchingHistory.bcbcBody (.data .c :: suffix) ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro coefficient_zero
  exact nonterminal
    ((sideCoefficient_eq_zero_iff_terminal_match_rat 3 BranchingHistory.bcbcBody _).mp
      coefficient_zero)

theorem pairedCoefficient_dataBCollisionSuffix_ne_zero :
    pairedCoefficient ℚ 3 BranchingHistory.bcbcBody
      (.data .c :: dataBCollisionSuffix) ≠ 0 := by
  apply pairedCoefficient_ne_zero_of_nonterminal
  decide

theorem pairedCoefficient_toggleBCollisionSuffix_ne_zero :
    pairedCoefficient ℚ 3 BranchingHistory.bcbcBody
      (.data .c :: toggleBCollisionSuffix) ≠ 0 := by
  apply pairedCoefficient_ne_zero_of_nonterminal
  decide

theorem pairedCoefficient_toggleCCollisionSuffix_ne_zero :
    pairedCoefficient ℚ 3 BranchingHistory.bcbcBody
      (.data .c :: toggleCCollisionSuffix) ≠ 0 := by
  apply pairedCoefficient_ne_zero_of_nonterminal
  decide

theorem terminalSuffix_state_eq_dataBCollisionSuffix
    (core : TerminalCore)
    (equal : core.generator (.data .b) = core.generator (.data .c)) :
    coreState core terminalSuffix = coreState core dataBCollisionSuffix := by
  simp [coreState, terminalSuffix, dataBCollisionSuffix, wordProduct, equal]

theorem terminalSuffix_state_eq_toggleBCollisionSuffix
    (core : TerminalCore)
    (equal : core.generator (.data .b) = core.generator .toggle) :
    coreState core terminalSuffix = coreState core toggleBCollisionSuffix := by
  simp [coreState, terminalSuffix, toggleBCollisionSuffix, wordProduct, equal]

theorem terminalSuffix_state_eq_toggleCCollisionSuffix
    (core : TerminalCore)
    (equal : core.generator (.data .c) = core.generator .toggle) :
    coreState core terminalSuffix = coreState core toggleCCollisionSuffix := by
  simp [coreState, terminalSuffix, toggleCCollisionSuffix, wordProduct, equal]

private theorem terminalSuffix_action_eq_dataBCollisionSuffix
    (code : PairedControl → List Letter) (source : ℚ)
    (equal : ∀ state,
      wordAction (code (.data .b)) state = wordAction (code (.data .c)) state) :
    wordAction (encodedWord code terminalSuffix) source =
      wordAction (encodedWord code dataBCollisionSuffix) source := by
  simp only [encodedWord, terminalSuffix, dataBCollisionSuffix, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, wordAction_append]
  rw [equal]

private theorem terminalSuffix_action_eq_toggleBCollisionSuffix
    (code : PairedControl → List Letter) (source : ℚ)
    (equal : ∀ state,
      wordAction (code (.data .b)) state = wordAction (code .toggle) state) :
    wordAction (encodedWord code terminalSuffix) source =
      wordAction (encodedWord code toggleBCollisionSuffix) source := by
  simp only [encodedWord, terminalSuffix, toggleBCollisionSuffix, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, wordAction_append]
  rw [← equal]

private theorem terminalSuffix_action_eq_toggleCCollisionSuffix
    (code : PairedControl → List Letter) (source : ℚ)
    (equal : ∀ state,
      wordAction (code (.data .c)) state = wordAction (code .toggle) state) :
    wordAction (encodedWord code terminalSuffix) source =
      wordAction (encodedWord code toggleCCollisionSuffix) source := by
  simp only [encodedWord, terminalSuffix, toggleCCollisionSuffix, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, wordAction_append]
  rw [← equal]

/-- Any two-state core satisfying the `bcbc` suffix gate must assign pairwise distinct matrices
to the three raw controls. -/
theorem bcbc_gate_generators_pairwise_ne
    (core : TerminalCore)
    (data_c_exact : ∀ word,
      core.gate ⬝ᵥ coreState core word = 0 ↔
        pairedCoefficient ℚ 3 BranchingHistory.bcbcBody (.data .c :: word) = 0) :
    core.generator (.data .b) ≠ core.generator (.data .c) ∧
      core.generator (.data .b) ≠ core.generator .toggle ∧
      core.generator (.data .c) ≠ core.generator .toggle := by
  have terminal_zero : core.gate ⬝ᵥ coreState core terminalSuffix = 0 :=
    (data_c_exact terminalSuffix).mpr pairedCoefficient_terminalSuffix_eq_zero
  have data_b_collision_ne :
      core.gate ⬝ᵥ coreState core dataBCollisionSuffix ≠ 0 := by
    intro collision_zero
    exact pairedCoefficient_dataBCollisionSuffix_ne_zero
      ((data_c_exact dataBCollisionSuffix).mp collision_zero)
  have toggle_b_collision_ne :
      core.gate ⬝ᵥ coreState core toggleBCollisionSuffix ≠ 0 := by
    intro collision_zero
    exact pairedCoefficient_toggleBCollisionSuffix_ne_zero
      ((data_c_exact toggleBCollisionSuffix).mp collision_zero)
  have toggle_c_collision_ne :
      core.gate ⬝ᵥ coreState core toggleCCollisionSuffix ≠ 0 := by
    intro collision_zero
    exact pairedCoefficient_toggleCCollisionSuffix_ne_zero
      ((data_c_exact toggleCCollisionSuffix).mp collision_zero)
  constructor
  · intro equal
    apply data_b_collision_ne
    rw [← terminalSuffix_state_eq_dataBCollisionSuffix core equal]
    exact terminal_zero
  constructor
  · intro equal
    apply toggle_b_collision_ne
    rw [← terminalSuffix_state_eq_toggleBCollisionSuffix core equal]
    exact terminal_zero
  · intro equal
    apply toggle_c_collision_ne
    rw [← terminalSuffix_state_eq_toggleCCollisionSuffix core equal]
    exact terminal_zero

/-- Any block-coded benchmark endpoint language realizing the `bcbc` suffix gate assigns
pairwise distinct affine actions to the three control macros. -/
theorem bcbc_macro_actions_pairwise_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 BranchingHistory.bcbcBody (.data .c :: word) = 0) :
    (¬ ∀ state,
      wordAction (code (.data .b)) state = wordAction (code (.data .c)) state) ∧
    (¬ ∀ state,
      wordAction (code (.data .b)) state = wordAction (code .toggle) state) ∧
    (¬ ∀ state,
      wordAction (code (.data .c)) state = wordAction (code .toggle) state) := by
  have terminal_endpoint :
      wordAction (encodedWord code terminalSuffix) source = target :=
    (endpoint_exact terminalSuffix).mpr pairedCoefficient_terminalSuffix_eq_zero
  have data_b_collision_ne :
      wordAction (encodedWord code dataBCollisionSuffix) source ≠ target := by
    intro collision_endpoint
    exact pairedCoefficient_dataBCollisionSuffix_ne_zero
      ((endpoint_exact dataBCollisionSuffix).mp collision_endpoint)
  have toggle_b_collision_ne :
      wordAction (encodedWord code toggleBCollisionSuffix) source ≠ target := by
    intro collision_endpoint
    exact pairedCoefficient_toggleBCollisionSuffix_ne_zero
      ((endpoint_exact toggleBCollisionSuffix).mp collision_endpoint)
  have toggle_c_collision_ne :
      wordAction (encodedWord code toggleCCollisionSuffix) source ≠ target := by
    intro collision_endpoint
    exact pairedCoefficient_toggleCCollisionSuffix_ne_zero
      ((endpoint_exact toggleCCollisionSuffix).mp collision_endpoint)
  constructor
  · intro equal
    apply data_b_collision_ne
    rw [← terminalSuffix_action_eq_dataBCollisionSuffix code source equal]
    exact terminal_endpoint
  constructor
  · intro equal
    apply toggle_b_collision_ne
    rw [← terminalSuffix_action_eq_toggleBCollisionSuffix code source equal]
    exact terminal_endpoint
  · intro equal
    apply toggle_c_collision_ne
    rw [← terminalSuffix_action_eq_toggleCCollisionSuffix code source equal]
    exact terminal_endpoint

/-- Benchmark core induced by a single raw benchmark letter for each paired control. -/
def letterwiseBenchmarkCore
    (code : PairedControl → Letter) (column gate : CoreState) : TerminalCore where
  generator := benchmarkMatrix ∘ code
  column := column
  gate := gate

theorem three_control_code_collision (code : PairedControl → Letter) :
    code (.data .b) = code (.data .c) ∨
      code (.data .b) = code .toggle ∨
      code (.data .c) = code .toggle := by
  cases code (.data .b) <;> cases code (.data .c) <;> cases code .toggle <;> simp

/-- No letterwise relabeling of the three paired controls into the two raw mixed-prime letters
can satisfy the `bcbc` suffix gate, regardless of the chosen endpoint column and gate row. -/
theorem no_letterwise_benchmark_bcbc_gate
    (code : PairedControl → Letter) (column gate : CoreState) :
    ¬ ∀ word,
      (letterwiseBenchmarkCore code column gate).gate ⬝ᵥ
          coreState (letterwiseBenchmarkCore code column gate) word = 0 ↔
        pairedCoefficient ℚ 3 BranchingHistory.bcbcBody (.data .c :: word) = 0 := by
  intro data_c_exact
  obtain ⟨data_ne, toggle_b_ne, toggle_c_ne⟩ :=
    bcbc_gate_generators_pairwise_ne
      (letterwiseBenchmarkCore code column gate) data_c_exact
  rcases three_control_code_collision code with data_equal | toggle_b_equal | toggle_c_equal
  · exact data_ne (congrArg benchmarkMatrix data_equal)
  · exact toggle_b_ne (congrArg benchmarkMatrix toggle_b_equal)
  · exact toggle_c_ne (congrArg benchmarkMatrix toggle_c_equal)

end MatrixMortality.GuardedMixedPrimeBridge

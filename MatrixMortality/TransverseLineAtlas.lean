import MatrixMortality.PhaseFracture

/-!
# Projectively involutive transverse actions have a finite line atlas

Two singular data controls cannot produce a genuinely two-dimensional projective orbit when the
phase toggle is projectively involutive. Every raw control word lands in one of two boundary
subspaces of vector dimension at most one or four data-image subspaces of vector dimension at
most two. The latter are projective-line charts only when the relevant data map has rank exactly
two. An arbitrary terminal row cuts every carrier in the whole carrier or a subspace of vector
dimension at most one.
-/

namespace MatrixMortality
namespace TransverseLineAtlas

open scoped Matrix

/-- Three-dimensional rational state space. -/
abbrev State := Fin 3 → ℚ
/-- Rational control matrices acting on the state space. -/
abbrev ControlMatrix := Matrix (Fin 3) (Fin 3) ℚ

/-- The two boundary-ray charts and the four optionally toggled data-image charts. -/
inductive Chart
  | boundary : Bool → Chart
  | data : Bool → TagLetter → Chart
  deriving DecidableEq, Fintype

theorem chart_count : Fintype.card Chart = 6 := by decide

/-- Exchange the untoggled and toggled version of one carrier. -/
def Chart.flip : Chart → Chart
  | .boundary toggled => .boundary (!toggled)
  | .data toggled letter => .data (!toggled) letter

/-- Canonical carrier selected by the parity of the leading toggles and the first data control.
The suffix following that first data control does not affect the carrier label. -/
def wordChart : List PairedControl → Chart
  | [] => .boundary false
  | .data letter :: _ => .data false letter
  | .toggle :: word => (wordChart word).flip

/-- Three controls assembled from two data maps and one phase toggle. -/
def generator (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) :
    PairedControl → ControlMatrix
  | .data letter => data letter
  | .toggle => toggle

/-- Exact normal forms of reachable columns before passing to their carrier subspaces. Scalars
are retained on the two boundary rays; data-image scalars are absorbed into the input vector. -/
inductive ReachableForm (data : TagLetter → ControlMatrix) (toggle : ControlMatrix)
    (column : State) : State → Prop
  | boundary (scalar : ℚ) : ReachableForm data toggle column (scalar • column)
  | toggledBoundary (scalar : ℚ) :
      ReachableForm data toggle column (scalar • (toggle *ᵥ column))
  | data (letter : TagLetter) (vector : State) :
      ReachableForm data toggle column (data letter *ᵥ vector)
  | toggledData (letter : TagLetter) (vector : State) :
      ReachableForm data toggle column (toggle *ᵥ (data letter *ᵥ vector))

private theorem toggle_twice_mulVec (toggle : ControlMatrix) (scalar : ℚ)
    (toggleSquare : toggle * toggle = scalar • 1) (vector : State) :
    toggle *ᵥ (toggle *ᵥ vector) = scalar • vector := by
  calc
    toggle *ᵥ (toggle *ᵥ vector) = (toggle * toggle) *ᵥ vector := by
      rw [Matrix.mulVec_mulVec]
    _ = (scalar • (1 : ControlMatrix)) *ᵥ vector := by rw [toggleSquare]
    _ = scalar • vector := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem reachableForm_toggle
    {data : TagLetter → ControlMatrix} {toggle : ControlMatrix} {column state : State}
    {toggleScalar : ℚ} (toggleSquare : toggle * toggle = toggleScalar • 1)
    (form : ReachableForm data toggle column state) :
    ReachableForm data toggle column (toggle *ᵥ state) := by
  cases form with
  | boundary scalar =>
      rw [Matrix.mulVec_smul]
      exact ReachableForm.toggledBoundary scalar
  | toggledBoundary scalar =>
      rw [Matrix.mulVec_smul,
        toggle_twice_mulVec toggle toggleScalar toggleSquare column]
      simpa [smul_smul, mul_comm] using
        ReachableForm.boundary (data := data) (toggle := toggle) (column := column)
          (scalar * toggleScalar)
  | data letter vector =>
      exact ReachableForm.toggledData letter vector
  | toggledData letter vector =>
      rw [toggle_twice_mulVec toggle toggleScalar toggleSquare (data letter *ᵥ vector),
        ← Matrix.mulVec_smul]
      exact ReachableForm.data letter (toggleScalar • vector)

/-- Every raw control word has one of six exact forms when the toggle is projectively
involutive. No source grammar or intended-word restriction is used. -/
theorem reachableForm
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (toggleScalar : ℚ) (toggleSquare : toggle * toggle = toggleScalar • 1)
    (word : List PairedControl) :
    ReachableForm data toggle column
      (wordProduct (generator data toggle) word *ᵥ column) := by
  induction word with
  | nil =>
      simpa [wordProduct] using
        ReachableForm.boundary (data := data) (toggle := toggle) (column := column) 1
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
      cases control with
      | data letter =>
          exact ReachableForm.data (data := data) (toggle := toggle) (column := column) letter
            (wordProduct (generator data toggle) word *ᵥ column)
      | toggle =>
          exact reachableForm_toggle toggleSquare induction

/-- Linear carrier of one chart. Nonzero boundary charts are rays; data charts are data-image
subspaces, optionally mapped by the toggle. -/
def carrier (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State) :
    Chart → Submodule ℚ State
  | .boundary false => Submodule.span ℚ {column}
  | .boundary true => Submodule.span ℚ {toggle *ᵥ column}
  | .data false letter => LinearMap.range (Matrix.toLin' (data letter))
  | .data true letter =>
      (LinearMap.range (Matrix.toLin' (data letter))).map (Matrix.toLin' toggle)

private theorem reachableForm_mem_carrier
    {data : TagLetter → ControlMatrix} {toggle : ControlMatrix} {column state : State}
    (form : ReachableForm data toggle column state) :
    ∃ chart, state ∈ carrier data toggle column chart := by
  cases form with
  | boundary scalar =>
      refine ⟨.boundary false, Submodule.smul_mem _ scalar ?_⟩
      exact Submodule.subset_span (Set.mem_singleton column)
  | toggledBoundary scalar =>
      refine ⟨.boundary true, Submodule.smul_mem _ scalar ?_⟩
      exact Submodule.subset_span (Set.mem_singleton (toggle *ᵥ column))
  | data letter vector =>
      refine ⟨.data false letter, ?_⟩
      exact ⟨vector, rfl⟩
  | toggledData letter vector =>
      refine ⟨.data true letter, ?_⟩
      exact ⟨data letter *ᵥ vector, ⟨vector, rfl⟩, rfl⟩

private theorem toggle_mulVec_mem_flip_carrier
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (toggleScalar : ℚ) (toggleSquare : toggle * toggle = toggleScalar • 1)
    {chart : Chart} {state : State} (stateInCarrier : state ∈ carrier data toggle column chart) :
    toggle *ᵥ state ∈ carrier data toggle column chart.flip := by
  cases chart with
  | boundary toggled =>
      cases toggled with
      | false =>
          obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp stateInCarrier
          rw [Matrix.mulVec_smul]
          exact Submodule.smul_mem _ scalar
            (Submodule.subset_span (Set.mem_singleton (toggle *ᵥ column)))
      | true =>
          obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp stateInCarrier
          rw [Matrix.mulVec_smul,
            toggle_twice_mulVec toggle toggleScalar toggleSquare column]
          exact Submodule.smul_mem _ scalar (Submodule.smul_mem _ toggleScalar
            (Submodule.subset_span (Set.mem_singleton column)))
  | data toggled letter =>
      cases toggled with
      | false =>
          exact ⟨state, stateInCarrier, rfl⟩
      | true =>
          obtain ⟨vector, vectorInRange, rfl⟩ := stateInCarrier
          change toggle *ᵥ (toggle *ᵥ vector) ∈
            LinearMap.range (Matrix.toLin' (data letter))
          rw [toggle_twice_mulVec toggle toggleScalar toggleSquare vector]
          exact Submodule.smul_mem _ toggleScalar vectorInRange

/-- The raw orbit lies in a deterministic one of the six carriers. Its label is finite-state:
only the leading-toggle parity and first data control matter. -/
theorem wordProduct_mulVec_mem_wordChart
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (toggleScalar : ℚ) (toggleSquare : toggle * toggle = toggleScalar • 1)
    (word : List PairedControl) :
    wordProduct (generator data toggle) word *ᵥ column ∈
      carrier data toggle column (wordChart word) := by
  induction word with
  | nil =>
      change (1 : ControlMatrix) *ᵥ column ∈ Submodule.span ℚ {column}
      rw [Matrix.one_mulVec]
      exact Submodule.subset_span (Set.mem_singleton column)
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
      cases control with
      | data letter =>
          exact ⟨wordProduct (generator data toggle) word *ᵥ column, rfl⟩
      | toggle =>
          exact toggle_mulVec_mem_flip_carrier data toggle column toggleScalar toggleSquare
            induction

/-- The complete reachable orbit is covered by six fixed linear subspaces. The nonzero scalar
hypothesis distinguishes a projective involution from a merely square-zero toggle. -/
theorem reachable_mem_carrier
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (toggleScalar : ℚ) (_toggleScalar_ne : toggleScalar ≠ 0)
    (toggleSquare : toggle * toggle = toggleScalar • 1)
    (word : List PairedControl) :
    ∃ chart,
      wordProduct (generator data toggle) word *ᵥ column ∈
        carrier data toggle column chart :=
  reachableForm_mem_carrier (reachableForm data toggle column toggleScalar toggleSquare word)

/-- Exact involutions are the scalar-one specialization of the projective theorem. -/
theorem reachable_mem_carrier_of_involutive
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (toggleSquare : toggle * toggle = 1) (word : List PairedControl) :
    ∃ chart,
      wordProduct (generator data toggle) word *ᵥ column ∈
        carrier data toggle column chart := by
  apply reachable_mem_carrier data toggle column 1 (by norm_num)
  simpa using toggleSquare

/-- A singular three-dimensional linear map has image dimension at most two. -/
theorem range_finrank_le_two_of_det_zero (matrix : ControlMatrix)
    (detZero : matrix.det = 0) :
    Module.finrank ℚ (LinearMap.range (Matrix.toLin' matrix)) ≤ 2 := by
  have matrixNotUnit : ¬IsUnit matrix := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact not_not.mpr detZero
  have matrixNotInjective : ¬Function.Injective (Matrix.toLin' matrix) := by
    intro injective
    exact matrixNotUnit (Matrix.mulVec_injective_iff_isUnit.mp injective)
  have kernelNontrivial : LinearMap.ker (Matrix.toLin' matrix) ≠ ⊥ := by
    intro kernelBot
    exact matrixNotInjective (LinearMap.ker_eq_bot.mp kernelBot)
  have kernelPositive : 1 ≤ Module.finrank ℚ (LinearMap.ker (Matrix.toLin' matrix)) :=
    Submodule.one_le_finrank_iff.mpr kernelNontrivial
  have rankNullity := (Matrix.toLin' matrix).finrank_range_add_finrank_ker
  have ambientDimension : Module.finrank ℚ (Fin 3 → ℚ) = 3 := by
    simp
  rw [ambientDimension] at rankNullity
  omega

/-- The two boundary carriers have vector dimension at most one. They are rays only when their
spanning vectors are nonzero. -/
theorem boundary_carrier_finrank_le_one
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (toggled : Bool) :
    Module.finrank ℚ (carrier data toggle column (.boundary toggled)) ≤ 1 := by
  cases toggled <;>
    exact (finrank_span_le_card _).trans (by simp)

/-- Boundary charts have dimension at most one; a rank-at-most-two data image and its toggled
image have dimension at most two. -/
theorem carrier_finrank_le_two
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column : State)
    (dataRank : ∀ letter,
      Module.finrank ℚ (LinearMap.range (Matrix.toLin' (data letter))) ≤ 2)
    (chart : Chart) :
    Module.finrank ℚ (carrier data toggle column chart) ≤ 2 := by
  cases chart with
  | boundary toggled =>
      exact (boundary_carrier_finrank_le_one data toggle column toggled).trans (by omega)
  | data toggled letter =>
      cases toggled with
      | false => exact dataRank letter
      | true =>
          exact (Submodule.finrank_map_le (Matrix.toLin' toggle)
            (LinearMap.range (Matrix.toLin' (data letter)))).trans (dataRank letter)

/-- States in one chart at which the terminal row vanishes. -/
def zeroSection (row : State) (chartCarrier : Submodule ℚ State) : Submodule ℚ State :=
  chartCarrier ⊓ LinearMap.ker (rowOutput row)

theorem mem_zeroSection_iff {row state : State} {chartCarrier : Submodule ℚ State}
    (stateInCarrier : state ∈ chartCarrier) :
    state ∈ zeroSection row chartCarrier ↔ row ⬝ᵥ state = 0 := by
  simp [zeroSection, stateInCarrier, rowOutput]

/-- A row cuts a subspace of dimension at most two in either the whole subspace or a subspace of
dimension at most one. Projectively, every nontrivial data-chart target is at most one point. -/
theorem zeroSection_eq_carrier_or_finrank_le_one
    (row : State) (chartCarrier : Submodule ℚ State)
    (carrierRank : Module.finrank ℚ chartCarrier ≤ 2) :
    zeroSection row chartCarrier = chartCarrier ∨
      Module.finrank ℚ (zeroSection row chartCarrier) ≤ 1 := by
  by_cases contained : chartCarrier ≤ LinearMap.ker (rowOutput row)
  · left
    exact inf_eq_left.mpr contained
  · right
    have sectionProper : zeroSection row chartCarrier < chartCarrier := by
      apply lt_of_le_of_ne inf_le_left
      intro sectionEquality
      apply contained
      intro state stateInCarrier
      have stateInSection : state ∈ zeroSection row chartCarrier := by
        change state ∈ chartCarrier ⊓ LinearMap.ker (rowOutput row)
        rw [sectionEquality]
        exact stateInCarrier
      exact stateInSection.2
    have rankStrict := Submodule.finrank_lt_finrank_of_lt sectionProper
    omega

/-- Every chart in a rank-at-most-two transverse action has a whole-chart or projective-point
terminal section. -/
theorem chart_zeroSection_classification
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (column row : State)
    (dataRank : ∀ letter,
      Module.finrank ℚ (LinearMap.range (Matrix.toLin' (data letter))) ≤ 2)
    (chart : Chart) :
    zeroSection row (carrier data toggle column chart) = carrier data toggle column chart ∨
      Module.finrank ℚ (zeroSection row (carrier data toggle column chart)) ≤ 1 :=
  zeroSection_eq_carrier_or_finrank_le_one row (carrier data toggle column chart)
    (carrier_finrank_le_two data toggle column dataRank chart)

/-- An exact paired recognizer with a projectively involutive toggle has its complete raw-control
zero language on six fixed carrier sections. The statement is uniform in `β` and `body`; no
admissibility or intended-history restriction is needed. -/
theorem pairedZero_iff_mem_six_zeroSections
    (β : Nat) (body : List TagLetter)
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (row column : State)
    (toggleScalar : ℚ) (toggleScalar_ne : toggleScalar ≠ 0)
    (toggleSquare : toggle * toggle = toggleScalar • 1)
    (sameZero : RepresentsZeroSet (pairedCoefficient ℚ β body)
      (generator data toggle) row column)
    (word : List PairedControl) :
    pairedCoefficient ℚ β body word = 0 ↔
      ∃ chart,
        wordProduct (generator data toggle) word *ᵥ column ∈
          zeroSection row (carrier data toggle column chart) := by
  let state := wordProduct (generator data toggle) word *ᵥ column
  obtain ⟨chart, stateInCarrier⟩ :=
    reachable_mem_carrier data toggle column toggleScalar toggleScalar_ne toggleSquare word
  constructor
  · intro sourceZero
    refine ⟨chart, (mem_zeroSection_iff stateInCarrier).mpr ?_⟩
    have targetZero := (sameZero word).mpr sourceZero
    simpa [linearCoefficient, state] using targetZero
  · rintro ⟨zeroChart, stateInSection⟩
    have targetZero : linearCoefficient (generator data toggle) row column word = 0 := by
      simpa [linearCoefficient, state, rowOutput] using stateInSection.2
    exact (sameZero word).mp targetZero

/-- Canonical-chart form of the same exact zero-language reduction. Whole-chart acceptance is
controlled by the finite label `wordChart`; every remaining target inside that chart has vector
dimension at most one under the singular-data hypotheses below. -/
theorem pairedZero_iff_mem_wordChart_zeroSection
    (β : Nat) (body : List TagLetter)
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (row column : State)
    (toggleScalar : ℚ) (_toggleScalar_ne : toggleScalar ≠ 0)
    (toggleSquare : toggle * toggle = toggleScalar • 1)
    (sameZero : RepresentsZeroSet (pairedCoefficient ℚ β body)
      (generator data toggle) row column)
    (word : List PairedControl) :
    pairedCoefficient ℚ β body word = 0 ↔
      wordProduct (generator data toggle) word *ᵥ column ∈
        zeroSection row (carrier data toggle column (wordChart word)) := by
  have stateInCarrier :=
    wordProduct_mulVec_mem_wordChart data toggle column toggleScalar toggleSquare word
  rw [mem_zeroSection_iff stateInCarrier]
  constructor
  · intro sourceZero
    have targetZero := (sameZero word).mpr sourceZero
    simpa [linearCoefficient] using targetZero
  · intro targetZero
    apply (sameZero word).mp
    simpa [linearCoefficient] using targetZero

/-- Master obstruction for the singular/projectively-involutive transverse architecture. Every
data image has vector dimension at most two, every terminal section is a whole chart or has
vector dimension at most one, and those six sections recognize the paired zeros on the complete
free control monoid. -/
theorem pairedZero_singular_sixLineAtlas
    (β : Nat) (body : List TagLetter)
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (row column : State)
    (dataSingular : ∀ letter, (data letter).det = 0)
    (toggleScalar : ℚ) (toggleScalar_ne : toggleScalar ≠ 0)
    (toggleSquare : toggle * toggle = toggleScalar • 1)
    (sameZero : RepresentsZeroSet (pairedCoefficient ℚ β body)
      (generator data toggle) row column) :
    (∀ chart,
      zeroSection row (carrier data toggle column chart) = carrier data toggle column chart ∨
        Module.finrank ℚ (zeroSection row (carrier data toggle column chart)) ≤ 1) ∧
      ∀ word,
        pairedCoefficient ℚ β body word = 0 ↔
          wordProduct (generator data toggle) word *ᵥ column ∈
            zeroSection row (carrier data toggle column (wordChart word)) := by
  have dataRank : ∀ letter,
      Module.finrank ℚ (LinearMap.range (Matrix.toLin' (data letter))) ≤ 2 := by
    intro letter
    exact range_finrank_le_two_of_det_zero (data letter) (dataSingular letter)
  exact ⟨chart_zeroSection_classification data toggle column row dataRank,
    pairedZero_iff_mem_wordChart_zeroSection β body data toggle row column
      toggleScalar toggleScalar_ne toggleSquare sameZero⟩

/-- Matrix-level involution is the scalar-one instance of the master obstruction. -/
theorem pairedZero_singular_sixLineAtlas_of_involutive
    (β : Nat) (body : List TagLetter)
    (data : TagLetter → ControlMatrix) (toggle : ControlMatrix) (row column : State)
    (dataSingular : ∀ letter, (data letter).det = 0)
    (toggleSquare : toggle * toggle = 1)
    (sameZero : RepresentsZeroSet (pairedCoefficient ℚ β body)
      (generator data toggle) row column) :
    (∀ chart,
      zeroSection row (carrier data toggle column chart) = carrier data toggle column chart ∨
        Module.finrank ℚ (zeroSection row (carrier data toggle column chart)) ≤ 1) ∧
      ∀ word,
        pairedCoefficient ℚ β body word = 0 ↔
          wordProduct (generator data toggle) word *ᵥ column ∈
            zeroSection row (carrier data toggle column (wordChart word)) := by
  apply pairedZero_singular_sixLineAtlas β body data toggle row column dataSingular 1
    (by norm_num)
  simpa using toggleSquare
  exact sameZero

end TransverseLineAtlas
end MatrixMortality

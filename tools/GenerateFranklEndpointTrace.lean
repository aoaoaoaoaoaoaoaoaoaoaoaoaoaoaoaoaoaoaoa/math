import Frankl.EndpointCertificate

namespace Frankl.TraceGenerator

private structure NamedChunk where
  name : String
  rectangle : RatRectangle
  tree : Subdivision
  leaves : ℕ

private inductive Partition where
  | certified (rectangle : RatRectangle) (tree : Subdivision)
  | horizontal (cut : ℚ) (lower upper : Partition)
  | vertical (cut : ℚ) (lower upper : Partition)

private def leafCount : Subdivision → ℕ
  | .leaf _ => 1
  | .horizontal _ lower upper => leafCount lower + leafCount upper
  | .vertical _ lower upper => leafCount lower + leafCount upper

private def partitionSubdivision (limit : ℕ) (rectangle : RatRectangle) :
    Subdivision → Partition
  | tree@(.leaf _) => .certified rectangle tree
  | tree@(.horizontal cut lower upper) =>
      if leafCount tree ≤ limit then
        .certified rectangle tree
      else
        .horizontal cut
          (partitionSubdivision limit (rectangle.lowerHorizontal cut) lower)
          (partitionSubdivision limit (rectangle.upperHorizontal cut) upper)
  | tree@(.vertical cut lower upper) =>
      if leafCount tree ≤ limit then
        .certified rectangle tree
      else
        .vertical cut
          (partitionSubdivision limit (rectangle.lowerVertical cut) lower)
          (partitionSubdivision limit (rectangle.upperVertical cut) upper)

private def namedChunks (stem : String) : Partition → List NamedChunk
  | .certified rectangle tree => [⟨stem, rectangle, tree, leafCount tree⟩]
  | .horizontal _ lower upper =>
      namedChunks (stem ++ "L") lower ++ namedChunks (stem ++ "U") upper
  | .vertical _ lower upper =>
      namedChunks (stem ++ "L") lower ++ namedChunks (stem ++ "U") upper

private structure NamedCover where
  name : String
  stem : String
  rectangle : RatRectangle
  partition : Partition

private def partitionChunkCount : Partition → ℕ
  | .certified _ _ => 1
  | .horizontal _ lower upper => partitionChunkCount lower + partitionChunkCount upper
  | .vertical _ lower upper => partitionChunkCount lower + partitionChunkCount upper

private def coverageShards (limit : ℕ) (stem : String) (rectangle : RatRectangle) :
    Partition → List NamedCover
  | partition@(.certified _ _) =>
      [⟨stem ++ "Cover", stem, rectangle, partition⟩]
  | partition@(.horizontal cut lower upper) =>
      if partitionChunkCount partition ≤ limit then
        [⟨stem ++ "Cover", stem, rectangle, partition⟩]
      else
        coverageShards limit (stem ++ "L") (rectangle.lowerHorizontal cut) lower ++
          coverageShards limit (stem ++ "U") (rectangle.upperHorizontal cut) upper
  | partition@(.vertical cut lower upper) =>
      if partitionChunkCount partition ≤ limit then
        [⟨stem ++ "Cover", stem, rectangle, partition⟩]
      else
        coverageShards limit (stem ++ "L") (rectangle.lowerVertical cut) lower ++
          coverageShards limit (stem ++ "U") (rectangle.upperVertical cut) upper

private def packChunks (budget : ℕ) :
    List NamedChunk → List NamedChunk → ℕ → List (List NamedChunk)
  | [], [], _ => []
  | [], current, _ => [current.reverse]
  | chunk :: remaining, [], _ => packChunks budget remaining [chunk] chunk.leaves
  | chunk :: remaining, current, weight =>
      if weight + chunk.leaves ≤ budget then
        packChunks budget remaining (chunk :: current) (weight + chunk.leaves)
      else
        current.reverse :: packChunks budget remaining [chunk] chunk.leaves

private def rationalSource (value : ℚ) : String :=
  "((" ++ toString value.num ++ " : ℚ) / " ++ toString value.den ++ ")"

private def realSource (value : ℚ) : String :=
  "((" ++ toString value.num ++ " : ℝ) / " ++ toString value.den ++ ")"

private def subdivisionSource : Subdivision → String
  | .leaf .interval => ".leaf .interval"
  | .leaf .zeroCorner => ".leaf .zeroCorner"
  | .leaf .oneCorner => ".leaf .oneCorner"
  | .horizontal cut lower upper =>
      ".horizontal " ++ rationalSource cut ++ "\n  (" ++ subdivisionSource lower ++
        ")\n  (" ++ subdivisionSource upper ++ ")"
  | .vertical cut lower upper =>
      ".vertical " ++ rationalSource cut ++ "\n  (" ++ subdivisionSource lower ++
        ")\n  (" ++ subdivisionSource upper ++ ")"

private def rectangle (horizontalLower horizontalUpper verticalLower verticalUpper : ℚ) :
    RatRectangle :=
  ⟨RatBall.ofBounds horizontalLower horizontalUpper,
    RatBall.ofBounds verticalLower verticalUpper⟩

private def chunkSource (chunk : NamedChunk) : String :=
  let horizontalLower := chunk.rectangle.horizontal.lower
  let horizontalUpper := chunk.rectangle.horizontal.upper
  let verticalLower := chunk.rectangle.vertical.lower
  let verticalUpper := chunk.rectangle.vertical.upper
  let rectangleName := chunk.name ++ "Rectangle"
  let treeName := chunk.name ++ "Tree"
  "private def " ++ rectangleName ++ " : RatRectangle :=\n" ++
    "  ⟨RatBall.ofBounds " ++ rationalSource horizontalLower ++ " " ++
      rationalSource horizontalUpper ++ ",\n" ++
    "    RatBall.ofBounds " ++ rationalSource verticalLower ++ " " ++
      rationalSource verticalUpper ++ "⟩\n\n" ++
    "private def " ++ treeName ++ " : Subdivision :=\n" ++
    subdivisionSource chunk.tree ++ "\n\n" ++
    "private theorem " ++ treeName ++ "_certified :\n" ++
    "    certifySubdivision 12 64 32 " ++ rectangleName ++ "\n" ++
      "      CertificateObjective.endpointExpression " ++ treeName ++ " =\n" ++
      "        some () := by\n" ++
    "  rfl\n\n" ++
    "/-- One static reflected endpoint-certificate chunk. -/\n" ++
    "theorem " ++ chunk.name ++ "_nonneg {a q : ℝ}\n" ++
    "    (haLower : " ++ realSource horizontalLower ++ " ≤ a)\n" ++
    "    (haUpper : a ≤ " ++ realSource horizontalUpper ++ ")\n" ++
    "    (hqLower : " ++ realSource verticalLower ++ " ≤ q)\n" ++
    "    (hqUpper : q ≤ " ++ realSource verticalUpper ++ ") :\n" ++
    "    0 ≤ endpointCertificateObjective a q := by\n" ++
    "  apply endpointCertificateObjective_nonneg_of_subdivision\n" ++
    "      (rectangle := " ++ rectangleName ++ ") (tree := " ++ treeName ++ ")\n" ++
    "  · norm_num [" ++ rectangleName ++ ", RatBall.ofBounds, RatBall.lower]\n" ++
    "  · norm_num [" ++ rectangleName ++ ", RatBall.ofBounds]\n" ++
    "  · norm_num [" ++ rectangleName ++ ", RatBall.ofBounds, RatBall.lower]\n" ++
    "  · norm_num [" ++ rectangleName ++
      ", RatBall.ofBounds, RatBall.upper, abundanceTarget]\n" ++
    "  · norm_num [" ++ rectangleName ++ ", RatBall.ofBounds, RatBall.lower]\n" ++
    "  · norm_num [" ++ rectangleName ++ ", RatBall.ofBounds, RatBall.upper]\n" ++
    "  · rw [" ++ rectangleName ++ "]\n" ++
    "    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith\n" ++
    "  · rw [" ++ rectangleName ++ "]\n" ++
    "    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith\n" ++
    "  · exact " ++ treeName ++ "_certified\n\n"

private def importsSource (modules : List String) : String :=
  String.join (modules.map fun moduleName => "import " ++ moduleName ++ "\n")

private def moduleSource (imports : List String) (body : String) : String :=
  importsSource imports ++ "\nnamespace Frankl\n\n" ++ body ++ "end Frankl\n"

private def validateChunk (chunk : NamedChunk) : IO Unit := do
  let result := certifySubdivision 12 64 32 chunk.rectangle
    CertificateObjective.endpointExpression chunk.tree
  unless result = some () do
    throw <| IO.userError ("uncertified generated chunk: " ++ chunk.name)

private def writeTraceBatches (outputDirectory moduleStem : String)
    (chunks : List NamedChunk) : IO (List String) := do
  let batches := packChunks 28 chunks [] 0
  let mut modules := []
  for (index, batch) in batches.enum do
    for chunk in batch do
      validateChunk chunk
    let shortName := moduleStem ++ "Trace" ++ toString index
    let moduleName := "Frankl.EndpointTrace." ++ shortName
    let body := String.join (batch.map chunkSource)
    IO.FS.writeFile (outputDirectory ++ "/" ++ shortName ++ ".lean")
      (moduleSource ["Frankl.EndpointCertificate"] body)
    modules := modules ++ [moduleName]
  pure modules

private def partitionCoverageSource (indent lead stem : String) : Partition → String
  | .certified _ _ =>
      indent ++ lead ++ "exact " ++ stem ++ "_nonneg\n" ++
        indent ++ "    (by linarith) (by linarith) (by linarith) (by linarith)\n"
  | .horizontal cut lower upper =>
      let hypothesis := "h" ++ stem
      let childIndent := if lead = "" then indent else indent ++ "  "
      indent ++ lead ++ "by_cases " ++ hypothesis ++ " : a ≤ " ++ realSource cut ++ "\n" ++
        partitionCoverageSource childIndent "· " (stem ++ "L") lower ++
        partitionCoverageSource childIndent "· " (stem ++ "U") upper
  | .vertical cut lower upper =>
      let hypothesis := "h" ++ stem
      let childIndent := if lead = "" then indent else indent ++ "  "
      indent ++ lead ++ "by_cases " ++ hypothesis ++ " : q ≤ " ++ realSource cut ++ "\n" ++
        partitionCoverageSource childIndent "· " (stem ++ "L") lower ++
        partitionCoverageSource childIndent "· " (stem ++ "U") upper

private def shardedCoverageSource (limit : ℕ) (indent lead stem : String) :
    Partition → String
  | .certified _ _ =>
      indent ++ lead ++ "exact " ++ stem ++ "Cover\n" ++
        indent ++ "    (by linarith) (by linarith) (by linarith) (by linarith)\n"
  | partition@(.horizontal cut lower upper) =>
      if partitionChunkCount partition ≤ limit then
        indent ++ lead ++ "exact " ++ stem ++ "Cover\n" ++
          indent ++ "    (by linarith) (by linarith) (by linarith) (by linarith)\n"
      else
        let hypothesis := "h" ++ stem
        let childIndent := if lead = "" then indent else indent ++ "  "
        indent ++ lead ++ "by_cases " ++ hypothesis ++ " : a ≤ " ++ realSource cut ++ "\n" ++
          shardedCoverageSource limit childIndent "· " (stem ++ "L") lower ++
          shardedCoverageSource limit childIndent "· " (stem ++ "U") upper
  | partition@(.vertical cut lower upper) =>
      if partitionChunkCount partition ≤ limit then
        indent ++ lead ++ "exact " ++ stem ++ "Cover\n" ++
          indent ++ "    (by linarith) (by linarith) (by linarith) (by linarith)\n"
      else
        let hypothesis := "h" ++ stem
        let childIndent := if lead = "" then indent else indent ++ "  "
        indent ++ lead ++ "by_cases " ++ hypothesis ++ " : q ≤ " ++ realSource cut ++ "\n" ++
          shardedCoverageSource limit childIndent "· " (stem ++ "L") lower ++
          shardedCoverageSource limit childIndent "· " (stem ++ "U") upper
private def coverageTheoremSource (visibility theoremName stem : String)
    (rectangle : RatRectangle) (partition : Partition) : String :=
  visibility ++ "theorem " ++ theoremName ++ " {a q : ℝ}\n" ++
    "    (haLower : " ++ realSource rectangle.horizontal.lower ++ " ≤ a)\n" ++
    "    (haUpper : a ≤ " ++ realSource rectangle.horizontal.upper ++ ")\n" ++
    "    (hqLower : " ++ realSource rectangle.vertical.lower ++ " ≤ q)\n" ++
    "    (hqUpper : q ≤ " ++ realSource rectangle.vertical.upper ++ ") :\n" ++
    "    0 ≤ endpointCertificateObjective a q := by\n" ++
    partitionCoverageSource "  " "" stem partition ++ "\n"

private def linearCoverageSource (indent coordinate hypothesisStem : String)
    (theorems : List (String × RatRectangle)) : String :=
  match theorems with
  | [] => indent ++ "contradiction\n"
  | [(theoremName, _)] =>
      indent ++ "exact " ++ theoremName ++ "\n" ++
        indent ++ "  (by linarith) (by linarith) (by linarith) (by linarith)\n"
  | (theoremName, rectangle) :: remaining =>
      let cut := if coordinate = "a" then rectangle.horizontal.upper else rectangle.vertical.upper
      let hypothesis := hypothesisStem ++ toString remaining.length
      indent ++ "by_cases " ++ hypothesis ++ " : " ++ coordinate ++ " ≤ " ++
        realSource cut ++ "\n" ++
        indent ++ "· exact " ++ theoremName ++ "\n" ++
        indent ++ "    (by linarith) (by linarith) (by linarith) (by linarith)\n" ++
        linearCoverageSource indent coordinate hypothesisStem remaining

private def rangeTheoremSource (documentation theoremName coordinate : String)
    (rectangle : RatRectangle) (theorems : List (String × RatRectangle)) : String :=
  "/-- " ++ documentation ++ " -/\n" ++
    "theorem " ++ theoremName ++ " {a q : ℝ}\n" ++
    "    (haLower : " ++ realSource rectangle.horizontal.lower ++ " ≤ a)\n" ++
    "    (haUpper : a ≤ " ++ realSource rectangle.horizontal.upper ++ ")\n" ++
    "    (hqLower : " ++ realSource rectangle.vertical.lower ++ " ≤ q)\n" ++
    "    (hqUpper : q ≤ " ++ realSource rectangle.vertical.upper ++ ") :\n" ++
    "    0 ≤ endpointCertificateObjective a q := by\n" ++
    linearCoverageSource "  " coordinate ("h" ++ theoremName) theorems ++ "\n"

private def adjacentBounds (bounds : List ℚ) : List (ℚ × ℚ) :=
  List.zip bounds bounds.tail

private def qOneLower : ℚ := 1 / 1000

private def qOneUpper : ℚ := 19099 / 50000

private def qOneBoundary (index : ℕ) : ℚ :=
  qOneLower + index * ((qOneUpper - qOneLower) / 128)

private def qOneBounds : List ℚ :=
  (List.range 129).map qOneBoundary

private def lowHorizontalBounds : List ℚ :=
  0 :: 1 / 1000 :: (List.range 16).map fun index => (index + 1 : ℚ) / 64

private def lowVerticalBounds : List ℚ :=
  0 :: 1 / 1000 :: (List.range 16).map fun index => (index + 1 : ℚ) / 32

private def qOneCell (index : ℕ) (bounds : ℚ × ℚ) :
    String × RatRectangle × Partition :=
  let cellRectangle := rectangle bounds.1 bounds.2 1 1
  let tree := adaptiveSubdivision 12 64 32 false cellRectangle
    CertificateObjective.endpointExpression 24
  let stem := "qOneCell" ++ toString index ++ "Root"
  (stem, cellRectangle, partitionSubdivision 12 cellRectangle tree)

private def lowCell (row column : ℕ) (horizontal vertical : ℚ × ℚ) :
    String × RatRectangle × Partition :=
  let cellRectangle := rectangle horizontal.1 horizontal.2 vertical.1 vertical.2
  let tree := adaptiveSubdivision 12 64 32 true cellRectangle
    CertificateObjective.endpointExpression 24
  let stem := "lowRow" ++ toString row ++ "Cell" ++ toString column ++ "Root"
  (stem, cellRectangle, partitionSubdivision 12 cellRectangle tree)

private def writeQOne (outputDirectory : String) : IO Unit := do
  let cells := (adjacentBounds qOneBounds).enum.map fun (index, bounds) =>
    qOneCell index bounds
  let rangeLists := (List.range 8).map fun index => (cells.drop (index * 16)).take 16
  let mut rangeModules := []
  let mut rangeTheorems := []
  for (rangeIndex, rangeCells) in rangeLists.enum do
    let chunks := (rangeCells.map fun (stem, _, partition) =>
      namedChunks stem partition).join
    let traceModules ← writeTraceBatches outputDirectory
      ("QOneRange" ++ toString rangeIndex) chunks
    let cellSources := String.join <| rangeCells.map fun (stem, cellRectangle, partition) =>
      coverageTheoremSource "private " (stem ++ "Cover") stem cellRectangle partition
    let cellTheorems := rangeCells.map fun (stem, cellRectangle, _) =>
      (stem ++ "Cover", cellRectangle)
    let firstRectangle := (rangeCells.head?).map (fun cell => cell.2.1)
    let lastRectangle := (rangeCells.getLast?).map (fun cell => cell.2.1)
    let some firstRectangle := firstRectangle
      | throw <| IO.userError "empty q=1 range"
    let some lastRectangle := lastRectangle
      | throw <| IO.userError "empty q=1 range"
    let rangeRectangle := rectangle firstRectangle.horizontal.lower
      lastRectangle.horizontal.upper 1 1
    let theoremName := "endpointCertificateObjective_qOneRange" ++
      toString rangeIndex ++ "_nonneg"
    let rangeSource := rangeTheoremSource "One certified range of the deterministic endpoint."
      theoremName "a" rangeRectangle cellTheorems
    let shortName := "QOneRange" ++ toString rangeIndex
    IO.FS.writeFile (outputDirectory ++ "/" ++ shortName ++ ".lean")
      (moduleSource traceModules (cellSources ++ rangeSource))
    rangeModules := rangeModules ++ ["Frankl.EndpointTrace." ++ shortName]
    rangeTheorems := rangeTheorems ++ [(theoremName, rangeRectangle)]
  let allRectangle := rectangle qOneLower qOneUpper 1 1
  let theoremSource := rangeTheoremSource
    "The deterministic endpoint is certified from the analytic corner to the target."
    "endpointCertificateObjective_qOne_nonneg" "a" allRectangle rangeTheorems
  IO.FS.writeFile (outputDirectory ++ "/QOne.lean")
    (moduleSource rangeModules theoremSource)

private def writeLow (outputDirectory : String) : IO Unit := do
  let horizontalCells := adjacentBounds lowHorizontalBounds
  let verticalCells := adjacentBounds lowVerticalBounds
  let mut rowModules := []
  let mut rowTheorems := []
  for (row, horizontal) in horizontalCells.enum do
    let cells := verticalCells.enum.map fun (column, vertical) =>
      lowCell row column horizontal vertical
    let chunks := (cells.map fun (stem, _, partition) => namedChunks stem partition).join
    let traceModules ← writeTraceBatches outputDirectory
      ("LowRow" ++ toString row) chunks
    let cellSources := String.join <| cells.map fun (stem, cellRectangle, partition) =>
      coverageTheoremSource "private " (stem ++ "Cover") stem cellRectangle partition
    let cellTheorems := cells.map fun (stem, cellRectangle, _) =>
      (stem ++ "Cover", cellRectangle)
    let rowRectangle := rectangle horizontal.1 horizontal.2 0 (1 / 2)
    let theoremName := "endpointCertificateObjective_lowRow" ++ toString row ++ "_nonneg"
    let rowSource := rangeTheoremSource "One horizontal row of the low endpoint rectangle."
      theoremName "q" rowRectangle cellTheorems
    let shortName := "LowRow" ++ toString row
    IO.FS.writeFile (outputDirectory ++ "/" ++ shortName ++ ".lean")
      (moduleSource traceModules (cellSources ++ rowSource))
    rowModules := rowModules ++ ["Frankl.EndpointTrace." ++ shortName]
    rowTheorems := rowTheorems ++ [(theoremName, rowRectangle)]
  let allRectangle := rectangle 0 (1 / 4) 0 (1 / 2)
  let theoremSource := rangeTheoremSource
    "The complete low endpoint rectangle has nonnegative certificate objective."
    "endpointCertificateObjective_low_nonneg" "a" allRectangle rowTheorems
  IO.FS.writeFile (outputDirectory ++ "/Low.lean")
    (moduleSource rowModules theoremSource)

private def writeResidual (outputDirectory : String) : IO Unit := do
  let residualRectangle := rectangle (1 / 4) (13 / 40) 0 (31 / 100)
  let tree := adaptiveSubdivision 12 64 32 false residualRectangle
    CertificateObjective.endpointExpression 24
  let stem := "residualRoot"
  let partition := partitionSubdivision 12 residualRectangle tree
  let chunks := namedChunks stem partition
  let traceModules ← writeTraceBatches outputDirectory "Residual" chunks
  let covers := coverageShards 8 stem residualRectangle partition
  let coverSource := String.join <| covers.map fun cover =>
    coverageTheoremSource "private " cover.name cover.stem cover.rectangle cover.partition
  let theoremSource := coverSource ++
    "/-- The exact residual rectangle below the analytic conditional-mean core. -/\n" ++
    "theorem endpointCertificateObjective_residual_nonneg {a q : ℝ}\n" ++
    "    (haLower : ((1 : ℝ) / 4) ≤ a) (haUpper : a ≤ ((13 : ℝ) / 40))\n" ++
    "    (hqLower : ((0 : ℝ) / 1) ≤ q) (hqUpper : q ≤ ((31 : ℝ) / 100)) :\n" ++
    "    0 ≤ endpointCertificateObjective a q := by\n" ++
    shardedCoverageSource 8 "  " "" stem partition ++ "\n"
  IO.FS.writeFile (outputDirectory ++ "/Residual.lean")
    (moduleSource traceModules theoremSource)

def generate (outputRoot : String) : IO Unit := do
  let outputDirectory := outputRoot ++ "/Frankl/EndpointTrace"
  IO.FS.createDirAll outputDirectory
  writeQOne outputDirectory
  writeLow outputDirectory
  writeResidual outputDirectory
  IO.FS.writeFile (outputRoot ++ "/Frankl/EndpointTrace.lean")
    (importsSource ["Frankl.EndpointTrace.Low", "Frankl.EndpointTrace.QOne",
      "Frankl.EndpointTrace.Residual"])

end Frankl.TraceGenerator

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [outputRoot] => Frankl.TraceGenerator.generate outputRoot
  | _ => throw <| IO.userError "usage: GenerateFranklEndpointTrace.lean OUTPUT_ROOT"

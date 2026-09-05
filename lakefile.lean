import Lake

open Lake DSL System Lean

package matrix_mortality where
  version := v!"0.1.0"
  enableArtifactCache := true
  restoreAllArtifacts := true
  leanOptions := #[
    ⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩,
    ⟨`linter.docPrime, true⟩, ⟨`linter.hashCommand, true⟩, ⟨`linter.oldObtain, true⟩,
    ⟨`linter.style.refine, true⟩, ⟨`linter.style.cdot, true⟩,
    ⟨`linter.style.dollarSyntax, true⟩, ⟨`linter.style.lambdaSyntax, true⟩,
    ⟨`linter.style.longFile, 1500⟩, ⟨`linter.style.longLine, true⟩,
    ⟨`linter.style.missingEnd, true⟩, ⟨`linter.style.setOption, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib MatrixMortality where
  globs := #[.andSubmodules `MatrixMortality]

@[default_target]
lean_lib Frankl where
  globs := #[.andSubmodules `Frankl]

lean_lib Verification where
  globs := #[.submodules `Verification]

namespace Gate

/-- Resolve modules through Lake; the gate does not maintain a second import graph. -/
def module (name : Name) : FetchM Lake.Module := do
  let some mod := (← getWorkspace).findModule? name
    | error s!"unknown verification root: {name}"
  return mod

/-- A proof gate consumes the entire imported source closure, the corresponding compiled
artifacts, the audit implementation, and the reviewed transitive-axioms snapshot. -/
def proof (pkg : Package) (label : String) (roots : Array Name)
    (complete := false) : FetchM (Job FilePath) := withCurrPackage pkg do
  let modules ← if complete then
    Array.flatten <$> pkg.leanLibs.mapM (·.getModuleArray)
  else
    roots.mapM module
  let modules := modules.qsort (fun a b => a.name.lt b.name)
  let roots := modules.map (·.name)
  let audit ← module `Verification.Audit
  let imports ← Job.collectArray <$> modules.mapM (·.transImports.fetch)
  -- Resolve the graph in FetchM. Concurrent fetches from JobM can race Lake's build store
  -- and refetch pending dependencies inside synchronous export-info continuations.
  let imported ← imports.await
  let mut closure := #[]
  let mut seen : NameSet := {}
  for mod in imported.flatten ++ modules.push audit do
    if mod.pkg.keyName == pkg.keyName && !seen.contains mod.name then
      seen := seen.insert mod.name
      closure := closure.push mod
  let sources := (closure.map (·.leanFile)).toList.mergeSort (fun a b =>
    a.toString ≤ b.toString) |>.toArray
  let files := sources ++ #[pkg.dir / "lakefile.lean",
    pkg.dir / "verification/axioms.txt", pkg.dir / "scripts/check-proof-sources.sh"]
  let inputs := Job.mixArray (← files.mapM (inputTextFile ·))
  let artifacts := Job.mixArray (← (modules.push audit).mapM (·.leanArts.fetch))
  (inputs.mix artifacts).mapM fun _ => do
    addLeanTrace
    addPureTrace (label, roots, complete) "verification contract"
    addPureTrace (closure.map (·.name)) "audited module inventory"
    let out := pkg.buildDir / "verification" / s!"{label}.txt"
    let result ← buildArtifactUnlessUpToDate out (text := true) (restore := true) do
      createParentDirs out
      proc {cmd := "bash", args := #["scripts/check-proof-sources.sh"] ++
        sources.map (·.toString), cwd := some pkg.dir}
      let auditFile := pkg.buildDir / "verification" / s!"{label}.lean"
      let header := String.join ((roots.push `Verification.Audit).toList.map
        (fun root => s!"import {root}\n"))
      IO.FS.writeFile auditFile <| header ++
        s!"\nverify_axioms \"verification/axioms.txt\" {if complete then "complete" else "present"}\n" ++
        "verify_environment MatrixMortality Frankl Verification\n"
      let lean ← getLean
      let leanPath ← getLeanPath
      let options ← getLeanOptions
      let leanArgs := options.values.toArray.map fun (name, value) =>
        LeanOption.asCliArg ⟨name, value⟩
      let output ← captureProc' {
        cmd := lean.toString
        args := leanArgs.push auditFile.toString
        cwd := some pkg.dir
        env := #[("LEAN_PATH", some leanPath.toString)]
      }
      if complete && output.stdout != (← IO.FS.readFile (pkg.dir / "verification/axioms.txt")) then
        error "complete verification output differs from the reviewed snapshot"
      IO.FS.writeFile out output.stdout
    return result.path

/-- Enumerate declared input trees; root-level files exclude worktrees and build output. -/
def files (pkg : Package) (directories : Array String) (extensions : Array String) :
    FetchM (Array FilePath) := do
  let mut paths := #[]
  for directory in directories do
    let candidates ← if directory == "." then
      (← (pkg.dir).readDir).mapM (fun entry => pure entry.path)
    else
      (pkg.dir / directory).walkDir
    for path in candidates do
      if extensions.contains (path.extension.getD "") && !(← path.isDir) then
        paths := paths.push path
  return paths.qsort (fun a b => a.toString < b.toString)

/-- Cache a non-Lean validation action, including its input inventory and tool identities. -/
def action (pkg : Package) (label : String) (inputs : Array FilePath)
    (tools : Array (String × Array String)) : FetchM (Job FilePath) := withCurrPackage pkg do
  let command := pkg.dir / "scripts" / s!"check-{label}.sh"
  let paths := inputs ++ #[command, pkg.dir / "lakefile.lean", pkg.dir / ".python-version"]
  let inputs := Job.mixArray (← paths.mapM (inputBinFile ·))
  inputs.mapM fun _ => do
    addLeanTrace
    addPureTrace (label, paths.map (·.toString.dropPrefix pkg.dir.toString |>.toString))
      "validation input inventory"
    for (tool, args) in tools do
      let version ← captureProc' {cmd := tool, args, cwd := some pkg.dir}
      addPureTrace (version.stdout, version.stderr) tool
    if tools.any (·.1 == "uv") then
      let python ← captureProc {cmd := "uv", args := #["python", "find"], cwd := some pkg.dir}
      let version ← captureProc' {cmd := python, args := #["--version"]}
      addPureTrace (version.stdout, version.stderr) "Python"
    let out := pkg.buildDir / "verification" / s!"{label}.txt"
    let result ← buildArtifactUnlessUpToDate out (text := true) (restore := true) do
      createParentDirs out
      let output ← captureProc' {cmd := "bash", args := #[command.toString], cwd := some pkg.dir}
      IO.FS.writeFile out (output.stdout ++ output.stderr)
    return result.path

end Gate

target m92 pkg : FilePath :=
  Gate.proof pkg "m92" #[`Verification.M92]

target m35 pkg : FilePath :=
  Gate.proof pkg "m35" #[`Verification.M35]

target m44 pkg : FilePath :=
  Gate.proof pkg "m44" #[`Verification.M44]

target binary pkg : FilePath :=
  Gate.proof pkg "binary" #[`MatrixMortality.Undecidability.UniversalBinary]

target packing pkg : FilePath :=
  Gate.proof pkg "packing" #[`MatrixMortality.Undecidability.UniversalPacking]

target source pkg : FilePath :=
  Gate.proof pkg "source" #[`MatrixMortality.Undecidability.UniversalNearySource]

target foundations pkg : FilePath :=
  Gate.proof pkg "foundations" #[`MatrixMortality.MatrixSemigroup]

target mortality pkg : FilePath :=
  Gate.proof pkg "mortality" #[`MatrixMortality]

target frankl pkg : FilePath :=
  Gate.proof pkg "frankl" #[`Frankl]

target proofs pkg : FilePath :=
  Gate.proof pkg "proofs" #[`MatrixMortality, `Frankl, `Verification.Publication] (complete := true)

target publishedProofs pkg : FilePath :=
  Gate.proof pkg "published" #[`Verification.Publication]

target html pkg : FilePath := do
  let inputs ← Gate.files pkg #["."] #["html", "json", "png"]
  Gate.action pkg "html" (inputs ++ #[pkg.dir / "scripts/render_publication_graph.py",
    pkg.dir / "scripts/publish.sh"]) #[
    ("bash", #["--version"]), ("jq", #["--version"]),
    ("xmllint", #["--version"]), ("uv", #["--version"])]

target symbolic pkg : FilePath := do
  let checkers ← Gate.files pkg #["scripts", "tools"] #["py", "rs", "json"]
  let generated ← Gate.files pkg #["MatrixMortality"] #["lean"]
  let inputs := checkers ++ generated.filter (fun path =>
    (path.fileName.getD "").startsWith "ParabolicFirstB")
  Gate.action pkg "symbolic" inputs #[
    ("bash", #["--version"]), ("uv", #["--version"]),
    ("rustc", #["--version", "--verbose"]), ("rustfmt", #["--version"])]

target references pkg : FilePath := do
  Gate.action pkg "references" (← Gate.files pkg #["references"] #["md", "pdf"])
    #[("sha256sum", #["--version"])]

target paper pkg : FilePath := do
  Gate.action pkg "paper" (← Gate.files pkg #["paper"] #["tex", "bib", "pdf"])
    #[("tectonic", #["--version"])]

target ledger pkg : FilePath :=
  Gate.action pkg "ledger" #[pkg.dir / "SALVAGE.md"] #[("awk", #["--version"])]

target publication : Unit := do
  return Job.mixArray #[← publishedProofs.fetch, ← html.fetch, ← paper.fetch]

target all : Unit := do
  return Job.mixArray #[← proofs.fetch, ← html.fetch, ← symbolic.fetch,
    ← references.fetch, ← paper.fetch, ← ledger.fetch]

# Verification Targets

Lean and mathlib are pinned to `v4.33.1`. Lake owns compilation, dependency discovery,
parallel scheduling, and the content-addressed artifact cache. Named gates also cache
source-policy scans, environment lint, and transitive-axioms verification.

```sh
scripts/check.sh m82          # Only the M₈(2) proof closure and its verification
scripts/check.sh m35 m44      # Multiple targets share dependency jobs
scripts/check.sh publication  # Published proofs, HTML, and reproducible paper
scripts/check.sh all          # Full corpus, auxiliary certificates, references, HTML, paper
```

`m35`, `m44`, `m82`, and `m92` pin the types of their primitive-recursive reductions, many-one
reductions, and noncomputability endpoints. `source`, `binary`, `packing`, `foundations`,
`mortality`, and `frankl` select other proof closures. `proofs` checks the whole corpus.
`html`, `symbolic`, `references`, `paper`, and `ledger` select non-Lean stages.
The default remains `all`; publication explicitly selects `publication`.

For an individual module under development, use `lake build MatrixMortality.ModuleName`.
That compiles its imports but does not run a named verification gate. Compilation granularity
is a module, not a declaration. Import the individual universal endpoint modules when possible;
`UniversalNeary` is their aggregate, not the source theorem's owner.

## Cache Contract

`enableArtifactCache` and `restoreAllArtifacts` are enabled. The latter restores local
artifacts needed by editors and direct `lake env lean` invocations. Dependency checkouts and
builds remain in the manifest-keyed package pool owned by `share-lake-packages.sh`.
Each worktree retains its own mutable `.lake/build`.

The canonical gate defaults `LAKE_CACHE_DIR` to `$XDG_CACHE_HOME/lake`, or `~/.cache/lake`.
On the research workstation this is a symlink to `/data/main/lean-cache/artifacts`; the local
Lean/Lake launcher applies the same defaults to direct invocations in every worktree,
including branches predating this build configuration. An explicit `LAKE_CACHE_DIR` wins.
An explicitly empty value disables this artifact store.

Lake keys compiled modules by their compiler, options, source, and imported artifacts.
Proof-gate keys additionally include every first-party source in the imported closure,
the reviewed snapshot, the gate implementation, and the module inventory. Scanning source
bytes separately is necessary: a prohibited source construct must not disappear behind an
unchanged compiled result. Failed checks do not produce successful receipts.

Changing an unrelated Frankl file does not invalidate `m92`. Changing HTML does not invalidate
proof verification. Returning to previously checked source reuses its cached artifacts and
receipts, including in another worktree. The global reviewed snapshot is deliberately one
input shared by proof gates; editing it invalidates their verification receipts, not unrelated
Lean compilation.

Non-Lean actions declare their file inventories, scripts, and tool-version inputs. Python is
pinned by `.python-version`; individual certificate dependencies remain in their PEP 723
metadata. Symbolic certificates are auxiliary checks, not premises of Lean endpoint theorems,
and do not run during publication. They remain in the full gate.

## Inspect And Recover

```sh
lake --wfail --no-build build m92  # Fails if work is needed
lake --wfail -v build m92          # Show native trace and cache decisions
lake query m92                    # Print the verified receipt's path
lake --rehash build m92           # Rehash inputs instead of trusting saved file hashes
```

Receipts live in `.lake/build/verification/`. Proof receipts contain the exact transitive
axioms of reviewed declarations present in the target environment. The complete gate also
rejects missing reviewed declarations and discovers every library module through Lake's globs,
including files absent from the root aggregates.
`verification/axioms.txt` owns the reviewed declaration inventory and expected output;
`AxiomAudit.lean` remains a direct, uncached replay of that contract.

This is trusted-local build reuse, not independent verification or a signed public build
attestation. The native artifact cache is experimental. No cache upload service is configured
by this project, and its store must not be writable by untrusted users. After suspected cache
corruption, stop builds before clearing it with `lake cache clean`. This deletes only cached
artifacts, not source or the separate dependency package pool. There is no automatic eviction;
monitor `/data` and clear obsolete cache contents deliberately.

For independent first-party reproduction, use a fresh worktree and
`LAKE_CACHE_DIR= scripts/check.sh proofs`. Dependency artifacts remain a separate trust input;
a completely cold third-party reproduction requires an independent clone and dependency build.

## Extend

Add an endpoint probe under `Verification/` and a named `Gate.proof` target in `lakefile.lean`.
The imports determine its dependency closure. Add new published proof roots to
`Verification/Publication.lean`; research-only modules stay outside that aggregate.
Review changes to the canonical snapshot rather than regenerating it blindly.

Do not introduce an outer build system that treats the whole check script as one action.
Lake already supplies the relevant dependency graph and native shared cache; the shell files
are bounded validation commands, not a second scheduler.

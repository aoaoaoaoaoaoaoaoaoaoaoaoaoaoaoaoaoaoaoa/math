# Reproducibility

This repository is a fixed verification snapshot of the `GPCP(4)` and `M₃(5)` result. The
single command below checks source integrity, the local bibliography, Lean proofs and axioms,
the independent falsifier, the standalone HTML, and the manuscript PDF:

```sh
./scripts/check.sh
```

## Pinned Inputs

- Lean `4.12.0`, commit `dc2533473114`, selected by [lean-toolchain](lean-toolchain);
- mathlib commit `809c3fb3b5c8f5d7dace56e200b426187516535a`, with every transitive dependency
  pinned by [lake-manifest.json](lake-manifest.json);
- Ruff `0.15.22`, ty `0.0.58`, and html5validator `0.4.2`, selected explicitly by the check
  script;
- Tectonic `0.16.9` for the committed manuscript PDF, built with
  `SOURCE_DATE_EPOCH=1784606400` (`2026-07-21T04:00:00Z`).

The script expects `lake`, `uv`/`uvx`, `tectonic`, `xmllint`, `rg`, `diff`, and GNU `sha256sum` on
`PATH`. It defaults `ELAN_HOME` to `$HOME/.local/share/elan`; another installation may set the
variable explicitly. A first run may download the pinned Lake and uv dependencies.

## Integrity

[ARTIFACTS.sha256](ARTIFACTS.sha256) authenticates every publication, proof, executable,
document, and bibliography file in this snapshot. Every preserved paper also has a same-stem
Markdown synopsis whose `SHA-256` field is checked independently. The generated
[paper/main.pdf](paper/main.pdf) must compare byte-for-byte with a clean Tectonic build of
[paper/main.tex](paper/main.tex).

The frozen outputs of the decisive checks are in [verification](verification/README.md). They
are audit records, not substitutes for rerunning the commands.

## Formal Boundary

Lean checks the new instance-level equivalences from restricted tag-system semantics through
the exact five integer matrices. The axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`; there are no project axioms or admitted proofs.
The build treats all warnings as errors, disables automatic implicit variables, enables
mathlib's strict syntax profile, runs every default environment linter over the package, and
compares the transitive axiom report byte-for-byte with the reviewed snapshot.

The repository does not formalize Neary's Lemma 9/Table 2 universality compiler, its
computability, or the final many-one undecidability wrapper. The unconditional mathematical
result imports that peer-reviewed theorem in the ordinary mathematical sense. See
[FOUNDATIONS.md](FOUNDATIONS.md) for the logical and operational trust base.

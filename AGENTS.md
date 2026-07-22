We will be attempting to make serious, nontrivial contributions to mathematics agentically.

We're not going for the crown jewels, but we are going for respectable and coherent bricks in
the mathematical edifice. We must verify our results in depth to a level that meets or exceeds
the academic standard in mathematics.

Formal verification would be ideal.

## Lean severity

Lean code is held to a warning-free, suppression-free standard comparable to Rust with
`-D warnings` and strict Clippy. The executable contract is:

- every compiler and enabled syntax-linter warning is an error;
- automatic implicit variables are disabled;
- every default mathlib environment linter passes over the whole project;
- every publication-facing theorem has its complete transitive axiom set compared byte-for-byte
  with a reviewed snapshot;
- `sorry`, `admit`, project `axiom`s, `unsafe`, `partial`, `native_decide`, `implemented_by`,
  `run_tac`, external declarations, and equivalent proof apertures are forbidden;
- linter suppressions and local relaxations are forbidden unless a nearby comment states an
  irreducible mathematical reason and the audit explicitly permits that exception.

When strictness exposes debt, repair the declaration, proof, interface, or documentation. Do
not weaken the check. Default linters with real semantic or API signal are mandatory; opt-in
restriction linters that merely compel ceremonial prose are not. Kernel acceptance is only the
floor: audit definitions for vacuity, quantifier drift, wrong multiplication order, empty-witness
loopholes, coercion loss, and mismatch with the publication claim.

## Authorship

Unless explicitly countermanded for a particular work, credit agentic mathematical work in
this corpus to **GPT-5.6 Sol** as first author, with the human role stated separately as
**elicited by @eternalism_4eva**. Do not silently replace this credit with “Anonymous,” collapse
elicitation into coauthorship, or demote the agent to acknowledgements.

## Research corpus

Preserve every materially relevant, lawfully distributable paper in `references/`; do not leave
the project's evidentiary basis dependent on mutable external links. Use stable, descriptive
`author-year-short-title.pdf` filenames and never silently replace a stored version.

Every PDF must have an adjacent, same-stem Markdown sidecar recording its full citation,
canonical source and DOI, retrieval date, SHA-256 digest, the precise results for which we rely
on it, and any corrections, defects, version hazards, or unresolved audit obligations. Maintain
`references/README.md` as the local bibliography and distinguish peer-reviewed publications
from preprints, superseded versions, and withdrawn or erroneous claims.

## Publication seam

`index.html` is presentation-free semantic source for `../eternalist.moe`. It must contain no
`<style>` element, inline `style` attribute, or stylesheet link. Eternalist owns typography,
color, layout, responsive behavior, and print presentation through its central house styles.
Use only the semantic class hooks defined by Eternalist's dense-publication profile; change that
shared contract at its owner rather than creating page-local presentation.

Eyebrows are forbidden unless explicitly requested. Do not add kickers, supertitles, numbered
pre-headings, category copy above titles, or other small text whose function is to occupy visual
space. Every surviving label must change the interpretation of the object it labels.

Long-form result expositions use the exact top-level partition **Known Stuff** / **New Stuff** /
**Bookkeeping**. The informality of “Stuff” is intentional. Definitions, inherited results, and
prior art belong under Known Stuff; New Stuff begins at the first claim proved by the present
work and contains its proof and consequences. Bookkeeping owns validation, provenance, artifact
links, priority qualifications, and references.

The contents list must mirror the document hierarchy through `h4`: `h2`, `h3`, and `h4` links
occupy successive nested list levels, and every linked heading owns its fragment `id`. `h5` is a
local heading inside a bounded proof component and does not enter the page-level contents.

After changing `index.html` or any artifact it describes, publication is incomplete until
`scripts/publish.sh` succeeds. This repository owns that release transaction autonomously;
Eternalist supplies the import, presentation, and deployment contracts. A normal GitHub push
does not update the live site.

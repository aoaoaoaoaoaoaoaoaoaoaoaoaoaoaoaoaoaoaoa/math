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

## Lake package sharing

All worktrees share dependency checkouts and dependency build artifacts through manifest-keyed
pools below the primary checkout's `.lake/shared-packages/`. Each worktree's own `.lake/build/`
remains private. `scripts/share-lake-packages.sh` owns this layout; do not replace its links with
copied package directories. A host may place the pool on another filesystem by replacing
`.lake/shared-packages/` with a directory symlink; package links resolve the physical location.

The common `post-checkout` hook links new worktrees automatically. Run
`scripts/share-lake-packages.sh --install` after a fresh clone to install the hook and reconcile
all existing worktrees. The canonical check also repairs the current worktree before invoking
Lake.

Never run `lake update` against a shared package link. Detach exactly one worktree that will own
an intentional `lake update`, perform the update there, then run
`scripts/share-lake-packages.sh` to validate and move the result into its new manifest-keyed
pool. Do not detach worktrees that merely receive an already-locked toolchain or manifest through
checkout, cherry-pick, merge, or restore; reconcile them directly after the lock files change.
Only one detached update may exist at a time. Its staging tree lives beside the shared pool and
uses copy-on-write when the filesystem supports it.

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

## Ephemeral prompts

Prompts addressed to Pro or any other external model are transient execution inputs. Write them
under `/tmp`; never commit them or add them to the durable issue tracker unless explicitly
ordered. Preserve only the mathematical results that survive subsequent synthesis and audit.

## Public issue tracker

Use the repository's public GitHub issues as its durable work ledger. Open an issue when work is
material, coherent, and genuinely deferred; record the exact completed boundary, outstanding
proof obligations, dependencies, and acceptance test. Update or close issues as the mathematics
moves. Do not create ceremonial tickets for work that can be completed in the current pass, and
do not hide project work in a private auxiliary tracker.

## Salvage theorem registry

`SALVAGE.md` is the canonical index of reusable mathematics recovered from attacks that did not
settle their target. Distill every such result into a stable record or reject it; do not preserve
raw external-model reports as a substitute.

Each record states its kind, evidence, disposition, exact scope, operational use, and next
promotion step. `FRONTIER.md` cites record identifiers and owns strategy. `FORMALIZATION.md`
owns Lean-checked claims. `audits/` own bounded review evidence. Public GitHub issues own
scheduled hardening work. Never promote `reported` or `computational` evidence into a theorem
claim.

## Publication seam

`publications.json` is the canonical map from presentation-free semantic sources to routes below
`/math/` on `../eternalist.moe`. Its single `index` entry owns `/math/`; a `collection` owns a
subject landing page; a `reference` owns a reusable expository aid below a collection; every
reusable established construction, definition, lemma, or reduction is a `module`; and every
research-result exposition is a `result`. Reference, module, and result routes sit below a
collection. Adding one requires its source, its manifest entry, and its listing by its immediate
parent, but no Eternalist content patch.

Each optional `graphs` entry binds a collection to one typed JSON proof graph. Public graph nodes
contain established mathematics only. `requires` edges state logical dependency and must be
acyclic; lateral relations may record specialization, instantiation, strengthening, transport, or
dispute without changing the proof order. Open cuts, attack status, probabilities, and roadmaps
remain in repository ledgers and never enter the public graph.

Every listed source must contain no `<style>` element, inline `style` attribute, or stylesheet
link. Eternalist owns typography, color, layout, responsive behavior, and print presentation
through its central house styles. Use only the semantic class hooks defined by Eternalist's
dense-publication profile; change that shared contract at its owner rather than creating
page-local presentation.

Eyebrows are forbidden unless explicitly requested. Do not add kickers, supertitles, numbered
pre-headings, category copy above titles, or other small text whose function is to occupy visual
space. Every surviving label must change the interpretation of the object it labels.

Long-form module and result expositions use the exact top-level partition **Known Stuff** /
**New Stuff** / **Bookkeeping**. The informality of “Stuff” is intentional. Definitions,
inherited results, and prior art belong under Known Stuff; New Stuff begins at the first claim
proved by the present work and contains its proof and consequences. Bookkeeping owns validation,
provenance, artifact links, priority qualifications, and references.

Each canonical top-level section is a native `<details>` disclosure, closed by default, with its
real `h2` inside the `summary`. Do not replace this with JavaScript, synthetic buttons, or
presentational concealment. Subsection fragment links must remain capable of revealing their
closed ancestor, and print must expose all section contents.

Every long-form module or result begins its `.shell` with one visible
`<section class="abstract" aria-label="Abstract">` before the contents. State the searchable
problem name, parameters, conclusion, restrictions, consequences, and unresolved boundary with
the density of the existing verdict blocks. This prose is the sole abstract source; Eternalist
derives description metadata from it. Do not maintain a hidden or separately authored abstract.

The standalone HTML owns its mathematics directly. Author every structurally mathematical
expression as native MathML; matrices use `mtable`. Do not introduce MathJax, KaTeX, TeX
preprocessing, generated equation images, CSS-drawn notation, or a second mathematical source.
Unicode remains lawful for isolated symbols in prose, titles, metadata, and literal words. A
`.formula` is presentation around one direct `<math display="block">` child, never a substitute
for mathematical markup.

The contents list must mirror the document hierarchy through `h4`: `h2`, `h3`, and `h4` links
occupy successive nested list levels. Every `h2`, `h3`, and `h4` owns a stable fragment `id` and
ends with exactly one semantic self-link of the form
`<a class="fragment-link" href="#section-id" aria-label="Link to this section">#</a>`.
The source owns this fragment contract; Eternalist owns its presentation. `h5` is a local heading
inside a bounded proof component and does not enter the page-level contents.

After changing a listed source, the manifest, or any artifact a source describes, publication is
incomplete until `scripts/publish.sh` succeeds. This repository owns that release transaction
autonomously; Eternalist supplies the import, presentation, and deployment contracts. A normal
GitHub push does not update the live site.

## Lean proof style

Finished proofs expose a static proof DAG, not the temporal trace of interactive
proof search. Use ordinary Lean and mathlib naming, formatting, namespace, and
lint conventions, sharpened by the following rules:

- Prefer direct proof terms when their structure is immediately legible.
- Otherwise build the proof from semantically named `have` declarations,
  `calc` chains, explicit constructors, and `refine` applications that expose
  the outer term.
- Write known theorem arguments explicitly. Naked `apply` sequences are
  exploratory residue.
- Preserve hypotheses; derive normalized forms as new named facts instead of
  rewriting or simplifying hypotheses in place.
- Put automation at leaves whose exact proposition is visible. Important
  proofs must expose their logical skeleton.
- Make cases and induction branches explicit and named. Avoid dependence on
  ambient goal ordering.
- Avoid `simp_all`, `at *`, long semicolon pipelines, `all_goals`, `any_goals`,
  goal swapping, and comparable global proof-state mutation unless the final
  proof has an irreducible reason to require them.

For example:

```lean
def compose {A B C : Sort*} (f : A → B) (g : B → C) (x : A) : C :=
  g (f x)

theorem transport {α : Sort*} {P : α → Prop} {x y : α}
    (hxy : x = y) (hx : P x) : P y := by
  have hy : P y := by
    simpa [hxy] using hx
  exact hy

theorem chain {α : Type*} [Preorder α] {a b c d : α}
    (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) : a ≤ d := by
  calc
    a ≤ b := h₁
    _ ≤ c := h₂
    _ ≤ d := h₃
```

After discovery, refactor accepted tactic scripts until their outer logic,
meaningful intermediate propositions, relational chains, and automation
boundaries are visible without mentally executing the proof state.

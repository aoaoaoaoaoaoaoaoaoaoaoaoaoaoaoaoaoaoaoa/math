# Halava and Holub (2011)

**Citation.** Vesa Halava and Štěpán Holub, “Reduction Tree of the Binary
Generalized Post Correspondence Problem,” *International Journal of Foundations of
Computer Science* **22**(2), 473–490, 2011.

- DOI: https://doi.org/10.1142/S0129054111008143
- Author PDF: https://www.karlin.mff.cuni.cz/~holub/soubory/Tree.pdf
- Local PDF: `halava-holub-2011-binary-gpcp-reduction-tree.pdf`
- Retrieved: 2026-07-21
- SHA-256: `11c49da4da37894b610f2a93c47bcd9fe17342519627cf84c1b16826b1579871`

## Results used

The paper studies GPCP whose source alphabet has two letters. It analyzes letter,
beginning, and end blocks, bounds the number of end blocks, and shows how several
successors can under stated hypotheses be compressed into one instance. It also identifies
a gap in the earlier Ehrenfeucht–Karhumäki–Rozenberg binary-PCP proof and points to the
complete Halava–Harju–Hirvensalo proof.

For this project it supplies structural machinery at the decidable lower endpoint
`GPCP(2)`. Together with the present proof of undecidability of `GPCP(4)`, it isolates
`GPCP(3)` as the exact source-alphabet frontier and suggests successor/end-block
compression as a principled alternative to ad hoc tile fusion.

## Audit notes

The abstract says the construction “implies that binary GPCP can be decided in polynomial
time.” The conclusion is more circumspect: the nearly nonbranching reduction tree strongly
indicates polynomial time, while depth, short solutions, and one-letter-block cases require
additional work beyond the paper. We therefore rely on the established decidability of
`GPCP(2)` and on the proved reduction-tree structure, not on a completed polynomial-time
bound from this article alone.

Here “binary GPCP” means a two-letter source alphabet, matching the bounded-GPCP
parameter relevant to this campaign; it does not merely mean a binary target alphabet.

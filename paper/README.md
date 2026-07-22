# Working Note

`main.tex` is the current eight-page manuscript of the `GPCP(4)` and `M₃(5)` results. The
author field remains a placeholder.

Build from the project root with the complete verification suite:

```sh
./scripts/check.sh
```

For a manuscript-only build, run `tectonic main.tex` in this directory.

The manuscript proves the four-tile source equivalence directly, gives the fresh-marker
five-pair repair, derives the exact five-matrix theorem, and states the Lean trust boundary.
It does not rely on Rote's long unary terminal guard. Neary's Lemma 9 restricted-tag
universality theorem remains the sole external theorem in the undecidability wrapper.

Before submission, obtain independent review of the source theorem and exact Neary parameter
identification, then ask the source/GPCP/matrix authors whether either headline result is known
under another convention.

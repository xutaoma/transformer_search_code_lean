# Lean 4 proofs

One Lean 4 + Mathlib project with two libraries:

| Library | Paper | Statements | Details |
|---|---|---|---|
| `DFSLean/` | Training dynamics: Sec. 4 and App. C (Prop. 4.1, Lemmas C.1–C.4, Cor. C.3, Thm C.5, **Thm 4.2**) | `DFSLean/Spec.lean`, `DFSLean/Spec2.lean` | [`DFSLean/README.md`](DFSLean/README.md) |
| `DFSExpr/` | Expressivity: Sec. 3 and its appendix | `DFSExpr/Spec.lean` | [`DFSExpr/README.md`](DFSExpr/README.md) |

Lean `v4.36.0-rc2` (`lean-toolchain`) and Mathlib commit `e75a902d` (`lakefile.toml`, `lake-manifest.json`).

## Build

Install [elan](https://github.com/leanprover/elan); it downloads the pinned Lean version automatically. Then:

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build           # builds DFSLean, DFSExpr and the statement check SpecCheck
```

A successful build has:
* no errors;
* "declaration uses sorry" warnings only from the three `Spec.lean`/`Spec2.lean` files. They state the
  theorems without proofs, and nothing depends on them;
* axiom reports from `SpecCheck` showing that every main theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`.

## How the statements are checked

Each statement in a `Spec` file, e.g. `DFS.Spec.learning_dynamics`, is proved under the same name without
`Spec.` in another file. `DFSLean/SpecCheck.lean` and `DFSExpr/SpecCheck.lean` contain one line per theorem:

```lean
example : type_of% @DFS.Spec.learning_dynamics := @DFS.learning_dynamics
```

This compiles only if the proved theorem has exactly the stated type. So to see what is proved, read the
`Spec` files and the definitions they use (`DFSLean/Defs.lean`, `DFSLean/Model.lean`, `DFSExpr/Defs.lean`).

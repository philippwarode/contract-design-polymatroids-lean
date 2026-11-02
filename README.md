# Lean formalization of continuous contract design over polymatroids

This repository contains the `ContractDesignPolymatroids` Lean 4 library accompanying *The Complexity of Continuous Contract Design over Polymatroids* by Max Klimm, Paul Lippke, and Philipp Warode. The initial public release was a standalone copy of `lean/Stoc/` from source commit `c385cfd63f31929e95d6fbf1e86849b615223ba5` of the authors' working repository. It contains no files from that repository's separate `Paper` or `Research` Lean libraries.

The source is organized after the paper: preliminaries, linear costs, best responses, optimal shares, subclasses, hardness, approximation, and general convex costs. [COVERAGE.md](COVERAGE.md) maps paper labels to Lean declarations and records where the formalization is partial. The recorded scope has 66 results marked `follows`, 15 marked `partly`, and 0 with no mathematical assertion to formalize. A formalization of a mathematical core does not automatically cover every running-time or machine-model claim in the corresponding paper result.

## Build

The project pins Lean in `lean-toolchain` and Mathlib in `lake-manifest.json`. With [elan](https://lean-lang.org/install/) installed, run from the repository root:

```sh
lake exe cache get
lake build ContractDesignPolymatroids
```

The first command downloads Mathlib's compiled cache; the second checks the complete `ContractDesignPolymatroids` library. Build products stay in `.lake/` and are not committed. The files `ContractDesignPolymatroids.lean` and `ContractDesignPolymatroids/` are the formalization; `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` fix its dependencies. Declaration names retain the `Stoc` namespace, as listed in `COVERAGE.md`.

## Citation and license

Cite a tagged release or the version-specific Zenodo DOI when available, so that the cited proofs do not change as this repository evolves. GitHub can display citation metadata from `CITATION.cff`. The code is licensed under the MIT License.

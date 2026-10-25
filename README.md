# EPPA for reducts — Lean formalization

Lean 4 formalization project associated with research on EPPA for reducts of the random graph and related hypergraphs.

**Scope:** coherent EPPA for finite two-graphs, and non-EPPA for finite equivalence relations on (r)-element subsets (and injective ordered (r)-tuples) with at most (m) classes, for (r,m\ge 2).

**Status:** repository setup only. Neither main result is yet formalized or certified.

The manuscript and its LaTeX sources are **private**, not part of this repository. This repository contains only explicitly public Lean code, CI configuration, and project-level metadata.

## Build

Lean and Mathlib are pinned in `lean-toolchain` and `lakefile.toml`. After installing elan:

```sh
lake update
lake exe cache get
lake build
```

GitHub Actions runs builds and audits the logical axioms used by the project. Successful CI establishes compilation/audit of the code present at that commit, not completeness of the mathematical goals.

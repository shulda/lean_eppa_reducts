# EPPA for reducts — Lean formalization

A public Lean 4 project for two selected results about reducts of the random graph.

**Target statements (not yet proved in Lean):**

- Coherent EPPA for finite two-graphs.
- Failure of EPPA for equivalence relations on unordered `r`-subsets or on ordered injective `r`-tuples, with at most `m` equivalence classes, for all `r, m ≥ 2`.

**Current status (26 October 2026):** audited positive development includes a finite valuation two-graph in the exact approved target API, combined index/matrix automorphisms, their semidirect composition law and a faithful quotient by the single globally constant symmetric matrix. The negative branch includes class-label recovery and fixed-vertex bounds. Neither principal EPPA result has been proved; transversal extension, coherence and the negative coset obstruction remain open.

The research manuscript and LaTeX sources remain **private**. This public repository is for Lean code, build infrastructure, and public project metadata only.

## Build

Toolchain: Lean v4.34.1 and Mathlib v4.34.1; the common `AllThoseEPPA` language and EPPA vocabulary is pinned as a dependency.

```sh
lake update
lake exe cache get
lake build
```

The GitHub Actions workflow checks compilation, rejects `sorry`/`admit` and custom axioms, audits logical axioms, and rejects accidentally tracked LaTeX manuscript files. A green badge confirms only the declarations actually present in that commit.

## Progress and recovery

See [FORMALIZATION.md](FORMALIZATION.md) for the authoritative public scope, exact CI checkpoints, proof milestones, project recovery instructions, and the next planned steps. The unpublished LaTeX source and private expanded proof manuscript are not stored here.

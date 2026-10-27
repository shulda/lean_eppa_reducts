# EPPA for reducts of the random graph — Lean 4 formalization

This is the public mathematical guide to the Lean development in [`shulda/lean_eppa_reducts`](https://github.com/shulda/lean_eppa_reducts). It documents *proved* theorems and their exact semantics, not merely project intentions.

**Verified baseline (27 October 2026):** [commit `d12d133a`](https://github.com/shulda/lean_eppa_reducts/commit/d12d133a37d909837c6fbf4c7409f699f2918264), [full GitHub Actions build and axiom audit #40471101713](https://github.com/shulda/lean_eppa_reducts/actions/runs/40471101713). The audit checked **1,121 declarations** in `EPPAReducts` and admitted only `propext`, `Classical.choice`, and `Quot.sound`.

## Proven results

1. **Coherent EPPA for all finite two-graphs**, including the empty input, with one finite induced extension and a simultaneous choice of extensions respecting composition.
2. **Failure of EPPA for unlabelled equivalences on unordered $r$-element subsets**, for every $r,m\ge 2$, when there are at most $m$ equivalence classes.
3. **Failure of EPPA for unlabelled equivalences on ordered injective $r$-tuples**, for every $r,m\ge 2$, under the same class bound.
4. **Failure of EPPA for finite graphs modulo global complementation**, as the $r=m=2$ case of item 2.

The underlying exact Lean theorem types, with source links, are in [Main theorems](Main-theorems.md).

**Scope boundary:** the rooting reduction from two-graphs modulo complementation to graphs modulo complementation, the consequent failure of EPPA for that fifth reduct, and the final five-reduct classification were **not yet part of the audited baseline above**. They are being formalized separately; a manuscript assertion must not be reported as Lean-checked until the new theorem has passed CI and axiom audit.

## Guide

- [Main theorems](Main-theorems.md): precise statements in mathematical language and exact checked declarations.
- [Mathematical definitions](Mathematical-definitions.md): two-graphs, unlabelled class relations, induced embeddings, partial automorphisms, coherence.
- [Proof architecture](Proof-architecture.md): valuation construction and normalizer-coset obstructions.
- [Adversarial audit](Adversarial-audit.md): paper-to-Lean fidelity, deliberate differences and exclusions.
- [Verification](Verification.md): SHA, CI, trusted axioms, reproducible build.
- [Using the library](Using-the-library.md): imports and checked entry points.
- [Publishing](Publishing.md): source-controlled Wiki synchronization.

**Confidentiality:** the unpublished research manuscript, its LaTeX source, bibliography, and internal expanded proof notes are not part of this public repository. This guide contains independently written statements about the already-public Lean declarations, not manuscript text.

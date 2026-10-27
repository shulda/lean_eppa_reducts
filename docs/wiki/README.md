# EPPA for reducts of the random graph — Lean 4 formalization

This is the public mathematical guide to the Lean development in [`shulda/lean_eppa_reducts`](https://github.com/shulda/lean_eppa_reducts). It documents *proved* theorems and their exact semantics, not merely project intentions.

**Original certified baseline (27 October 2026):** [commit `d12d133a`](https://github.com/shulda/lean_eppa_reducts/commit/d12d133a37d909837c6fbf4c7409f699f2918264), [full GitHub Actions build and axiom audit #40471101713](https://github.com/shulda/lean_eppa_reducts/actions/runs/40471101713). The audit checked **1,121 declarations** in `EPPAReducts` and admitted only `propext`, `Classical.choice`, and `Quot.sound`.

**Extended certified main (27 October 2026):** [commit `3f35830e3493`](https://github.com/shulda/lean_eppa_reducts/commit/3f35830e34938d91fd082c5f9c9ef47b8e371c98), [full Lean build and axiom audit #40517057037](https://github.com/shulda/lean_eppa_reducts/actions/runs/40517057037). **1,290 declarations** checked; the only logical axioms are `propext`, `Classical.choice`, `Quot.sound`.

## Proven results

1. **Coherent EPPA for all finite two-graphs**, including the empty input, with one finite induced extension and a simultaneous choice of extensions respecting composition.
2. **Failure of EPPA for unlabelled equivalences on unordered $r$-element subsets**, for every $r,m\ge 2$, when there are at most $m$ equivalence classes.
3. **Failure of EPPA for unlabelled equivalences on ordered injective $r$-tuples**, for every $r,m\ge 2$, under the same class bound.
4. **Failure of EPPA for finite graphs modulo global complementation**, as the $r=m=2$ case of item 2.
5. **The complete rooting reduction** from finite two-graphs modulo complementation to finite graphs modulo complementation, and **failure of EPPA for the former** (both class-level implication and explicit finite obstruction).

The underlying exact Lean theorem types, with source links, are in [Main theorems](Main-theorems.md).

**Scope boundary:** the standalone full five-reduct *EPPA/coherent-EPPA table* has not yet been certified as one Lean theorem. The general model-theoretic fact that Thomas's five classes exhaust all reducts is also not a formalized theorem here; that historical classification is an external ingredient. See [Rooting reduction](Rooting-reduction.md) and [Main theorems](Main-theorems.md) for exactly what is checked.

## Guide

- [Rooting reduction](Rooting-reduction.md): full class-level reduction and fifth-reduct non-EPPA, with precise witness transfer.
- [Main theorems](Main-theorems.md): precise statements in mathematical language and exact checked declarations.
- [Mathematical definitions](Mathematical-definitions.md): two-graphs, unlabelled class relations, induced embeddings, partial automorphisms, coherence.
- [Proof architecture](Proof-architecture.md): valuation construction and normalizer-coset obstructions.
- [Adversarial audit](Adversarial-audit.md): paper-to-Lean fidelity, deliberate differences and exclusions.
- [Verification](Verification.md): SHA, CI, trusted axioms, reproducible build.
- [Using the library](Using-the-library.md): imports and checked entry points.
- [Publishing](Publishing.md): source-controlled Wiki synchronization.

**Confidentiality:** the unpublished research manuscript, its LaTeX source, bibliography, and internal expanded proof notes are not part of this public repository. This guide contains independently written statements about the already-public Lean declarations, not manuscript text.

# EPPA for reducts — Lean 4 formalization

## Research wiki and semantic audit

The [source-controlled research wiki](docs/wiki/README.md) documents the mathematical results in reader-facing language, links each certified theorem to exact Lean declarations, and gives the proof architecture, semantic audit and reproducibility instructions. Its [publishing workflow](.github/workflows/publish-wiki.yml) can synchronize the [GitHub Wiki](https://github.com/shulda/lean_eppa_reducts/wiki) once the independent Wiki remote is initialized. The unpublished manuscript remains private.


A public formalization of selected EPPA results for finite relational structures. The research manuscripts and their LaTeX sources remain **private** and are not stored in this repository.

## Certified mathematical results

All statements below have been compiled as actual Lean theorems and checked by an allowed-axiom audit in the imported `EPPAReducts` project.

| Mathematical statement | Exact Lean theorem | Source |
| --- | --- | --- |
| **Every finite two-graph has coherent EPPA**, including the empty input. One finite induced witness simultaneously extends every partial automorphism, preserving identity and composition. | `EPPAReducts.TwoGraphs.humanTwoGraphsHaveCoherentEPPA : HumanTargets.twoGraphsHaveCoherentEPPA` | [FiniteCoherentEPPA.lean](EPPAReducts/TwoGraphs/FiniteCoherentEPPA.lean) |
| **For all `r,m ≥ 2`**, equivalence relations on ordered *injective* `r`-tuples with at most `m` classes fail ordinary EPPA. | `EPPAReducts.BoundedEquivalence.orderedBoundedEquivalencesFailEPPA` | [OrderedNoEPPAWitness.lean](EPPAReducts/BoundedEquivalence/OrderedNoEPPAWitness.lean) |
| **For all `r,m ≥ 2`**, equivalence relations on unordered `r`-element subsets with at most `m` classes fail ordinary EPPA. | `EPPAReducts.BoundedEquivalence.allUnorderedBoundedEquivalencesFailEPPA : unorderedBoundedEquivalencesFailEPPA` | [UnorderedNoEPPAWitness.lean](EPPAReducts/BoundedEquivalence/UnorderedNoEPPAWitness.lean) |
| **Finite graphs modulo global complementation fail EPPA**, as the `r=m=2` specialization. | `EPPAReducts.BoundedEquivalence.humanGraphsModuloComplementationFailEPPA : HumanTargets.graphsModuloComplementationFailEPPA` | [UnorderedNoEPPAWitness.lean](EPPAReducts/BoundedEquivalence/UnorderedNoEPPAWitness.lean) |

The [author-approved Lean specifications](EPPAReducts/HumanTargets.lean) are independent of the proofs. For the negative results the equivalence classes are **unlabelled**: automorphisms may permute classes. In particular, a graph *modulo complementation* is represented by an equivalence relation on unordered distinct vertex pairs having at most two classes, not by a graph assumed to possess a complementing automorphism. All non-EPPA theorems rule out **every finite induced common EPPA witness** for one explicitly constructed finite obstruction; they do not merely fail for a selected extension.

## Reproducible certification

The full [Lean CI run 40470086340](https://github.com/shulda/lean_eppa_reducts/actions/runs/40470086340) succeeded on `main` commit [`3f621d41`](https://github.com/shulda/lean_eppa_reducts/commit/3f621d4137cb53f59ec30812523c76240334ac6c), including all four exact theorem declarations above. The audited integration commit [`4fafd64d`](https://github.com/shulda/lean_eppa_reducts/commit/4fafd64da44f072e0d73ae78f272d974096c56da) additionally reports **1,121 declarations** under `EPPAReducts`, with only `propext`, `Classical.choice`, and `Quot.sound` as allowed logical axioms.

The workflow also rejects `sorry`, `admit`, added `axiom` declarations and tracked LaTeX sources. The CI result certifies the exact imported declarations **at the checked commit**, not hypothetical unstaged proofs.

## Local build

The project uses Lean **v4.34.1** and a pinned Mathlib dependency, plus the `AllThoseEPPA` interface as a separate dependency.

```sh
lake exe cache get
lake build
```

See [FORMALIZATION.md](FORMALIZATION.md) for the complete milestone ledger, checked proof interfaces, GitHub Actions links and recovery procedure. Private manuscripts and internal proof notes must not be committed to this public repository without explicit permission.

# EPPA for reducts — Lean 4 formalization

## Research wiki and semantic audit

The [source-controlled research wiki](docs/wiki/README.md) documents the mathematical results in reader-facing language, links each certified theorem to exact Lean declarations, and gives the proof architecture, semantic audit and reproducibility instructions. Its [publishing workflow](.github/workflows/publish-wiki.yml) can synchronize the [GitHub Wiki](https://github.com/shulda/lean_eppa_reducts/wiki) once the independent Wiki remote is initialized. The unpublished manuscript remains private.


A public Lean 4 formalization of the five-class EPPA/coherent-EPPA status table for the reducts of the random graph, including the rooting reduction and a general negative theorem for bounded equivalences. The research manuscripts and their LaTeX sources remain **private** and are not stored in this repository.

## Complete five-reduct EPPA-status classification

The actual Lean theorem [`Classification.fiveReductEPPAClassification`](EPPAReducts/Classification/FiveReductEPPA.lean) proves this table as a conjunction of **ten quantified EPPA and coherent EPPA propositions**, not an array of assumed truth values:

| Finite structures | EPPA | Coherent EPPA |
| --- | :---: | :---: |
| Simple graphs | Yes | Yes |
| Finite sets | Yes | Yes |
| Two-graphs | Yes | Yes |
| Graphs modulo global complementation | No | No |
| Two-graphs modulo global complementation | No | No |

The positive graph result has a genuine finite `SimpleGraph` witness. Both complementation classes have **unnamed** equivalence classes and may swap their classes under automorphisms. The [rooting reduction](EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean) is proved as a universal class-level implication. [The Wiki classification](docs/wiki/Five-reduct-classification.md) documents the exact sources and quantifiers. The classical theorem of Thomas enumerating *all* first-order reducts is an external model-theoretic result, **not** formalized here.

**Exact integrated-main certification:** commit [`9178c621d64c`](https://github.com/shulda/lean_eppa_reducts/commit/9178c621d64cea2e73e65b725bacbd3fc9648ada), [full Lean CI #40529501919](https://github.com/shulda/lean_eppa_reducts/actions/runs/40529501919), **1,666 build jobs and 1,338 axiom-audited declarations**; only `propext`, `Classical.choice`, and `Quot.sound`.

## Additional independently certified results

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

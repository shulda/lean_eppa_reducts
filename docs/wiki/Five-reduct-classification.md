# EPPA and coherent EPPA: classification of the five finite reduct classes

This is the **formally verified status table** for the five finite classes associated with the reducts of the countable random graph. It is one Lean theorem with ten mathematical propositions, **not** a list of Boolean answers. The separate classical theorem of Thomas identifying these five classes as *all* first-order reducts is an external model-theoretic result and is not formalized in this repository.

## Mathematical statement

| Finite class | EPPA | Coherent EPPA |
| --- | :---: | :---: |
| $\mathcal G$ — finite simple graphs | **Yes** | **Yes** |
| $\mathcal S$ — finite sets | **Yes** | **Yes** |
| $\mathcal T$ — finite two-graphs | **Yes** | **Yes** |
| $\mathcal G^\pm$ — graphs modulo global complementation | **No** | **No** |
| $\mathcal T^\pm$ — two-graphs modulo global complementation | **No** | **No** |

**Certified Lean declaration:** [`EPPAReducts.Classification.fiveReductEPPAClassification`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean), of type `FiveReductEPPAClassification`. The conjunction quantifies over finite input structures and their genuine EPPA or coherent-EPPA witnesses, with induced embeddings and extensions of **all** partial automorphisms. Each negative claim excludes common witnesses for the entire corresponding class.

## Five rows: precise proof routes

**$\mathcal G$ — yes/yes.** [`graphsHaveEPPA` and `graphsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean) follow from [`finiteSimpleGraphsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrizationCoherence.lean). This produces a finite **`SimpleGraph` witness**, not just a general binary-relational structure. A coherent binary-relational witness from the pinned, independently verified `AllThoseEPPA` dependency is normalized to its mutual, off-diagonal edges. Induced embeddings, full automorphisms and the coherent extension equations are transferred explicitly in [`GraphSymmetrization.lean`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrization.lean), [`GraphSymmetrizationAutomorphism.lean`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrizationAutomorphism.lean), and [`GraphSymmetrizationCoherence.lean`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrizationCoherence.lean).

**$\mathcal S$ — yes/yes.** [`finiteSetsHaveEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/OrdinaryPositiveCorollaries.lean) and [`setsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean) use the actual extension map of all partial permutations on a finite set, proved by [`finiteSetsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/PositiveBaselines.lean).

**$\mathcal T$ — yes/yes.** [`finiteTwoGraphsHaveEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/OrdinaryPositiveCorollaries.lean) is derived from [`humanTwoGraphsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/TwoGraphs/FiniteCoherentEPPA.lean). This uses an actual four-point-even two-graph, a finite common induced valuation witness, and a simultaneous compositional extension. It includes the empty input structure.

**$\mathcal G^\pm$ — no/no.** This is the class of equivalence relations on unordered **distinct pairs**, with at most two **unnamed** classes. Automorphisms may exchange the classes. [`graphsModuloNotHaveEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean) is derived from the explicit negative pair-equivalence obstruction, and [`graphsModuloNotHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean) follows via a separately proved coherent-to-ordinary implication.

**$\mathcal T^\pm$ — no/no.** This is an equivalence relation on unordered **triples** whose class kernel admits a true four-point-even two-graph representative. Its classes are unnamed and may be exchanged. [`twoGraphsModuloNotHaveEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean) follows by the formally verified [rooting reduction](Rooting-reduction), while [`twoGraphsModuloNotHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean) again uses an explicit quantified coherent witness definition and a proved implication to ordinary EPPA.

## Audit boundary

The **whole two-column table** is formalized. This does **not** also certify Thomas's independent enumeration of the closed permutation supergroups of the random graph, nor the article's specific six-vertex illustration of the graph-modulo-complementation obstruction. The former is used externally; the latter is replaced by a different, general, formally checked finite obstruction. The manuscript's further discussion of looped graphs and random hypergraphs is outside this certificate.

The proof code passed [full integrated-main CI #40529501919](https://github.com/shulda/lean_eppa_reducts/actions/runs/40529501919) at [commit `9178c621d64c`](https://github.com/shulda/lean_eppa_reducts/commit/9178c621d64cea2e73e65b725bacbd3fc9648ada): **1,666 successful build jobs, 1,338 declarations axiom-audited**, with only `propext`, `Classical.choice` and `Quot.sound`. The originating theorem-source commit [`26004874e21d`](https://github.com/shulda/lean_eppa_reducts/commit/26004874e21da1cf8187c68b7ae7553361eb61f2) independently passed [CI #40528044634](https://github.com/shulda/lean_eppa_reducts/actions/runs/40528044634).

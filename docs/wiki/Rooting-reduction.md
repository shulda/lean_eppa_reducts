# Rooting reduction — mathematical theorem and exact semantic audit

The target classes have **unnamed** colour classes. Let \(\mathcal G^\pm\) denote finite vertex sets equipped with one equivalence relation on unordered distinct pairs with at most two classes; let \(\mathcal T^\pm\) denote finite vertex sets with one equivalence relation on unordered distinct triples, admitting a two-graph representative (the indicator has even parity on each four-element set). Every embedding is induced. Class labels may be interchanged by both partial and full automorphisms.

## What Lean proves

**Rooting reduction.** If \(\mathcal T^\pm\) has EPPA, then \(\mathcal G^\pm\) has EPPA. This is the actual universal statement about *all finite structures and all their partial automorphisms*, not merely a reduction for one conveniently chosen obstruction. See [graphsModuloHaveEPPA_of_twoGraphsModulo](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean).

**Consequence.** Neither \(\mathcal G^\pm\) nor \(\mathcal T^\pm\) has ordinary EPPA. See [graphsModuloNotHaveEPPA](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean), [twoGraphsModuloNotHaveEPPA](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean) and the *explicit* obstruction theorem [twoGraphsModuloFailEPPA](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPartialAutomorphism.lean).

## Why the reduction works

Start with a finite unlabelled pair-class structure, choose an auxiliary Boolean presentation of its two classes, and adjoin a new isolated root \(\ast\). Define the triple parity by

\[
t(\ast,x,y)=c(\{x,y\}),\qquad
t(x,y,z)=c(\{x,y\})+c(\{x,z\})+c(\{y,z\})\pmod 2.
\]

This is a genuine two-graph: on four vertices, every unordered pair contributes twice to the total parity of the four triples. The source embedding preserves and reflects equality of the **unnamed** classes of rooted triples.

Any partial automorphism of the old pair-class structure changes its chosen Boolean pair-colour presentation by one global bit \(\delta\), including the degenerate small-domain cases. Fixing the root gives a literal partial bijection on the enlarged carrier. For pairs incident with the root, apply a gauge value \(\delta\) at the root and zero elsewhere; the augmented edge colouring changes by \(\delta+f(u)+f(v)\). Three edge contributions yield precisely one \(\delta\) on every triple, since \(3\delta=\delta\) and every gauge vertex occurs twice in characteristic two. Thus the **equality kernel** of the triple colouring is preserved: the map is an authentic partial automorphism of the unlabelled triple-class structure.

Now assume this rooted object embeds into a finite EPPA witness \(C\). Restrict at the embedded root: the equivalence relation on triples containing the root induces one on pairs of non-root vertices. This is the root shadow \(B\). Every extension of a rooted partial automorphism fixes the root; its restriction to non-root vertices is therefore an automorphism of \(B\), possibly interchanging the two unnamed pair classes, and extends the old partial automorphism. Hence \(B\) is a single common finite EPPA witness for the original \(A\).

The existing finite graph-modulo-complementation obstruction rules this out. This proves failure of ordinary EPPA for \(\mathcal T^\pm\), and therefore also failure of coherent EPPA.

## Source-to-Lean contracts

| Requirement | Certified Lean construction |
| --- | --- |
| Actual unlabelled triple classes with a genuine two-graph representative | [ModuloComplementation.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/ModuloComplementation.lean) |
| Four-point evenness of the rooted triple indicator | [PairTriangleTwoGraph.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/PairTriangleTwoGraph.lean), [RootingPairColours.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPairColours.lean) |
| Exact pair-class / rooted triple-class agreement | [RootedTripleKernel.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootedTripleKernel.lean) |
| Root-fixed literal source/target bijection | [RootingPartialLift.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPartialLift.lean) |
| Global unlabelled pair-class shift | [RootingColourShift.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingColourShift.lean) |
| Gauge / triple parity, including all distinct triples | [GaugeParityIdentity.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/GaugeParityIdentity.lean), [PairParityMapTransport.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/PairParityMapTransport.lean), [RootingPairGauge.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPairGauge.lean) |
| Every rooted partial automorphism really preserves triple-class equality | [RootingPartialAutomorphism.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPartialAutomorphism.lean) |
| Arbitrary finite root-shadow witness and restriction of its automorphisms | [RootingShadow.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingShadow.lean), [RootShadowInduced.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootShadowInduced.lean), [RootShadowAutomorphism.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootShadowAutomorphism.lean) |
| Conditional witness transfer, with its premise then discharged | [RootingTransfer.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingTransfer.lean), [RootingPartialAutomorphism.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPartialAutomorphism.lean) |
| Universal EPPA class implication and non-EPPA | [RootingGlobalTransfer.lean](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean) |

## Certification and limits

[Full main build and allowed-axiom audit #40517057037](https://github.com/shulda/lean_eppa_reducts/actions/runs/40517057037) passed on [commit 3f35830e3493](https://github.com/shulda/lean_eppa_reducts/commit/3f35830e34938d91fd082c5f9c9ef47b8e371c98) with **1,290 declarations**, using only Lean's standard logical axioms `propext`, `Classical.choice` and `Quot.sound`. The final rooting and no-EPPA conclusions have **no unproved hypothesis**.

The private paper's six-vertex *illustration* of the graph obstruction has not been checked as a separate theorem: the general formally verified obstruction is more than sufficient. The classical external assertion that these five classes are *all* first-order reducts of the countable random graph is a different theorem and is **not** proved here.
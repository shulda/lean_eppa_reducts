# Formalization ledger — EPPA for reducts

**Repository:** `shulda/lean_eppa_reducts` (**not** any other EPPA project).
**Source of mathematical claims:** private Project source `eppa_reducts8.tex`; not tracked by Git.
**Confidentiality rule:** never push LaTeX, bibliography, manuscript extracts, or an internal detailed proof manuscript to this public repository before explicit author approval.
**Updated:** 2026-10-26 (full coherent EPPA for all finite two-graphs certified on the work branch; negative EPPA theorem open).

## Scope and acceptance targets

Only two load-bearing results are intended:

1. Every finite two-graph has **coherent EPPA**. The user-facing formulation quantifies over all isomorphisms between induced substructures and a compositional choice of extensions.
2. For every `r,m ≥ 2`, finite equivalence relations on **unordered r-element subsets** with **at most m equivalence classes** fail EPPA; likewise for **ordered injective r-tuples**. The human-facing final corollary specializes `r=m=2` to graphs **modulo global complementation**.

**Important:** a graph modulo complementation is an unlabelled equivalence relation on unordered pairs with ≤2 classes, **not** a graph that happens to admit a complementing automorphism. A model with `m` named edge colours has the wrong automorphism group and is not the intended target.

The human-readable English formulations were approved by the author on 2026-10-25. The self-contained **Lean** formulations in `EPPAReducts/HumanTargets.lean` were reviewed and approved by the author on 2026-10-25. Their definitions are frozen acceptance targets. The private paper draft may evolve in exposition or proof details; the mathematical targets should remain stable. The expanded **private** mathematical manuscript is now `eppa_reducts_formalization_v2.tex` (18-page PDF), superseding `v1` and `v0`. It is a provisional mathematical proof plan, **not** a Lean-verified theorem or an external referee certification. Do not silently weaken them by restricting carrier size, considering only a chosen graph representative, requiring exactly `m` classes, naming colours, or assuming coherence only for full automorphisms.

Explicitly out of scope: the six-vertex exposition as a separate theorem, the rooting transfer to complementary two-graphs, looped-graph EPPA, and the claimed wider hypergraph reduct classification. These may be optional regression tests or later projects, but they are not part of the requested certification.

## Current verified state

- [x] **2026-10-26 (certified at proof commit `643f6856ca87a9791c142bf8c504035e1fad6cb1`, [CI 40336732374](https://github.com/shulda/lean_eppa_reducts/actions/runs/40336732374)):** `BoundedEquivalence/TwistedTransporter.lean` establishes `twistedTransporterEquivStabilizer`, an actual equivalence between the transporter fiber from `u • x` to `x` and `MulAction.stabilizer G x`, proves `card_twistedTransporters`, and proves `exists_transporter_iff_mem_orbit`. These are genuine finite-group-action ingredients for the coset incidence count; **the coset-orbit bound and negative EPPA obstruction are still open**.

- [x] **2026-10-26 (certified at proof commit `171153ba3cb1dbeface07b099cf2fbed6273da69`, [CI 40331155882](https://github.com/shulda/lean_eppa_reducts/actions/runs/40331155882)):** `TwoGraphs/FiniteCoherentEPPA.lean` proves `valuationTwoGraph_coherentEPPAWitness`, `allFiniteTwoGraphsHaveCoherentEPPA`, and **the exact author-approved positive target** `humanTwoGraphsHaveCoherentEPPA : HumanTargets.twoGraphsHaveCoherentEPPA`, for *all* finite two-graphs including the empty structure. The proof gives a common finite induced witness and an actual coherent choice for every literal partial bijection; identity and exact composition are certified. The factorial carrier replaces the paper's LCM only in size, not in the theorem's semantics. Full build, forbidden-placeholder check, manuscript-publication guard and allowed-axiom audit passed. **The negative result remains open.**

- [x] **2026-10-26 (certified at proof commit `171153ba3cb1dbeface07b099cf2fbed6273da69`, [CI 40331155882](https://github.com/shulda/lean_eppa_reducts/actions/runs/40331155882)):** `TwoGraphs/CanonicalCoherentLiftComposition.lean` proves `canonicalConjugatedLift_composition` for the exact `HumanTargets.IsComposition` and `canonicalConjugatedLift_identity` for every induced subset. A transient first attempt failed because Lean needed explicit unfolding of the identity partial map's endpoints; corrected in this certified proof commit.

- [x] **2026-10-26 (certified at commit `37af994e208511b0a8acae8d4ec26b38d86d748a`, [CI 40329585202](https://github.com/shulda/lean_eppa_reducts/actions/runs/40329585202)):** `TwoGraphs/CanonicalCoherentLift.lean` defines the actual ambient extension `canonicalConjugatedLift` by conjugating the middle homomorphic section with fixed endpoint transports, and proves `canonicalConjugatedLift_isAutomorphism` and `canonicalConjugatedLift_extendsOld`. The section's preservation extends to the original literal partial maps.

- [x] **2026-10-26 (certified at commit `71132d45f8ab9417ff52e587d90f0a7c23f82b9a`, [CI 40317589759](https://github.com/shulda/lean_eppa_reducts/actions/runs/40317589759)):** `TwoGraphs/CanonicalMiddleLiftComposition.lean` proves `canonicalMiddleLift_composition`, the literal partial-map composition law for the **same** chosen ambient middle subgroup section, after canonical-subset casts. Full build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `06369fdc58ae017a37bd70b0591c1355f370a3ce`, [CI 40317020415](https://github.com/shulda/lean_eppa_reducts/actions/runs/40317020415)):** `TwoGraphs/CanonicalMiddleLift.lean` defines the ambient middle lift of every normalized literal partial automorphism, proves it preserves the actual two-graph, extends the normalized action on its canonical representative, and sends the identity partial map to the identity witness permutation. Build and allowed-axiom audit passed. Composition is a separate pending obligation.

- [x] **2026-10-26 (certified at commit `4c9bd466ec8e708cb083c39bef99902c67e86ad2`, [CI 40316539767](https://github.com/shulda/lean_eppa_reducts/actions/runs/40316539767)):** `TwoGraphs/SubsetSectionCast.lean` proves that equality-conjugation of a permutation preserves the induced two-graph and, crucially, that it is sent by the **same chosen ambient subgroup section** to the same witness automorphism. Build and allowed-axiom audit passed. Ambient coherentisation remains open.

- [x] **2026-10-26 (certified at commit `2aff2f2b7cf28d14a1bf6d81c0680b7b98ef027d`, [CI 40315504173](https://github.com/shulda/lean_eppa_reducts/actions/runs/40315504173)):** `TwoGraphs/NormalizedPermutationComposition.lean` proves the composition law for normalized automorphisms of one common canonical representative under the exact approved `IsComposition`, modulo only equality-induced subtype conjugations; build and allowed-axiom audit passed. The actual ambient subgroup-section coherence is not yet proved.

- [x] **2026-10-26 (certified at commit `bb3ee42e099d696914424e9b3b2aec8bbcb244bb`, [CI 40314830060](https://github.com/shulda/lean_eppa_reducts/actions/runs/40314830060)):** `TwoGraphs/NormalizedPartialComposition.lean` proves `normalizedPartialEquiv_composition`, full functorial composition of heterogeneous normalized partial isomorphisms under the exact approved `IsComposition` predicate, including all source/middle/target canonical-subtype casts. Build and allowed-axiom audit passed. Coherent ambient extension remains open.

- [x] **2026-10-26 (certified at commit `34f1ef007e82e0be20489e64db76dbaa705b127d`, [CI 40314323730](https://github.com/shulda/lean_eppa_reducts/actions/runs/40314323730)):** `TwoGraphs/PartialCompositionEquiv.lean` proves `isComposition_subtypeEquiv`: the exact approved Option-valued partial-map composition predicate implies strict equality of the represented subtype equivalences after source/middle/target casts. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `592512a33a2da41c12b11fd8321f0516fc3b50f2`, [CI 40313851069](https://github.com/shulda/lean_eppa_reducts/actions/runs/40313851069)):** `TwoGraphs/NormalizedPartialEquiv.lean` defines heterogeneous normalization independently of any preservation proof, proves the existing normalized permutation is exactly its canonical-representative cast, and proves the source-to-target transporter square. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `bc84dd3e8b360272f477f06e171d2c5bcc4d28b1`, [CI 40313357314](https://github.com/shulda/lean_eppa_reducts/actions/runs/40313357314)):** `TwoGraphs/TransporterComposition.lean` proves generic cancellation of intermediate equivalences and composition of subtype casts, plus that equal induced subsets have the same selected direct and inverse transporters after casting. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `eb289a1d07dde6251d35c1498af97b0c4bc64765`, [CI 40312789510](https://github.com/shulda/lean_eppa_reducts/actions/runs/40312789510)):** `TwoGraphs/NormalizedTransportCompatibility.lean` proves `normalizedPartialAutomorphism_transport`, the exact chosen-source-to-target transporter compatibility identity for each normalized literal partial automorphism, including its subtype-cast equality. Full build and allowed-axiom audit passed. Coherentisation is not yet proved.

- [x] **2026-10-26 (certified at commit `419adb2179ea72c9319e9479811f75355d4739ec`, [CI 40312200656](https://github.com/shulda/lean_eppa_reducts/actions/runs/40312200656)):** `TwoGraphs/NormalizedPartialIdentity.lean` proves `normalizedPartialAutomorphism_identity` (every induced subset, including empty) and exact cancellation of its chosen representative transport equivalence. Full project build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `e776c9e7580005d3a33b62c152083586bb7f75e3`, [CI 40309163318](https://github.com/shulda/lean_eppa_reducts/actions/runs/40309163318)):** `TwoGraphs/NormalizedPartialAutomorphism.lean` proves `normalizedPartialAutomorphism`, its exact pointwise transporter formula, and `normalizedPartialAutomorphism_preserves` for every literal partial two-graph automorphism, producing an actual automorphism of the canonical induced representative. Build and allowed-axiom audit passed. Composition and final coherentisation remain open.

- [x] **2026-10-26 (certified at commit `d223a5e088f17d6c3315cbb02dd7456cb389e3c2`, [CI 40308672135](https://github.com/shulda/lean_eppa_reducts/actions/runs/40308672135)):** `TwoGraphs/PartialBijectionAlgebra.lean` proves the identity and inverse literal partial bijections preserve A, and `isComposition_bijection_apply` bridges the exact approved Option-valued IsComposition relation to pointwise composition of actual subtype equivalences. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `2d4e0faf23b157dfa8b029ba719fed5622963fa3`, [CI 40307172086](https://github.com/shulda/lean_eppa_reducts/actions/runs/40307172086)):** `TwoGraphs/InducedSubsetGroupSections.lean` packages the literal `InducedSubsetGroupSection` API, and proves simultaneous existence of homomorphic automorphism-group lifts for **every** induced subset in one C_X, including the empty subset with the identity action. Build and allowed-axiom audit passed. Generic coherentisation still outstanding.

- [x] **2026-10-26 (certified at commit `1cb9645390e4d7d89fd53f4764e24ec9b82f3c28`, [CI 40306685748](https://github.com/shulda/lean_eppa_reducts/actions/runs/40306685748)):** `TwoGraphs/CanonicalAmbientTransport.lean` constructs one ambient automorphism extending the selected representative-to-subset isomorphism for each induced subset, and proves its forward and inverse actions on embedded old vertices. Build and allowed-axiom audit passed. Coherentisation itself remains open.

- [x] **2026-10-26 (certified at commit `6ec966220a0c5e80cb16abb0df5e952e72ef1a5a`, [CI 40304896219](https://github.com/shulda/lean_eppa_reducts/actions/runs/40304896219)):** `TwoGraphs/CanonicalSubsetTransport.lean` proves induced subset isomorphism to a chosen canonical representative and chooses actual literal `HumanTargets.PartialBijection` transporters preserving A. Source and target of a literal partial automorphism have the same canonical representative. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `eff1100b95bc0e536c19b6e338899f07344df550`, [CI 40304367669](https://github.com/shulda/lean_eppa_reducts/actions/runs/40304367669)):** `TwoGraphs/InducedSubsetIsomorphism.lean` proves the reflexive, symmetric and transitive equivalence of induced two-graph isomorphism on Finset subsets and constructs its quotient and equal chosen representatives for isomorphic subsets. Build and allowed-axiom audit passed. The quotient representative was not yet equipped with an actual chosen isomorphism.

- [x] **2026-10-26 (certified at commit `3dbe2fefc104b4d0b2be702358c23ad3f22802ea`, [CI 40302965978](https://github.com/shulda/lean_eppa_reducts/actions/runs/40302965978)):** `TwoGraphs/FiniteValuationEPPA.lean` proves `allFiniteTwoGraphsHaveOrdinaryEPPA`: **every** finite two-graph, including empty input, has a single finite induced valuation witness extending every literal HumanTargets partial automorphism. The exact theorem compiled and passed allowed-axiom audit. **Coherent EPPA is still open.**

- [x] **2026-10-26 (certified at commit `ce588a7cfe870b7019b92867ba2396cba00fda24`, [CI 40301998410](https://github.com/shulda/lean_eppa_reducts/actions/runs/40301998410)):** `TwoGraphs/PartialAutomorphismExtension.lean` proves `exists_valuationTwoGraph_extension_of_partial`, genuine ordinary extension of **every** literal `HumanTargets.PartialBijection` preserving any induced input A in C_X, including empty domain. Build and allowed-axiom audit passed. Coherent selection of extensions remains open.

- [x] **2026-10-26 (certified at commit `a463d486031bf0ca4e2707bdc521a90e46d2018b`, [CI 40301547740](https://github.com/shulda/lean_eppa_reducts/actions/runs/40301547740)):** `TwoGraphs/IndexedTransversalExtension.lean` proves `imageSubtypeEquiv` and `exists_twoGraphAutomorphism_extending_indexedTransversalIso`: an induced isomorphism between any two finite injected D-indexed transversals in the actual valuation two-graph extends to an automorphism of the entire witness. Build and allowed-axiom audit passed. The ordinary EPPA bridge to arbitrary literal partial bijections remains a separate obligation.

- [x] **2026-10-26 (certified at commit `dc86581351d5daa83120e82688ab20fcd53b04ec`, [CI 40296886260](https://github.com/shulda/lean_eppa_reducts/actions/runs/40296886260)):** `TwoGraphs/InducedSubtypeSection.lean` proves `exists_inducedSubtype_coherentLift` for every nonempty induced sub-two-graph of original A, provided its size divides |X|. Its automorphism preservation is stated in terms of the literal original `HumanTargets.TwoGraph`, and its extensions are simultaneous genuine two-graph automorphisms satisfying identity and composition. Build and allowed-axiom audit passed. This is not yet coherent EPPA for A.

- [x] **2026-10-26 (certified at commit `e411d75f440cfbca6cd4195ae207a36bfc04c6d3`, [CI 40296415368](https://github.com/shulda/lean_eppa_reducts/actions/runs/40296415368)):** `TwoGraphs/EmbeddedSubtypePreservation.lean` proves `preservesEmbeddedTransversal_of_inducedSubtype`, transferring the exact original `HumanTargets.TwoGraph` preservation of induced substructure automorphisms into the valuation-transversal preservation predicate. Build and allowed-axiom audit passed. No simultaneous lift is constructed in this lemma.

- [x] **2026-10-26 (certified at commit `2f1c40ce2252aa13bf5071b85a9e8d8a50797e3c`, [CI 40295959770](https://github.com/shulda/lean_eppa_reducts/actions/runs/40295959770)):** `TwoGraphs/FactorialRootedWitness.lean` proves `exists_factorialRootedTransversal`: on X = Fin(|V|!) it packages one **induced** input-two-graph transversal and the divisibility of every nonempty induced subset cardinality by |X|. Build and allowed-axiom audit passed. This is a candidate witness carrier, not yet EPPA or coherent EPPA.

- [x] **2026-10-26 (certified at commit `48eb7d4627d5a981dd2a48cbe2639f6b2b97d2ca`, [CI 40295535515](https://github.com/shulda/lean_eppa_reducts/actions/runs/40295535515)):** `TwoGraphs/FiniteCommonIndex.lean` constructs `factorialIndexEmbedding : V ↪ Fin(|V|!)` for every finite V, and proves `card_nonempty_subtype_dvd_index` for every nonempty induced subset. Build and allowed-axiom audit passed. This is a larger common multiple than the manuscript's LCM, not a weakening of the approved existential EPPA target.

- [x] **2026-10-26 (certified at commit `1d78c1c3c2c9e6a2f9dd3784cbb85468f6291717`, [CI 40294614407](https://github.com/shulda/lean_eppa_reducts/actions/runs/40294614407)):** `TwoGraphs/IndexedRootedTransversal.lean` proves `exists_indexed_rootedTransversal` for any nonempty finite input A, finite X, any prescribed injection `V ↪ X` with `|V| ∣ |X|`. It constructs X-valuations and an **induced** embedding of A into `valuationTwoGraph X` using the prior rooted representation and induced block inflation. Exact HumanTargets API; build and allowed-axiom audit passed. Ordinary EPPA transfer, global common multiple and final coherentisation remain open.

- [x] **2026-10-26 (certified at commit `8ee2c507bc026434ecad60295a1c84e5e66a65d5`, [CI 40294152256](https://github.com/shulda/lean_eppa_reducts/actions/runs/40294152256)):** `TwoGraphs/FiniteRootedTransversal.lean` proves existence of the induced valuation-transversal embedding into C_V for any nonempty finite two-graph with no order supplied, using `finiteCarrierLinearOrder` transported from Fin(card V). Build and allowed-axiom audit passed. Empty input and larger divisible index sets remain open.

- [x] **2026-10-26 (certified at commit `64b6278ee293ea9629e346e2faca98fcada7cc85`, [CI 40293773884](https://github.com/shulda/lean_eppa_reducts/actions/runs/40293773884)):** `TwoGraphs/RootedTransversalEmbedding.lean` proves `orderedRootTransversalEmbedding_induced` in the exact approved `HumanTargets.IsInducedTwoGraphEmbedding` API for *every* two-graph with a linear order and any root, including all repeated-vertex cases. Build and allowed-axiom audit passed. It is not yet a theorem for arbitrary finite types without an order choice.

- [x] **2026-10-26 (certified at commit `2a2fbd185f73d1631ed95c1389db7df14809d4d6`, [CI 40293085365](https://github.com/shulda/lean_eppa_reducts/actions/runs/40293085365)):** `TwoGraphs/OrderedRootValuation.lean` proves pairwise XOR encodes every rooted graph edge and raw three-valuation parity equals each original triple on three distinct vertices (`orderedRootValuation_pairXor`, `orderedRootValuation_rawTripleParity`). Build and allowed-axiom audit passed. It still assumes a chosen linear order and has not yet established a literal induced embedding into the quotient witness.

- [x] **2026-10-26 (certified at commit `5c392f5947eeff306e1e96a35ccbb312018bdee9`, [CI 40292640982](https://github.com/shulda/lean_eppa_reducts/actions/runs/40292640982)):** `TwoGraphs/RootedGraphRepresentative.lean` proves `rootedGraph_adj_iff_triple`, `rootedGraph_edgeBit_eq_rootTriple`, and `rootedGraph_represents_twoGraph`: for every input two-graph and every root, the constructed *actual* Mathlib SimpleGraph has odd-edge triangles exactly the original distinguished genuine triples. Build and allowed-axiom audit passed. No restriction on input cardinality.

- [x] **2026-10-26 (certified at commit `9ed631e3d654364c5b1a81b06fc23d0afc5009df`, [CI 40291856070](https://github.com/shulda/lean_eppa_reducts/actions/runs/40291856070)):** `TwoGraphs/RootedParityAll.lean` proves `twoGraph_triple_false_of_repeat` and `twoGraph_rootedParity_distinct` for *any* original two-graph and every distinct triple, including root-containing cases. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `8af640dd7a0d590487439a1f61fd2e848dc7a606`, [CI 40291028390](https://github.com/shulda/lean_eppa_reducts/actions/runs/40291028390)):** `TwoGraphs/RootedParityAway.lean` proves `twoGraph_rootedParity_away`: the exact original two-graph relation of a triple disjoint from its root equals the XOR of its three rooted pair contributions. Built and allowed-axiom audited. Root-containing/degenerate triples were still open.

- [x] **2026-10-26 (certified at commit `2ff9ff4ac996e5fe2e29ea8405c6575b8f6a5188`, [CI 40290595056](https://github.com/shulda/lean_eppa_reducts/actions/runs/40290595056)):** `TwoGraphs/TwoGraphFourPointXor.lean` proves `twoGraph_fourPointXor` for an arbitrary actual `HumanTargets.TwoGraph` on four distinct vertices, directly from the original four-point even `Finset`-cardinality axiom. Build and allowed-axiom audit passed. Rooted reconstruction and final coherent EPPA are not yet proved.

- [x] **2026-10-26 (certified at commit `5a1b3843634d94b9b516569bb0d3ec696c181fac`, [CI 40288311026](https://github.com/shulda/lean_eppa_reducts/actions/runs/40288311026)):** `TwoGraphs/DivisibleTransversalSection.lean` proves `exists_divisibleTransversal_coherentLift`: for every finite nonempty `D ↪ X` with `|D| ∣ |X|` and every chosen valuation transversal, there exists a simultaneous choice of *actual* two-graph automorphisms extending all its induced automorphisms, preserving identity and composition. The block decomposition and conjugator are fixed independently of the group elements. Build and allowed-axiom audit passed. **This does not yet prove the author's full coherent EPPA theorem**: abstract coherentisation, arbitrary two-graph representation and final theorem bridges remain open.

- [x] **2026-10-26 (certified at commit `9e38bee989a839f041c8b3a22658fe6a229eca92`, [CI 40287552542](https://github.com/shulda/lean_eppa_reducts/actions/runs/40287552542)):** `TwoGraphs/ConjugatedTransversalLift.lean` defines `conjugatedMarkedLift` with a single fixed ambient conjugator and proves the lifted permutations are genuine two-graph automorphisms, map every original marked transversal vertex as prescribed, send identity to identity and preserve composition. Build and allowed-axiom audit passed. The final coherent EPPA theorem remains open.

- [x] **2026-10-26 (certified at commit `d6044410ac4fb8242b8599bbaba48208aba5006e`, [CI 40287066572](https://github.com/shulda/lean_eppa_reducts/actions/runs/40287066572)):** `TwoGraphs/TransversalConjugator.lean` proves `exists_conjugatingAutomorphism`: a single genuine ambient automorphism of `C_X` maps the inflated restricted marked D-transversal to its original chosen X-valuations. Build and allowed-axiom audit passed. No conjugated homomorphism was yet defined.

- [x] **2026-10-26 (certified at commit `e18a08f7bd7430c38dc2403b2edf60407c1a01f7`, [CI 40286299025](https://github.com/shulda/lean_eppa_reducts/actions/runs/40286299025)):** `TwoGraphs/RestrictedTransversal.lean` proves `rawTripleParity_restrict`, `quotientTripleParity_restrict`, `restrictedTransversal_parity`, and `BlockCoordinates.restrictedTransversal_induced_iso`: induced two-graph structures coincide on the restricted full transversal and original transversal. Build and allowed-axiom audit passed.

- [x] **2026-10-26 (certified at commit `8e7ddef1d83802a6ec2b1ad09d37ade508da0e23`, [CI 40285640129](https://github.com/shulda/lean_eppa_reducts/actions/runs/40285640129)):** `TwoGraphs/FullTransversalBlockLift.lean` constructs faithful-class canonical lifts and `BlockCoordinates.inflatedCanonicalFullTransversalLift`, proves the lifted permutations are genuine `HumanTargets` two-graph automorphisms, map the identity to the identity, respect composition and act as prescribed on the distinguished inflated full transversal. Build and allowed-axiom audit passed. This is a homomorphic lift **only for the marked inflated transversal**. Conjugation to arbitrary embedded transversals and final coherent EPPA remain open.

- [x] **2026-10-26 (certified at commit `e4acfe289fff73d60705d6435b8f16fbdefe5964`, [CI 40285183039](https://github.com/shulda/lean_eppa_reducts/actions/runs/40285183039)):** `TwoGraphs/CombinedBlockActionLaws.lean` proves `inflateCombinedActionClass_identity` and `inflateCombinedActionClass_trans`, the faithful quotient-action identity and composition laws for block inflation. Build and allowed-axiom audit passed. This is the algebraic homomorphism property, not the final subgroup section.

- [x] **2026-10-26 (certified at commit `6535d02a57bea9f2ba7a4b99dc500cf557e09d03`, [CI 40284794636](https://github.com/shulda/lean_eppa_reducts/actions/runs/40284794636)):** `TwoGraphs/CombinedBlockAction.lean` builds the faithful combined-action quotient and proves `inflateActionData_wellDefined`, `inflateCombinedActionClass`, and quotient-level `inflateValuationVertex_combinedActionClass`. Build and allowed-axiom audit passed. Identity/composition and the subgroup lift still open.

- [x] **2026-10-26 (certified at commit `0abc0728f75719e347985e9e1e8a9225af0d8d1d`, [CI 40283977872](https://github.com/shulda/lean_eppa_reducts/actions/runs/40283977872)):** `TwoGraphs/BlockEquivariance.lean` proves `inflateValuationClass_reindex`, `inflateValuationClass_shiftValuationByRow`, and `BlockCoordinates.inflateValuationVertex_matrixIndexPerm`, the exact combined-action intertwining relation for an induced block embedding. Build and allowed-axiom audit passed. Subgroup lift/coherent EPPA remain open.

- [x] **2026-10-26 (certified at commit `330839fe26bd44cc0d091f4b93bb49566d6e57b7`, [CI 40281652774](https://github.com/shulda/lean_eppa_reducts/actions/runs/40281652774)):** `TwoGraphs/ValuationBlockInflation.lean` proves quotient valuation inflation along the block retraction is injective, and the resulting map `C_D ↪ C_X` is an **induced two-graph embedding** in the exact approved `HumanTargets` API. Build and allowed-axiom audit passed; action equivariance was still open.


- [x] **2026-10-26 (certified at commit `a4b137f059ef465b91bf7ee73393d6a38963cdb7`, [CI 40281026541](https://github.com/shulda/lean_eppa_reducts/actions/runs/40281026541)):** `TwoGraphs/BlockDivisibility.lean` proves existence of a marked product block system from an arbitrary finite injection `D ↪ X`, nonempty D and `|D| ∣ |X|`. It exports an equivariant retraction and homomorphic permutation lift. Build and allowed-axiom audit passed (418 declarations). Valuation inflation was still outstanding at that commit.


- [x] **2026-10-26 (certified at commit `c5879b3be4907c4de9901b14134868597a273d74`, [CI 40280464187](https://github.com/shulda/lean_eppa_reducts/actions/runs/40280464187)):** `TwoGraphs/BlockCoordinates.lean` defines marked product blocks `D × I ≃ X`, gives the projection, marked embedding and blockwise permutation action, proves its identity/composition/equivariance and compatible matrix inflation. Build and allowed-axiom audit passed (415 declarations). Existence from cardinal divisibility was still open at that commit.


- [x] **2026-10-26 (certified at commit `a5fc8fdabce133a93a57a63658341e26a7bc339b`, [CI 40279715886](https://github.com/shulda/lean_eppa_reducts/actions/runs/40279715886)):** `TwoGraphs/MatrixBlockInflation.lean` proves pullback of symmetric matrices preserves symmetry, XOR and global-constant kernel, with the exact semidirect formula under an equivariant block projection. Build and allowed-axiom audit passed (385 declarations). The requisite finite block system remains to be constructed.


- [x] **2026-10-26 (certified at commit `1f88ed4aaafef4ba119dd57539e5d7c8600b27b7`, [CI 40279161645](https://github.com/shulda/lean_eppa_reducts/actions/runs/40279161645)):** `TwoGraphs/FullTransversalCoherentLift.lean` proves the unique canonical full-transversal combined-action extension respects identity and composition, using the semidirect action law and full-transversal uniqueness. Build and allowed-axiom audit passed (379 declarations). This is a coherent **group section for the full transversal**, not the final coherent EPPA theorem.


- [x] **2026-10-26 (certified at commit `87b3b81441789dae99022b514c3528b0a3156605`, [CI 40278695493](https://github.com/shulda/lean_eppa_reducts/actions/runs/40278695493)):** `TwoGraphs/FullTransversalLift.lean` defines the full-transversal preservation predicate, proves closure under composition, and obtains an **exists-unique combined-action permutation lift** from technical EPPA plus full-transversal uniqueness. Build and allowed-axiom audit passed (369 declarations). The subgroup homomorphism and coherent EPPA remain open.


- [x] **2026-10-26 (certified at commit `f1ba16bc3db7ab8f84730cde3f7a775b19547b1f`, [CI 40278168134](https://github.com/shulda/lean_eppa_reducts/actions/runs/40278168134)):** `TwoGraphs/FullTransversalUniqueness.lean` proves that equality of a combined action on one valuation-class point in every fibre determines the entire permutation, without finiteness or matrix symmetry. Build and allowed-axiom audit passed (364 declarations). This is uniqueness only in the combined-action image, not among arbitrary ambient automorphisms.


- [x] **2026-10-26 (certified at commit `f56cb8cb5d06535e7630f79344fe4bd6070c35b4`, [CI 40273840188](https://github.com/shulda/lean_eppa_reducts/actions/runs/40273840188)):** `TwoGraphs/TransversalCoordinateExtension.lean` proves `exists_twoGraphAutomorphism_extending_any_transversal_embedding`, the technical extension theorem for **all** finite valuation transversals, including arbitrary injective target-coordinate maps and empty source. Build and allowed-axiom audit passed (359 declarations). This is not full coherent EPPA.


- [x] **2026-10-26 (certified at commit `00ef965f9b14df353f80503cec08667fb1b48727`, [CI 40273552991](https://github.com/shulda/lean_eppa_reducts/actions/runs/40273552991)):** `TwoGraphs/TransversalCoordinateExtension.lean` combines Mathlib `Equiv.Perm.exists_extending_pair` with the cut/matrix construction to prove that every induced isomorphism between nonempty valuation two-graph transversals extends to an automorphism, with arbitrary injective target projections. Build and allowed-axiom audit passed (358 declarations). Empty case, arbitrary input representation, full-transversal uniqueness, homomorphic sections and coherence remained open at that commit.


- [x] **2026-10-26 (certified at commit `8ff3ed8ec95b83c8b77499d487796bf8c3cd5d3b`, [CI 40273211410](https://github.com/shulda/lean_eppa_reducts/actions/runs/40273211410)):** `TwoGraphs/TransversalLiteralExtension.lean` bridges literal `HumanTargets.TwoGraph.isTriple` preservation to raw parity and proves genuine automorphism extension of nonempty transversals for a given ambient index permutation σ. Build and allowed-axiom audit passed (355 declarations). Arbitrary injective target-coordinate maps and empty s remain open.


- [x] **2026-10-26 (certified at commit `1a5948d17c7fd8a8235fe1135f6890b820399580`, [CI 40272857743](https://github.com/shulda/lean_eppa_reducts/actions/runs/40272857743)):** `TwoGraphs/TransversalMatrixAction.lean` proves matrix row prescriptions implement the exact target quotient valuation classes and yields symmetric matrix actions extending every nonempty raw parity-preserving transversal. Build and allowed-axiom audit passed (349 declarations). The literal two-graph interface, coordinate-injection extension, and empty case remained open.


- [x] **2026-10-26 (certified at commit `037d4fe1138cefa4052143b4adbbeb2aee6c297a`, [CI 40272099343](https://github.com/shulda/lean_eppa_reducts/actions/runs/40272099343)):** `TwoGraphs/TransversalMatrixAssembly.lean` constructs a globally symmetric Boolean matrix with prescribed rows on a finite transversal, fills the complementary block with zero and derives the row conditions from raw triple-parity preservation. Build and allowed-axiom audit passed (345 declarations). Actual image-mapping on quotient valuation vertices remained open at that commit.


- [x] **2026-10-26 (certified at commit `c1f6536ceb2d362b5cfd2b55bacc1c3fff1840d5`, [CI 40271743338](https://github.com/shulda/lean_eppa_reducts/actions/runs/40271743338)):** `TwoGraphs/TransversalRowPrescription.lean` proves the exact six-bit consistency of matrix row prescriptions from a cut potential, including the diagonal cases. Build and allowed-axiom audit passed (339 declarations); full symmetric extension still open at this commit.


- [x] **2026-10-26 (certified at commit `197b9afa0b187cc813d1eea5f3d5ba8135226631`, [CI 40271418117](https://github.com/shulda/lean_eppa_reducts/actions/runs/40271418117)):** `TwoGraphs/TransversalDiscrepancy.lean` proves that equality of source/target raw triple parity implies the pair-discrepancy triangle cocycle condition and a cut potential on nonempty domains. Build and allowed-axiom audit passed (335 declarations). Matrix extension and bridge to literal partial isomorphisms remain open.


- [x] **2026-10-26 (certified at commit `cb6c466af6d6ac8dee17b6ab1600d2d8fbe09c71`, [CI 40271131368](https://github.com/shulda/lean_eppa_reducts/actions/runs/40271131368)):** `TwoGraphs/CutPotential.lean` proves the Boolean triangle-cocycle/cut-potential equivalence on nonempty types, without finiteness. Build and allowed-axiom audit passed (329 declarations). Actual transversal extension still open.


- [x] **2026-10-26 (certified at commit `26a2390b94a203eb35b6e9f394be78e4dc575846`, [CI 40269800789](https://github.com/shulda/lean_eppa_reducts/actions/runs/40269800789)):** `TwoGraphs/CombinedKernel.lean` proves `matrixIndexPerm_eq_iff`: for nonempty X, equality of the combined actions of two symmetric matrices implies and is implied by equality of their index permutations and global constant XOR of the matrices. Also proves index-coordinate uniqueness and cancellation. Build and allowed-axiom audit passed (325 declarations). Transversal EPPA, subgroup section and coherence are still open.


- [x] **2026-10-26 (certified at commit `a0206e5f3441ecb9c015de51793fefc10a68e67d`, [CI 40269508547](https://github.com/shulda/lean_eppa_reducts/actions/runs/40269508547)):** `TwoGraphs/MatrixQuotient.lean` constructs the quotient of symmetric matrices by equality of induced permutations, proves the quotient action faithful, and proves that equality of classes means XOR by *one global constant matrix*, for nonempty X. Build and allowed-axiom audit passed (322 declarations). Group multiplication on quotient and coherent EPPA remain open.


- [x] **2026-10-26 (certified at commit `01539cc8fdd0787c509e27e310347f0a3cf31709`, [CI 40268927655](https://github.com/shulda/lean_eppa_reducts/actions/runs/40268927655)):** `TwoGraphs/MatrixKernelConverse.lean` proves a globally constant XOR acts trivially, and the exact iff characterization of equal symmetric-matrix actions on a nonempty index type. Build and axiom audit passed (297 declarations). Quotient group and coherent EPPA not yet proved.


- [x] **2026-10-26 (certified at commit `eaabbc78cc36b3d2568b4c69e4715c14a7cefa82`, [CI 40268362379](https://github.com/shulda/lean_eppa_reducts/actions/runs/40268362379)):** `TwoGraphs/MatrixKernel.lean` shows equality of row-shift permutations of symmetric Boolean matrices forces their XOR to be a *single globally constant matrix* when X is nonempty. Build and axiom audit passed (293 declarations). Converse and full kernel equivalence remained open at that commit.


- [x] **2026-10-26 (certified at commit `0dd7b6f41869b2697dc1a2ae6352eedfd75c73a8`, [CI 40267808828](https://github.com/shulda/lean_eppa_reducts/actions/runs/40267808828)):** `TwoGraphs/CombinedGroupLaw.lean` proves exact semidirect composition of `matrixIndexPerm` (inverse-reindexed second matrix) and the reverse index/matrix commutation relation. Build and axiom audit passed (289 declarations). This is a group-action law, not EPPA.


- [x] **2026-10-26 (certified at commit `8fe15f8d00d316fcab37eadda8115353bbeaf335`, [CI 40265970399](https://github.com/shulda/lean_eppa_reducts/actions/runs/40265970399)):** `TwoGraphs/CombinedAutomorphism.lean` introduces `matrixIndexPerm σ F`, proves closure of genuine automorphisms under composition and certifies it in the exact human-target API for symmetric F. Full semidirect multiplication, global-matrix kernel, EPPA and coherent sections remained open at this commit.


- [x] **2026-10-26 (certified at commit `cc2c0604657742f43f52c0867d61372c863ccdba`, [CI 40265687883](https://github.com/shulda/lean_eppa_reducts/actions/runs/40265687883)):** `TwoGraphs/IndexMatrixConjugation.lean` proves the conjugation law of row shifts by index reindexing and the index-permutation composition law. Build and allowed-axiom audit passed (283 declarations). Transversal extension and coherence remain open.


- [x] **2026-10-26 (certified at commit `d0fcd12a3d7c7a98408aae0f7dde68edc7efb9e8`, [CI 40265415221](https://github.com/shulda/lean_eppa_reducts/actions/runs/40265415221)):** `TwoGraphs/IndexPermutation.lean` formalizes index reindexing on valuations/quotients, actual bijections of the witness carrier, and preservation of the exact `HumanTargets.TwoGraph`. Build and allowed-axiom audit passed (273 declarations). The semidirect matrix/index composition law is still to be formalized.


- [x] **2026-10-26 (certified at commit `7057a602eb78ee8431d2e9bcb21818cc2e7aadaa`, [CI 40265098263](https://github.com/shulda/lean_eppa_reducts/actions/runs/40265098263)):** the technical `valuationTwoGraph` constructor accepts explicit `[DecidableEq (ValuationVertex X)]` so the Finset representation in automorphism proofs agrees definitionally. **The author-approved `HumanTargets` API was not modified.** Build and axiom audit passed (256 declarations).


- [x] **2026-10-26 (certified at commit `7057a602eb78ee8431d2e9bcb21818cc2e7aadaa`, [CI 40265098263](https://github.com/shulda/lean_eppa_reducts/actions/runs/40265098263)):** `TwoGraphs/MatrixAutomorphism.lean` proves `valuationTwoGraph_automorphism_of_ternary` and `rowShiftPerm_isTwoGraphAutomorphism` in the exact approved `HumanTargets` interface. Still no EPPA or coherence. Build and axiom audit passed (256 declarations).


- [x] **2026-10-26 (certified at commit `4f9b8eefb4ffdbf56f1d9a71d6e1968c256e3002`, [CI 40264126517](https://github.com/shulda/lean_eppa_reducts/actions/runs/40264126517)):** `TwoGraphs/AnyTripleParity.lean` proves the unordered triple predicate equals its labelled ternary formula for all triples, including repeated vertices. Build and allowed-axiom audit passed (255 declarations).


- [x] **2026-10-26 (certified at commit `4875844ad2e471ceb6c057345bda8e78451a6393`, [CI 40263358263](https://github.com/shulda/lean_eppa_reducts/actions/runs/40263358263)):** `TwoGraphs/MatrixXor.lean` proves closure of symmetric Boolean matrices under XOR, composition of raw/quotient/vertex shifts, permutation composition, and identity. Build and allowed-axiom audit passed (252 declarations). This is the matrix subgroup law, not the full permutation-plus-matrix action or coherent EPPA.


- [x] **2026-10-25 (certified at commit `3be6b8846c0d09ffdc2cef7f95043e8fa9c415ae`, [CI 40225502440](https://github.com/shulda/lean_eppa_reducts/actions/runs/40225502440)):** `TwoGraphs/QuotientRowShift.lean` descends row shifts to `ValuationClass`, proves involutivity, constructs an actual `Equiv.Perm` of valuation vertices and establishes ternary relation preservation for symmetric matrices. Build and allowed-axiom audit passed (241 declarations). No full matrix-permutation group, extension lemma or coherent EPPA yet.


- [x] **2026-10-25 (certified at commit `b94335ae0af34cbba47b7d2913011c7658792e02`, [CI 40225195233](https://github.com/shulda/lean_eppa_reducts/actions/runs/40225195233)):** `TwoGraphs/SymmetricRowShift.lean` proves `rawTripleParity_symmetricRowShift` for every symmetric Boolean matrix and all triples, even repeated first coordinates. Build and allowed-axiom audit passed (231 declarations). Still missing quotient action and group law.


- [x] **2026-10-25 (certified at commit `bc97bda4a162044af05cb322c130c6c7d091067e`, [CI 40224704175](https://github.com/shulda/lean_eppa_reducts/actions/runs/40224704175)):** `TwoGraphs/ValuationTwoGraph.lean` constructs an actual `HumanTargets.TwoGraph` on `X × ValuationClass X` with the **literal** four-point filtered-powerset parity theorem `unorderedTripleParity_fourPointEven`. Build and allowed-axiom audit passed (225 declarations). The output is constrained to `X : Type` to match the approved `HumanTargets.TwoGraph` universe. **No EPPA or coherence property follows yet.**


- [x] **2026-10-25 (certified at commit `fbfb49f7f25c4e28b2784a28df0c26ed72557ae8`, [CI 40224271063](https://github.com/shulda/lean_eppa_reducts/actions/runs/40224271063)):** `TwoGraphs/FourTripleDistinct.lean` supplies the six explicit pairwise inequalities between the four three-element subsets of a four-element set, needed to apply the generic certified `four_filter_even_iff_xor` lemma. Build and allowed-axiom audit passed (217 declarations).


- [x] **2026-10-25 (certified at commit `f815bfda62ad031bc291c6189feee7b806fddc73`, [CI 40224043914](https://github.com/shulda/lean_eppa_reducts/actions/runs/40224043914)):** `TwoGraphs/UnorderedTripleRelation.lean` defines Boolean parity on arbitrary finite subsets, false unless cardinality three, and proves agreement with ordered ternary parity for distinct vertices. Build and allowed-axiom audit passed (215 declarations). Four-point filter-cardinality parity and packaging as the approved `HumanTargets.TwoGraph` remain open.


- [x] **2026-10-25 (certified at commit `5583953a4c4d7ec0dbdde90dbb13cf4872a41d75`, [CI 40223742183](https://github.com/shulda/lean_eppa_reducts/actions/runs/40223742183)):** `TwoGraphs/UnorderedTriplePermutation.lean` proves valuation triple parity is independent of the enumeration of the same three-element Finset, using adjacent-swap formulas and all six permutations. Build and allowed-axiom audit passed (207 declarations). It prepares the actual unordered triple predicate.


- [x] **2026-10-25 (certified at commit `f33611d4d7cd3dd93cb03369cd250e14e6bc524b`, [CI 40223338045](https://github.com/shulda/lean_eppa_reducts/actions/runs/40223338045)):** `TwoGraphs/FourBoolCount.lean` proves the combinatorial equivalence between even cardinality of a filtered four-element set and the XOR of its four Boolean indicators. Build and allowed-axiom audit passed (189 declarations). The complete `HumanTargets.TwoGraph` bridge still awaits the unordered-triple reconstruction.


- [x] **2026-10-25 (certified at commit `94911f08c10eeb529bbfa07f1acad867e4788d95`, [CI 40222685342](https://github.com/shulda/lean_eppa_reducts/actions/runs/40222685342)):** `TwoGraphs/FourSubsetEnumeration.lean` explicitly enumerates the four unordered three-element subsets of a four-element Finset, via powersetCard insert recursion. Build and allowed-axiom audit passed (188 declarations). This will be used to convert the fourpoint XOR formula to the exact accepted `HumanTargets.TwoGraph.fourPointEven` condition.


- [x] **2026-10-25 (certified at commit `1d696ca5e33d51141cecf6ecb0701bd5beeb784e`, [CI 40221574696](https://github.com/shulda/lean_eppa_reducts/actions/runs/40221574696)):** `TwoGraphs/ValuationTernaryExtras.lean` proves zero parity for repeated vertices, its last-two variant, and the equivalent Boolean XOR four-point equation. Build and allowed-axiom audit passed (176 declarations). These are needed for the exact `Finset`-based two-graph bridge.


- [x] **2026-10-25 (certified at commit `7dfc552c5f2159910585e3ff45c8b791b6d12645`, [CI 40221320611](https://github.com/shulda/lean_eppa_reducts/actions/runs/40221320611)):** `TwoGraphs/ValuationVertex.lean` adds concrete `ValuationVertex X = X × ValuationClass X`, labelled triple parity, symmetry, unrestricted four-point F₂ cancellation, and finite-carrier instances. Build and allowed-axiom audit passed (171 declarations). **Not** yet the unordered Finset two-graph or the main theorem.


- [x] **2026-10-25 (certified at commit `3e0980ab0ebef84814ca7b3e8eb01ccb58b3bb23`, [CI 40219483658](https://github.com/shulda/lean_eppa_reducts/actions/runs/40219483658)):** `TwoGraphs/QuotientFourPointParity.lean` proves `quotientFourPointParityModTwo` for four genuine quotient-valuation vertices, including repeated first coordinates. Build and allowed-axiom audit passed (164 declarations). This **does not yet** construct the unordered `Finset`-based `HumanTargets.TwoGraph` nor prove full coherent EPPA.


- [x] **2026-10-25 (certified at commit `71a8367b6b089003cd26b3b5f444bcc437084b56`, [CI 40219044633](https://github.com/shulda/lean_eppa_reducts/actions/runs/40219044633)):** `TwoGraphs/RawFourPointParity.lean` converts the Boolean XOR formula to ZMod 2 and proves the full four-point cancellation of the raw valuation triple parity without assumptions on first-coordinate distinctness. Build and axiom audit passed (163 declarations). This is algebraic fourpoint parity; descent to quotient triples and `HumanTargets.TwoGraph.fourPointEven` remained open at that commit.


- [x] **2026-10-25 (certified at commit `c984a164773939cdccd74f724158420f3e3e2379`, [CI 40218584301](https://github.com/shulda/lean_eppa_reducts/actions/runs/40218584301)):** two adjacent-swap invariances of raw and quotient triple-parity expressions, plus a simp bridge `quotientTripleParity_mk` back to arbitrary representatives. Build and axiom audit passed (159 declarations). These symmetry lemmas are necessary for an unordered triple relation; four-point parity remained open at that commit.


- [x] **2026-10-25 (certified at commit `31593e3d65f57f2005d791f59835d25e9f152b1c`, [CI 40218290510](https://github.com/shulda/lean_eppa_reducts/actions/runs/40218290510)):** `TwoGraphs/QuotientTripleParity.lean` includes raw representative congruence and a genuine descent by **three nested standard quotient lifts** to three quotient valuations (including repeated projections). Build and axiom audit passed (154 declarations). Permutation invariance, four-point parity and induced witness remain unfinished. The first unverified draft used an unavailable `liftOn₃`; replaced by nested lifts.


- [x] **2026-10-25 (certified at commit `17dabf2cf3c2411188dbaa08ee961601face6920`, [CI 40217669482](https://github.com/shulda/lean_eppa_reducts/actions/runs/40217669482)):** `TwoGraphs/RawTripleParity.lean` encodes the six-entry parity formula and proves invariance when each of the three valuation representatives is independently complemented. This is the key raw well-definedness result; build and axiom audit passed (149 declarations). Actual descent to `ValuationClass` and 4-point parity of the quotient witness remained open at that commit.


- [x] **2026-10-25 (certified at commit `8c6603ff62aef47945e1eb2f8f8bfa0b711d3bc5`, [CI 40217409587](https://github.com/shulda/lean_eppa_reducts/actions/runs/40217409587)):** added `TwoGraphs/ValuationQuotient.lean`: Boolean valuations, pointwise complement involution, genuine setoid and quotient classes, and proved identification of a valuation with its complement. This is the *per-vertex valuation quotient*, not the global symmetric-matrix quotient. Build and axiom audit passed (144 declarations). Quotient triple-parity independence and finiteness remain open.


- [x] **2026-10-25 (certified at commit `fd48daa742d89daf3c4cc3f67fa872b158157190`, [CI 40217104843](https://github.com/shulda/lean_eppa_reducts/actions/runs/40217104843)):** added `TwoGraphs/RootedGraph.lean`: actual mathlib `SimpleGraph` constructed directly from the approved `HumanTargets.TwoGraph`, with proved symmetry, looplessness, root isolation, and exact adjacency/triple equivalence away from the root. Build and axiom audit passed (135 declarations). The four-point parity ⇒ reconstruction of triples not containing the root remains outstanding.


- [x] **2026-10-25 (certified at commit `98a243de45ba6f2020493303577fc4c91927f3ba`, [CI 40216584518](https://github.com/shulda/lean_eppa_reducts/actions/runs/40216584518)):** added `fixedVertices_card_lt` to turn the no-fixed-r-subset statement into the exact numerical bound `|Fix(g)| < r`, used in the coset orbit theorem. Build and axiom audit passed (122 declarations). No coset proof yet.


- [x] **2026-10-25 (certified at commit `d61fb2af127cb963236d1a828ff2a4d2249e261c`, [CI 40216102399](https://github.com/shulda/lean_eppa_reducts/actions/runs/40216102399)):** new `BoundedEquivalence/ClassShiftFixed.lean` defines permutation transport of unordered `r`-subsets and proves `no_fixed_rSubset_of_class_shift`, the load-bearing fact that an automorphism with fixed-point-free induced class permutation cannot fix any entire `r`-subset. Build and axiom audit passed (121 declarations). Does **not** yet prove the coset-orbit bound or non-EPPA.


- [x] **2026-10-25 (certified at commit `727de4716599e8f8312852df0c1ac6733194ff9d`, [CI 40214730690](https://github.com/shulda/lean_eppa_reducts/actions/runs/40214730690)):** `all_extension_classes_meet_core` and `unique_extend_labels_of_bounded_classes` (Fin m) prove the finite at-most-m class-counting bridge and unique canonical extension of auxiliary class names to any candidate witness. Build and allowed-axiom audit passed (117 declarations). A missing `Finite (Fin m)` import caused a transient failed build on preceding commit `df9f672...`, then was corrected. **No** negative EPPA contradiction yet.


- [x] **2026-10-25 (certified at commit `019ee3b114c589770a8dc130c3f8aa50795c82a7`, [CI 40214294813](https://github.com/shulda/lean_eppa_reducts/actions/runs/40214294813)):** `BoundedEquivalence/ExtendLabels.lean` now contains `unique_extend_labels_from_core`, a unique extension theorem for auxiliary class names whenever every extension class meets the old core. Build and allowed-axiom audit passed (115 declarations). The finite cardinality/class-surjectivity lemma and the non-EPPA obstruction remained to be proved at that commit.


- [x] **2026-10-25 (certified at commit `2da4dd6d8924df25bf03319e00083e0071842f8c`, [CI 40213966684 attempt 2](https://github.com/shulda/lean_eppa_reducts/actions/runs/40213966684)):** extended `LabelEquiv.lean` with `label_action_id` and `label_action_comp`, proving identity and composition laws for induced permutations of all realized auxiliary class names. Build and allowed-axiom audit passed (114 declarations). Algebraic helper proof only; the coset obstruction is still open. Initial attempt failed due to a transient GitHub DNS lookup during dependency download; unchanged-code rerun passed.


- [x] **2026-10-25 (certified at commit `33e42b55ab1bb516a697bfb10dd773f11e9e8807`, [CI 40213691348](https://github.com/shulda/lean_eppa_reducts/actions/runs/40213691348)):** added `EPPAReducts/TwoGraphs/RootedCocycle.lean` with algebraic cocycle/boundary lemmas. This is the additive backbone of the rooted-graph representation; build and allowed-axiom audit passed (112 declarations). **Not** yet the bridge to the four-point parity definition of `HumanTargets.TwoGraph`.


- [x] **2026-10-25 (certified at commit `c5358ad95e69d1fee5b75aa17d517e6d2ed054ec`, [CI 40213454764](https://github.com/shulda/lean_eppa_reducts/actions/runs/40213454764)):** first genuine Lean proof lemmas in `EPPAReducts/BoundedEquivalence/LabelEquiv.lean`: `unique_label_equiv` and `unique_label_action`, establishing that two surjective labelings of the same unlabelled equivalence differ by a unique label bijection, and that a kernel-preserving permutation induces a unique class permutation. These are preliminary auxiliary statements, **not** EPPA or non-EPPA. Verified: build and axiom audit passed (105 declarations); this is not non-EPPA.


- [x] **2026-10-25:** created public Lean project, Lean and Mathlib `v4.34.1`; pinned `AllThoseEPPA` dependency (matching `lean_eppa_semigeneric`); no LaTeX source published.
- [x] **2026-10-25:** installed GitHub Actions build, Mathlib/toolchain cache, placeholder check, tracked-LaTeX check, and `axiom-audit` with allowlist `propext, Classical.choice, Quot.sound`.
- [x] **2026-10-25:** foundational, **unproved** two-graph parity and bounded-equivalence setoid definitions compile; do not mistake definitions for the two final theorems.
- [x] **2026-10-25:** CI build and axiom audit successful at exact commit `c8c8c6f154e0b313e487040f38601b1d6c8bee89`: [Actions run 40204033942](https://github.com/shulda/lean_eppa_reducts/actions/runs/40204033942). Audit saw only 5 declarations under `EPPAReducts`; no result yet established.
- [x] **2026-10-25:** inspected source proof structure and compared the shared API in `AllThoseEPPA/EPPA.lean` / `PartialIso.lean`. The latter already implements explicit embeddings, partial automorphisms, EPPA, coherent extension, equivalent partial-map representations, and coherent triples.
- [x] **2026-10-25:** first *desk audit* and private expanded formalization-oriented LaTeX manuscript prepared as chat artifact, not pushed. No definitive proof gap identified in either required human proof; several nontrivial omitted details expanded. Ran finite sanity checks for the six-vertex graph gadget and small `C_X` valuation structures/actions (`|X| ≤ 3`). These checks are not proofs.
- [x] **2026-10-25:** independent Lean target module imported by the project root and verified by GitHub Actions at commit `408d9eac51b00189f1d10a71b187296f80596028`: [run 40208174582](https://github.com/shulda/lean_eppa_reducts/actions/runs/40208174582), successful build and allowed-axiom audit (103 declarations). **The targets are only propositions: no proof of either is claimed.**
- [x] **2026-10-25:** prepared private working revision `eppa_reducts_formalization_v1.tex` (15-page compiled proof-audit manuscript), expanding proof-level contracts, edge cases and dependency checks for both target results. **It is private and is NOT in this public repository**; neither main theorem is Lean-proved. The previous `_v0.tex` remains superseded, not certified. Independent adversarial scrutiny remains desirable before freezing the proof plan.
- [x] **2026-10-25:** second adversarial read of both target proof chains completed in private revision `eppa_reducts_formalization_v2.tex` (18 pages, PDF companion; **not on public GitHub**). Checked quantifiers, quotient/matrix action and full-transversal uniqueness, block-group compatibility, abstract coherence, unlabelled class action, normalizer condition, finite orbit divisibility, exterior types, and ordered tuples. No substantive counterexample or missing mathematical hypothesis found; **provisional pre-Lean proof-plan stability gate passed**, subject to reconsideration if Lean exposes a gap. Added optional quantitative lift-fibre audit and a stronger class-action homomorphism contract. Independent finite tests checked 64 full transversals with 2304 composition laws, 64 block-group multiplication laws, several small parameter cases for the negative obstruction, and 264 normalizing cosets in Sym(4). These computations are not proofs, and the main targets remain unproved.
- [x] English human-readable theorem statements approved by the author.
- [x] Added self-contained Lean target propositions `HumanTargets.twoGraphsHaveCoherentEPPA` and `HumanTargets.graphsModuloComplementationFailEPPA` with induced-embedding, partial-isomorphism, extension and coherence definitions; **these are definitions of propositions, not proofs**.
- [x] Self-contained Lean target statement semantics reviewed and approved by the author (2026-10-25).
- [x] Final positive theorem and the exact `HumanTargets.twoGraphsHaveCoherentEPPA` proof certified at `171153ba` / CI 40331155882.
- [ ] General negative theorem (unordered, ordered) proved and audited in Lean.
- [ ] Certified bridge and full theorem for the **negative** human-readable target; the positive HumanTargets bridge is certified.

### GitHub state recovery protocol

On every fresh chat or after a crash:

1. Read **this** file on the actual `main` branch and inspect recent commits.
2. Read the main Lean build root `EPPAReducts.lean` and relevant new files; do not infer completed lemmas from checkbox entries.
3. Check the GitHub Actions run corresponding to the **current HEAD SHA**. Treat only a successful build **and allowed-axiom audit on that SHA** as verified.
4. Reopen the private Project manuscript `eppa_reducts8.tex` whenever a mathematical claim needs checking; use the privately generated expanded proof manuscript if it remains accessible as a user file, otherwise reconstruct privately.
5. Continue the first unchecked dependency; do not switch to `lean_eppa_semigeneric` or `lean_all_those_eppa_classes` except to **read/reuse** APIs.
6. Update this ledger **in the same commit** as every meaningful proof milestone, with Lean declaration names, exact CI SHA and caveats.

## Proof dependency graph (design, not certification)

### Positive: coherent EPPA for two-graphs — certified

- [x] The rooted representative constructs the actual input two-graph and an induced valuation transversal, including the empty input; certified by the rooted/finite-valuation sequence.
- [x] The quotient valuation two-graph and honest matrix/permutation actions are constructed with exact algebraic kernel, extension of all literal partial automorphisms, and finite witness carrier.
- [x] All induced substructures have simultaneous homomorphic sections in one witness, by block inflation for nonempty subsets and the identity section for the empty subset.
- [x] Canonical representatives, fixed ambient transports, normalized partial isomorphisms, and same-section composition assemble the coherent extension `canonicalConjugatedLift`, proved to be an automorphism and to extend the actual partial map.
- [x] The exact full positive target `HumanTargets.twoGraphsHaveCoherentEPPA` is proved by `humanTwoGraphsHaveCoherentEPPA`, with `|X| = |V|!` instead of the manuscript's smaller LCM. The final statement has no size restriction and no weakened coherence hypothesis. CI and allowed-axiom audit passed at `171153ba`.

### Negative: equivalences with boundedly many classes

- [ ] Finite group coset fixed-point lemma: for `L ≤ Sym(Ω)` and `g` normalizing `L`, if each member of `Lg` fixes at most `b` vertices, the union of these fixed points lies in at most `b` `L`-orbits. Can be proved by double-counting / twisted Burnside.
- [ ] Encode `r`-subset equivalence as an **unlabelled setoid** and separately choose auxiliary `Fin m` / `ZMod m` representatives. Verify equivalence of "at most `m` classes" and existence of such a presentation.
- [ ] Translation on `S = ZMod (m*lcm(1,…,r))`: orbit lengths of `r`-subsets and `(r-1)`-subsets divisible by `m`; choose equivariant colourings on orbits.
- [ ] Construct **r pairwise distinct**, translation-equivariant external types. `r=2` separate; for `r≥3` use translation-orbit invariants, e.g., number of cyclically consecutive pairs, with explicit examples.
- [ ] Build finite obstruction with `r` added fixed points. Prove the partial maps are structure isomorphisms, their extensions lie in the same stabilizer coset, that coset permutes all `m` classes without fixed class, and apply the orbit lemma for the contradiction.
- [ ] Ordered injective tuples: translation acts freely on ordered positive-length tuples; put a distinctive shift at each external-vertex position, then repeat the same coset argument.
- [ ] Specialize at `r=m=2` to graph modulo complementation, handling equivalence relations on **unordered pairs** exactly. State the failure for *every* candidate finite extension/witness, not merely a fixed one.

## Interfaces to reuse rather than rebuilding

- `AllThoseEPPA.EPPA`: `Structure.PartialAutomorphism`, `Structure.IsEPPAWitness`, `Structure.IsCoherentEPPAWitness`, `Structure.CoherentExtension`, `Structure.ExtendsAlong`.
- `AllThoseEPPA.PartialIso`: `PartialIsomorphism.Equivalent`, `PartialIsomorphism.CoherentTriple`.
- `AllThoseEPPA.Language`: trivial symbol group action. A relational language may have symbols of arity 3 and (for r-equivalence) `2*r`.
- `lean_eppa_semigeneric` contains a tested **raw-structure to shared typed-EPPA** bridge pattern, but its mathematics is a different problem. Do not import its valuation constructions or claim its coherent EPPA theorems solve two-graphs.
- Reuse Mathlib `Finset`, `ZMod`, `Equiv.Perm`, finite group actions, and quotient API wherever practical.

## Initial desk-audit warnings

- The valuation quotient (one constant complement **per vertex**) and the symmetric-matrix quotient (one global constant matrix) differ. A wrong quotient would invalidate the section/lift.
- Distinguish preservation of **equality** of colours from preservation of the auxiliary colour labels.
- The negative theorem is for **at most** `m` classes; the specifically chosen counterexample will use exactly `m` on a core.
- For the positive theorem, it is not enough to extend individual partial maps; the subgroup lift must be a genuine homomorphism for every induced substructure.
- Build success for `EPPAReducts.lean` certifies only the modules actually imported. Check that every target theorem is included in that build root and audited as a declaration.

## Next concrete actions

**Current certified milestone (2026-10-26):** the complete coherent EPPA theorem for finite two-graphs, including the exact `HumanTargets.twoGraphsHaveCoherentEPPA` proposition, is proved and audited on the work branch at `171153ba` (CI 40331155882). Merge the work branch and verify GitHub Actions on the **new main HEAD**, then do not reopen the positive chain unless an audit reveals a mismatch.

**Main outstanding mathematical target:** prove non-EPPA for unlabelled equivalence relations on unordered `r`-subsets with at most `m` classes for every `r,m≥2`; separately for ordered injective tuples; then specialize to the approved `HumanTargets.graphsModuloComplementationFailEPPA` target. The source relation is a setoid, not a named-colour structure.

**Next negative proof obligations, in order:** (1) twisted fixed-point/coset orbit bound for a normalizing permutation of a finite subgroup; (2) `ZMod` translation orbit divisibility and equivariant auxiliary labelings of subsets; (3) construction of the requisite pairwise distinct external types; (4) the finite unlabelled-class obstruction and its contradiction; (5) ordered tuples and the final exact target bridge. The existing `BoundedEquivalence/LabelEquiv.lean`, `ExtendLabels.lean` and `ClassShiftFixed.lean` are certified preparatory results, **not** the negative theorem.

Continue with small, isolated, audited Lean milestones. Do not publish either unpublished manuscript or internal notes in this public repository. Maintain this ledger and verify both build and allowed-axiom audit on the exact final theorem commit.

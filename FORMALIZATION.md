# Formalization ledger — EPPA for reducts

**Repository:** `shulda/lean_eppa_reducts` (**not** any other EPPA project).
**Source of mathematical claims:** private Project source `eppa_reducts8.tex`; not tracked by Git.
**Confidentiality rule:** never push LaTeX, bibliography, manuscript extracts, or an internal detailed proof manuscript to this public repository before explicit author approval.
**Updated:** 2026-10-26 (full combined action law, kernel and faithful symmetric matrix quotient certified; no EPPA theorem yet).

## Scope and acceptance targets

Only two load-bearing results are intended:

1. Every finite two-graph has **coherent EPPA**. The user-facing formulation quantifies over all isomorphisms between induced substructures and a compositional choice of extensions.
2. For every `r,m ≥ 2`, finite equivalence relations on **unordered r-element subsets** with **at most m equivalence classes** fail EPPA; likewise for **ordered injective r-tuples**. The human-facing final corollary specializes `r=m=2` to graphs **modulo global complementation**.

**Important:** a graph modulo complementation is an unlabelled equivalence relation on unordered pairs with ≤2 classes, **not** a graph that happens to admit a complementing automorphism. A model with `m` named edge colours has the wrong automorphism group and is not the intended target.

The human-readable English formulations were approved by the author on 2026-10-25. The self-contained **Lean** formulations in `EPPAReducts/HumanTargets.lean` were reviewed and approved by the author on 2026-10-25. Their definitions are frozen acceptance targets. The private paper draft may evolve in exposition or proof details; the mathematical targets should remain stable. The expanded **private** mathematical manuscript is now `eppa_reducts_formalization_v2.tex` (18-page PDF), superseding `v1` and `v0`. It is a provisional mathematical proof plan, **not** a Lean-verified theorem or an external referee certification. Do not silently weaken them by restricting carrier size, considering only a chosen graph representative, requiring exactly `m` classes, naming colours, or assuming coherence only for full automorphisms.

Explicitly out of scope: the six-vertex exposition as a separate theorem, the rooting transfer to complementary two-graphs, looped-graph EPPA, and the claimed wider hypergraph reduct classification. These may be optional regression tests or later projects, but they are not part of the requested certification.

## Current verified state

- [ ] **2026-10-26 (CI pending):** `TwoGraphs/TransversalCoordinateExtension.lean` uses Mathlib `Equiv.Perm.exists_extending_pair` to extend any injection from a finite source index subset to a permutation of X, then derives genuine automorphism extension for nonempty transversals with arbitrary injective target projections. Still open: empty s, lifting from the original arbitrary two-graph, full-transversal uniqueness, subgroup homomorphic sections, and coherent EPPA.


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
- [ ] Final positive theorem proved and audited in Lean.
- [ ] General negative theorem (unordered, ordered) proved and audited in Lean.
- [ ] Certified bridges from technical encodings to the two human-readable targets.

### GitHub state recovery protocol

On every fresh chat or after a crash:

1. Read **this** file on the actual `main` branch and inspect recent commits.
2. Read the main Lean build root `EPPAReducts.lean` and relevant new files; do not infer completed lemmas from checkbox entries.
3. Check the GitHub Actions run corresponding to the **current HEAD SHA**. Treat only a successful build **and allowed-axiom audit on that SHA** as verified.
4. Reopen the private Project manuscript `eppa_reducts8.tex` whenever a mathematical claim needs checking; use the privately generated expanded proof manuscript if it remains accessible as a user file, otherwise reconstruct privately.
5. Continue the first unchecked dependency; do not switch to `lean_eppa_semigeneric` or `lean_all_those_eppa_classes` except to **read/reuse** APIs.
6. Update this ledger **in the same commit** as every meaningful proof milestone, with Lean declaration names, exact CI SHA and caveats.

## Proof dependency graph (design, not certification)

### Positive: coherent EPPA for two-graphs

- [ ] Rooted graph representative: the four-point parity axiom reconstructs a graph representative of any nonempty finite two-graph.
- [ ] Quotient valuation space `Q_X`: quotient by constant complement is defined using `Bool`; well-defined labelled triple parity, symmetry, and algebraic four-point cancellation are Lean-proved. Exact unordered-`Finset` two-graph, finiteness, and the literal HumanTargets structure have now been verified (see `ValuationTwoGraph.lean`); matrix actions and EPPA still open.
- [ ] Symmetric matrix action on the valuation witness; quotient by a **single global constant matrix**, transformation composition, and honest automorphisms.
- [ ] For transversal partial isomorphisms, prove the switching/cut identity and extend the projection injection to a permutation; construct a symmetric matrix extension.
- [ ] Uniqueness of the action lift for a transversal covering **all** first coordinates. Carefully handle domains of size 0, 1, or 2.
- [ ] Blockwise permutation/matrix inflation whenever `|D| ∣ |X|`, equivariant valuation embedding, and a homomorphism `Aut(D) → Aut(C_X)` fixing its prescribed action on every induced transversal.
- [ ] Abstract coherentisation lemma (EPPA plus subgroup homomorphic lifts for every induced substructure) and explicit coherent choice.
- [ ] Final witness: `|X| = lcm(1,…,|A|)`, induced transversal embedding, empty case, exact bridge to the shared `AllThoseEPPA.Structure.IsCoherentEPPAWitness` and to approved human statement.

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

**Post-action-kernel checkpoint (2026-10-26):** Positive track now includes an exact `HumanTargets.TwoGraph` built on finite valuation vertices; matrix-row shifts and index reindexing proved genuine automorphisms; matrix XOR laws, semidirect conjugation and the combined action multiplication proved; the symmetric-matrix action quotient proved faithful with kernel **exactly the one global constant matrix** (not independent row complements); and full combined-action kernel proved. All this is compiled and audited on the referenced commits. **No EPPA or coherent EPPA theorem has been proved.**

**Next positive load-bearing work:** formalize the subgroup/group structure on the quotient action if required by the block homomorphism; derive the cut equation for isomorphisms between transversals; extend partial coordinate injections to permutations of finite X; construct the symmetric-matrix extension with all degenerate domain cases; prove uniqueness of full-transversal lifts; block-inflate homomorphically when `|D| ∣ |X|`; then abstract coherentisation and the final LCM/empty-input theorem, including the bridge to both the shared API and approved `HumanTargets.twoGraphsHaveCoherentEPPA`. The original arbitrary-two-graph rooted-representative bridge is still outstanding.

**Next negative load-bearing work:** prove the independent finite coset fixed-point/orbit bound (double-counting) and only then the cyclic-translation colouring obstruction for unlabelled equivalences on r-subsets and ordered injective r-tuples. The existing class-label recovery and fixed-vertex-bound lemmas are already audited; neither general negative EPPA nor its `r=m=2` human-facing corollary is proved.

1. **Private mathematical plan provisionally stable after second audit (v2).** Do not treat this as Lean verification or independent external refereeing. If Lean reveals a genuinely mathematical missing condition, repair the private proof manuscript and update this ledger before accepting the technical theorem.
2. The author approved the standalone Lean target definitions on 2026-10-25. Keep their exact semantics fixed; use separate technical definitions and prove equivalences at the end.
3. When resuming Lean, start with separately provable and auditable elementary positive and negative lemmas in small CI-green commits (rooted graph representation / quotient parity; finite coset-orbit lemma / unlabelled class-action bridge), reusing the upstream `AllThoseEPPA` API. The optional lift-count formula is a regression lemma, **not** a dependency of the principal theorem.
4. Keep both branches in **this one** public Lean repository. Never upload unpublished TeX, proof excerpts or the internal working manuscript without explicit permission.
5. At the end, prove bridges to the two exact readable target declarations; require green CI and axiom audit at the final theorem HEAD.

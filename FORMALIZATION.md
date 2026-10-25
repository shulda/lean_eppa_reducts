# Formalization ledger — EPPA for reducts

**Repository:** `shulda/lean_eppa_reducts` (**not** any other EPPA project).
**Source of mathematical claims:** private Project source `eppa_reducts8.tex`; not tracked by Git.
**Confidentiality rule:** never push LaTeX, bibliography, manuscript extracts, or an internal detailed proof manuscript to this public repository before explicit author approval.
**Updated:** 2026-10-25 (expanding negative obstruction with fixed-vertex lemmas; CI pending).

## Scope and acceptance targets

Only two load-bearing results are intended:

1. Every finite two-graph has **coherent EPPA**. The user-facing formulation quantifies over all isomorphisms between induced substructures and a compositional choice of extensions.
2. For every `r,m ≥ 2`, finite equivalence relations on **unordered r-element subsets** with **at most m equivalence classes** fail EPPA; likewise for **ordered injective r-tuples**. The human-facing final corollary specializes `r=m=2` to graphs **modulo global complementation**.

**Important:** a graph modulo complementation is an unlabelled equivalence relation on unordered pairs with ≤2 classes, **not** a graph that happens to admit a complementing automorphism. A model with `m` named edge colours has the wrong automorphism group and is not the intended target.

The human-readable English formulations were approved by the author on 2026-10-25. The self-contained **Lean** formulations in `EPPAReducts/HumanTargets.lean` were reviewed and approved by the author on 2026-10-25. Their definitions are frozen acceptance targets. The private paper draft may evolve in exposition or proof details; the mathematical targets should remain stable. The expanded **private** mathematical manuscript is now `eppa_reducts_formalization_v2.tex` (18-page PDF), superseding `v1` and `v0`. It is a provisional mathematical proof plan, **not** a Lean-verified theorem or an external referee certification. Do not silently weaken them by restricting carrier size, considering only a chosen graph representative, requiring exactly `m` classes, naming colours, or assuming coherence only for full automorphisms.

Explicitly out of scope: the six-vertex exposition as a separate theorem, the rooting transfer to complementary two-graphs, looped-graph EPPA, and the claimed wider hypergraph reduct classification. These may be optional regression tests or later projects, but they are not part of the requested certification.

## Current verified state

- [ ] **2026-10-25 (CI pending):** two adjacent-swap invariances of raw and quotient triple-parity expressions, plus a simp bridge `quotientTripleParity_mk` back to arbitrary representatives. These symmetry lemmas are necessary for an unordered triple relation; four-point parity remains open.


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
- [ ] Quotient valuation space `Q_X = (X → ZMod 2) / constant-one`; well-defined triple predicate; four-point parity for all vertices, not just transversals.
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

**Post-initial-proof checkpoint:** Main branch has genuine audited auxiliary theorems, but neither principal EPPA theorem. The immediate next positive milestone is the exact bridge from the human-facing finite four-point parity to `TwoGraphs.IsTriangleCocycle`, followed by quotient valuations. The immediate next negative milestone is the independent coset fixed-point orbit bound, then its specialization to the unlabelled Fin m class action. Avoid spending further time on only relabelling infrastructure unless a bridge requires it.


1. **Private mathematical plan provisionally stable after second audit (v2).** Do not treat this as Lean verification or independent external refereeing. If Lean reveals a genuinely mathematical missing condition, repair the private proof manuscript and update this ledger before accepting the technical theorem.
2. The author approved the standalone Lean target definitions on 2026-10-25. Keep their exact semantics fixed; use separate technical definitions and prove equivalences at the end.
3. When resuming Lean, start with separately provable and auditable elementary positive and negative lemmas in small CI-green commits (rooted graph representation / quotient parity; finite coset-orbit lemma / unlabelled class-action bridge), reusing the upstream `AllThoseEPPA` API. The optional lift-count formula is a regression lemma, **not** a dependency of the principal theorem.
4. Keep both branches in **this one** public Lean repository. Never upload unpublished TeX, proof excerpts or the internal working manuscript without explicit permission.
5. At the end, prove bridges to the two exact readable target declarations; require green CI and axiom audit at the final theorem HEAD.

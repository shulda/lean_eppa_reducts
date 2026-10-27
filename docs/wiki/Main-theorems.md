# Main theorems — mathematical statements and exact Lean proofs

The first four results below were already present in the audited `EPPAReducts.lean` import graph at [commit `d12d133a`](https://github.com/shulda/lean_eppa_reducts/commit/d12d133a37d909837c6fbf4c7409f699f2918264).

## 1. Coherent EPPA for finite two-graphs

A **two-graph** is a ternary relation on *unordered* triples such that every four-element set contains an even number of distinguished triples.

**Theorem.** Every finite two-graph $A$ has a finite two-graph $B$, an induced vertex embedding $A\hookrightarrow B$, and a single function sending *every* isomorphism between induced sub-two-graphs of $A$ to an automorphism of $B$. Each chosen automorphism extends the given partial isomorphism, and the choice preserves composable products: if $p:D\to E$ and $q:E\to F$, then $\Phi(q\circ p)=\Phi(q)\circ\Phi(p)$. The theorem includes $A=\varnothing$.

**Certified declaration:** [`EPPAReducts.TwoGraphs.humanTwoGraphsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/TwoGraphs/FiniteCoherentEPPA.lean#L73-L79), of type [`HumanTargets.twoGraphsHaveCoherentEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/HumanTargets.lean).

The `CoherentTwoGraphWitness` contains both the common finite extension and the actual composition law; it is not a family of unrelated extensions.

## 2. Non-EPPA for unordered $r$-subset equivalences

Fix integers $r,m\ge 2$. On the $r$-element subsets of a finite vertex set, consider **one equivalence relation with at most $m$ unnamed classes**. Vertex permutations may exchange classes.

**Theorem.** This class fails ordinary EPPA. There is a particular finite $A$ such that, for **every** finite $B$ and **every induced embedding** of $A$ into $B$, at least one partial automorphism of $A$ cannot be extended to an automorphism of $B$. This is the usual failure of the common EPPA-witness property, not a failure for just one selected ambient extension.

**Certified declaration:** [`EPPAReducts.BoundedEquivalence.allUnorderedBoundedEquivalencesFailEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/BoundedEquivalence/UnorderedNoEPPAWitness.lean#L118-L135), of type [`unorderedBoundedEquivalencesFailEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/BoundedEquivalence/UnorderedGraphTargetBridge.lean).

## 3. Non-EPPA for ordered injective $r$-tuple equivalences

Fix $r,m\ge 2$. The equivalence relation is on ordered injective tuples, not on multisets, unordered subsets or all tuples allowing repetitions. It again has at most $m$ **unlabelled** classes.

**Theorem.** The resulting finite class fails ordinary EPPA, with an explicit finite obstruction and a universal quantifier over every finite induced common EPPA witness.

**Certified declaration:** [`EPPAReducts.BoundedEquivalence.orderedBoundedEquivalencesFailEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/BoundedEquivalence/OrderedNoEPPAWitness.lean#L113-L135).

## 4. Graphs modulo global complementation

A finite graph modulo global complementation is represented by a single equivalence relation on **unordered pairs of distinct vertices** with at most two classes. It does **not** mean a graph admitting some complementing automorphism. Neither edge colour is named, and the whole pair-class partition may be interchanged.

**Theorem.** The class has no EPPA.

**Certified declaration:** [`EPPAReducts.BoundedEquivalence.humanGraphsModuloComplementationFailEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/BoundedEquivalence/UnorderedNoEPPAWitness.lean#L136-L144), of type [`HumanTargets.graphsModuloComplementationFailEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/HumanTargets.lean).

The [arity-two bridge](https://github.com/shulda/lean_eppa_reducts/blob/d12d133a37d909837c6fbf4c7409f699f2918264/EPPAReducts/BoundedEquivalence/UnorderedGraphTargetBridge.lean) establishes exact agreement of induced embeddings, partial automorphisms, full automorphisms and common EPPA witnesses.

### 5. Rooting reduction and two-graphs modulo complementation

A two-graph modulo global complementation is represented by an equivalence relation on **unordered triples**, where the two equivalence classes are **unnamed**, and there exists a four-point-even two-graph indicator whose equality kernel is that equivalence relation. Automorphisms are permitted to exchange the two classes. The definition also admits zero or one realized class; it does not demand two nonempty colours.

**Rooting reduction.** If the class of all finite two-graphs modulo global complementation had ordinary EPPA, then so would the class of all finite graphs modulo global complementation.

**Non-EPPA.** The finite two-graphs modulo global complementation do not have EPPA. In particular one finite structure defeats **every** finite induced EPPA witness, not merely a specific candidate witness.

**Certified declarations (on audited main):**

- [`EPPAReducts.TwoGraphs.graphsModuloHaveEPPA_of_twoGraphsModulo`](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean): the fully quantified implication `TwoGraphsModuloHaveEPPA → GraphsModuloHaveEPPA`.
- [`EPPAReducts.TwoGraphs.twoGraphsModuloNotHaveEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingGlobalTransfer.lean): the negation of the fifth class's EPPA assertion.
- [`EPPAReducts.TwoGraphs.twoGraphsModuloFailEPPA`](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPartialAutomorphism.lean): an explicit finite obstruction with a universal no-witness conclusion.
- [`EPPAReducts.TwoGraphs.allRootedPartialLifts`](https://github.com/shulda/lean_eppa_reducts/blob/3f35830e34938d91fd082c5f9c9ef47b8e371c98/EPPAReducts/TwoGraphs/RootingPartialAutomorphism.lean): every genuine unlabelled pair-class partial automorphism lifts after adding and fixing a new root, with **no unproved hypothesis**.

The relevant [full mathematical and source-facing audit](Rooting-reduction.md) includes empty-domain handling, the parity argument, root fixation, arbitrary ambient witnesses and the unlabelled two-class semantics.

## Distinguish formalized results from the remaining article-level corollaries

All five requested *individual* positive/negative directions except the original-language graph coherent-EPPA positive bridge are certified in the imported development. The complete **five-reduct classification as one standalone Lean theorem** remains an additional integration target. The classical classification of *all first-order reducts* as exactly five classes, due to Thomas, is a separate external mathematical result not asserted here as Lean-checked.

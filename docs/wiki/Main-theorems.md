# Main theorems — mathematical statements and exact Lean proofs

All links here refer to declarations contained in the audited `EPPAReducts.lean` import graph at [commit `d12d133a`](https://github.com/shulda/lean_eppa_reducts/commit/d12d133a37d909837c6fbf4c7409f699f2918264).

## 1. Coherent EPPA for finite two-graphs

A **two-graph** is a ternary relation on *unordered* triples such that every four-element set contains an even number of distinguished triples.

**Theorem.** Every finite two-graph $A$ has a finite two-graph $B$, an induced vertex embedding $A\hookrightarrow B$, and a single function sending *every* isomorphism between induced sub-two-graphs of $A$ to an automorphism of $B$. Each chosen automorphism extends the given partial isomorphism, and the choice preserves composable products: if $p:D\to E$ and $q:E\to F$, then $\Phi$q\circ p$=\Phi$q$\circ\Phi$p$$. The theorem includes $A=\varnothing$.

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

## Distinguish formalized results from the remaining article-level corollaries

The original acceptance targets are all certified. The full **five-reduct classification**, and the **rooting reduction** needed to deduce non-EPPA for two-graphs modulo complementation, are a newly requested scope expansion. A successful build of the four declarations above does *not* yet certify those additional results.

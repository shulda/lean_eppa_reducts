# Proof architecture

This page describes the proof graph behind the **audited baseline**. The development does not substitute an external black-box theorem for either requested result.

## Two-graphs: valuations and coherent lifts

1. Reconstruct a graph representative from the four-point parity of the input two-graph. For a chosen root, triple parity is the XOR of the three rooted pair indicators: [rooted graph representative](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/RootedGraphRepresentative.lean).
2. Construct the finite quotient-valuation two-graph. Distinguish **a valuation modulo its pointwise complement for each vertex** from the **global symmetric-matrix quotient** controlling the automorphism group: [valuation quotient](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/ValuationQuotient.lean), [matrix quotient](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/MatrixQuotient.lean), [valuation two-graph](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/ValuationTwoGraph.lean).
3. Embed the given two-graph as an induced transversal of valuations and extend every literal partial automorphism.
4. Build simultaneous homomorphic sections for automorphism groups of **all** induced subsets. The Lean proof chooses $N=|V|!$, which is divisible by every nonzero induced-subset cardinality. The mathematical manuscript may instead use the smaller $\mathrm{lcm}(1,\ldots,|V|)$; the larger choice does not change the statement.
5. Assemble canonical transports and sections into one choice satisfying exact composition: [canonical coherent lift](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/CanonicalCoherentLiftComposition.lean), [final human target](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/FiniteCoherentEPPA.lean).

## Negative EPPA: finite cyclic obstruction and group theory

1. Choose one finite core with **all $m$** auxiliary colours realized and $r$ distinguishable exterior points.
2. Define $r$ genuine partial automorphisms of this **same** unlabelled equivalence, each cyclically shifting the core while fixing one exterior point. These maps preserve equality of class labels even though they shift the labels.
3. Suppose all extend to full automorphisms of one hypothetical finite witness. Normalize the auxiliary labels of that witness using all the old realized classes. The normalization is justified by the class-count bound.
4. The extensions belong to the same coset of a normalizer of the pointwise core stabilizer. A finite group incidence-counting lemma bounds the number of orbits containing fixed points of that coset.
5. Exterior types are provably inequivalent under the pointwise core stabilizer. With $r$ exteriors and a coset fixed-point bound of $r-1$, a pigeonhole collision yields the contradiction.

The reusable group lemmas are in [`CosetOrbitBound.lean`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/CosetOrbitBound.lean) and [`CosetOrbitCollision.lean`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/CosetOrbitCollision.lean). Ordered and unordered obstructions require different tuple/subset-action bridges; the terminal proofs are [ordered](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/OrderedNoEPPAWitness.lean) and [unordered](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/UnorderedNoEPPAWitness.lean).

## The separately checked rooting reduction

The [exact root class theorem](Rooting-reduction.md) is now proved, rather than treated as a consequence of the group obstruction alone.

The Lean proof constructs a valid four-point-even two-graph from an arbitrary finite graph by adding an isolated root, proves that **every** source partial map lifts to a root-fixing partial map respecting the equality of unnamed triple classes, and restricts **every** hypothetical finite EPPA witness at its root to obtain a witness for the original pair classes. A complete root-shadow automorphism restriction proves that class swaps are correctly preserved. The algebraic ingredient is an audited uniform XOR shift with a vertex gauge in characteristic two.

[Full integrated CI #40517057037](https://github.com/shulda/lean_eppa_reducts/actions/runs/40517057037) certifies the imported modules and all conclusions at main SHA `3f35830e3493`.

The complete five-reduct table and its original-language coherent simple-graph witness have subsequently been proved and audited; the next section records their final exact Lean declarations.

## Completing the five-reduct table

The [exact final conjunction](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/FiveReductEPPA.lean) reuses all audited positive and negative theorems. Finite sets have a simultaneous extension of partial permutations. For **true finite simple graphs**, the pinned `AllThoseEPPA` coherent binary-relational witness is normalized by retaining only mutual off-diagonal edges; the [induced embedding](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrization.lean), [automorphism transport](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrizationAutomorphism.lean) and [coherent transport](https://github.com/shulda/lean_eppa_reducts/blob/9178c621d64cea2e73e65b725bacbd3fc9648ada/EPPAReducts/Classification/GraphSymmetrizationCoherence.lean) are formally checked. Finite two-graphs use the previously checked coherent valuation witness. In the two negative rows, formally defined coherent common-witness predicates imply ordinary EPPA, contradicting the proved finite obstructions.

This proves both EPPA statuses of these *five named finite classes*. Thomas's external model-theoretic enumeration is not asserted as a Lean result.

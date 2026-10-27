# Proof architecture

This page describes the proof graph behind the **audited baseline**. The development does not substitute an external black-box theorem for either requested result.

## Two-graphs: valuations and coherent lifts

1. Reconstruct a graph representative from the four-point parity of the input two-graph. For a chosen root, triple parity is the XOR of the three rooted pair indicators: [rooted graph representative](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/RootedGraphRepresentative.lean).
2. Construct the finite quotient-valuation two-graph. Distinguish **a valuation modulo its pointwise complement for each vertex** from the **global symmetric-matrix quotient** controlling the automorphism group: [valuation quotient](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/ValuationQuotient.lean), [matrix quotient](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/MatrixQuotient.lean), [valuation two-graph](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/ValuationTwoGraph.lean).
3. Embed the given two-graph as an induced transversal of valuations and extend every literal partial automorphism.
4. Build simultaneous homomorphic sections for automorphism groups of **all** induced subsets. The Lean proof chooses $N=|V|!$, which is divisible by every nonzero induced-subset cardinality. The mathematical manuscript may instead use the smaller (\mathrm{lcm}$1,\ldots,|V|$); the larger choice does not change the statement.
5. Assemble canonical transports and sections into one choice satisfying exact composition: [canonical coherent lift](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/CanonicalCoherentLiftComposition.lean), [final human target](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/TwoGraphs/FiniteCoherentEPPA.lean).

## Negative EPPA: finite cyclic obstruction and group theory

1. Choose one finite core with **all $m$** auxiliary colours realized and $r$ distinguishable exterior points.
2. Define $r$ genuine partial automorphisms of this **same** unlabelled equivalence, each cyclically shifting the core while fixing one exterior point. These maps preserve equality of class labels even though they shift the labels.
3. Suppose all extend to full automorphisms of one hypothetical finite witness. Normalize the auxiliary labels of that witness using all the old realized classes. The normalization is justified by the class-count bound.
4. The extensions belong to the same coset of a normalizer of the pointwise core stabilizer. A finite group incidence-counting lemma bounds the number of orbits containing fixed points of that coset.
5. Exterior types are provably inequivalent under the pointwise core stabilizer. With $r$ exteriors and a coset fixed-point bound of $r-1$, a pigeonhole collision yields the contradiction.

The reusable group lemmas are in [`CosetOrbitBound.lean`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/CosetOrbitBound.lean) and [`CosetOrbitCollision.lean`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/CosetOrbitCollision.lean). Ordered and unordered obstructions require different tuple/subset-action bridges; the terminal proofs are [ordered](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/OrderedNoEPPAWitness.lean) and [unordered](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/UnorderedNoEPPAWitness.lean).

**Extra requested corollaries:** the rooting reduction for two-graphs modulo complementation and the complete five-reduct classification must be audited separately when implemented. The preceding coset obstruction does not by itself prove the fifth-reduct non-EPPA statement.

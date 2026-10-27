# Using the Lean library

The public project uses Lean **v4.34.1** and pins its Mathlib and `AllThoseEPPA` dependencies.

## Main import and declarations

The build-root import exposes the checked end theorems:

```lean
import EPPAReducts

#check EPPAReducts.TwoGraphs.humanTwoGraphsHaveCoherentEPPA
#check EPPAReducts.BoundedEquivalence.allUnorderedBoundedEquivalencesFailEPPA
#check EPPAReducts.BoundedEquivalence.orderedBoundedEquivalencesFailEPPA
#check EPPAReducts.BoundedEquivalence.humanGraphsModuloComplementationFailEPPA
```

The declarations above are actual proved theorems, not statements imported as axioms. Look at [Main theorems](Main-theorems.md) for fully qualified source links and assumptions.

## Definitions reusable for further reductions

- [`HumanTargets.TwoGraph` and `CoherentTwoGraphWitness`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/HumanTargets.lean) define actual two-graph parity and coherent extension.
- [`UnorderedBoundedEquivalence`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/UnorderedWitnessAPI.lean) defines equivalences on unordered (r)-sets with unlabelled classes.
- [`OrderedBoundedEquivalence`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/OrderedFiniteObstruction.lean) is the separate ordered injective-tuple version.
- [`CosetOrbitBound.lean`](https://github.com/shulda/lean_eppa_reducts/blob/main/EPPAReducts/BoundedEquivalence/CosetOrbitBound.lean) provides the finite group-counting principle.
- The [`AllThoseEPPA`](https://github.com/shulda/lean_all_those_eppa_classes) package is reused for foundational typed-structure notions; the standalone human targets here are phrased explicitly to avoid hiding a subtle semantic mismatch.

For external consumers, use the exact pinned versions from this repository's `lakefile.toml` and `lake-manifest.json`. A successful import establishes theorem availability; to certify a *new* mathematical application, prove its exact statement and run a fresh full axiom audit.

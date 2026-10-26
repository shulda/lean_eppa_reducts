import EPPAReducts.TwoGraphs.CutPotential
import EPPAReducts.TwoGraphs.RawTripleParity

/-!
# The cut equation for two transversals of the valuation witness

Given source and target coordinate maps and chosen valuation
representatives, each pair x,y has a discrepancy: the XOR of its
source and target edge contributions.

Equality of the raw triple parity on all source and target triples
forces the discrepancy to satisfy the Boolean triangle cocycle
equation. A cut potential therefore exists whenever the domain
is nonempty. This is the core mathematical argument behind the
transversal extension theorem, not yet its symmetric-matrix lift.
-/

namespace EPPAReducts.TwoGraphs

universe u v
variable {D : Type u} {X : Type v}

/-- Pairwise contribution to raw triple parity on a transversal. -/
def transversalPairParity
    (pos : D → X) (χ : D → Valuation X) (x y : D) : Bool :=
  Bool.xor (χ x (pos y)) (χ y (pos x))

/-- The raw triple parity is the XOR of the three pair contributions. -/
theorem rawTripleParity_eq_transversalPairs
    (pos : D → X) (χ : D → Valuation X) (x y z : D) :
    rawTripleParity (pos x) (pos y) (pos z) (χ x) (χ y) (χ z) =
      Bool.xor
        (Bool.xor
          (transversalPairParity pos χ x y)
          (transversalPairParity pos χ x z))
        (transversalPairParity pos χ y z) := by
  rfl

/-- Difference between the source and target pair parities. -/
def transversalPairDiscrepancy
    (src dst : D → X)
    (χ η : D → Valuation X) (x y : D) : Bool :=
  Bool.xor (transversalPairParity src χ x y)
    (transversalPairParity dst η x y)

/-- Equality of the XOR of three source bits and three target bits
forces the three pairwise discrepancies to XOR to false. -/
private theorem xor_triangle_discrepancy_of_equal
    (a b c d e f : Bool)
    (h : Bool.xor (Bool.xor a b) c =
      Bool.xor (Bool.xor d e) f) :
    Bool.xor (Bool.xor (Bool.xor a d) (Bool.xor b e))
      (Bool.xor c f) = false := by
  revert h
  cases a <;> cases b <;> cases c <;>
    cases d <;> cases e <;> cases f <;> decide

/-- Preserving every raw triple parity implies the cut equation
for the discrepancy between the two transversals. -/
theorem transversalDiscrepancy_isTriangleCocycle
    (src dst : D → X) (χ η : D → Valuation X)
    (hpres : ∀ x y z,
      rawTripleParity (src x) (src y) (src z) (χ x) (χ y) (χ z) =
      rawTripleParity (dst x) (dst y) (dst z) (η x) (η y) (η z)) :
    IsBooleanTriangleCocycle
      (transversalPairDiscrepancy src dst χ η) := by
  intro x y z
  have h := hpres x y z
  rw [rawTripleParity_eq_transversalPairs src χ,
    rawTripleParity_eq_transversalPairs dst η] at h
  change Bool.xor
    (Bool.xor
      (Bool.xor (transversalPairParity src χ x y)
        (transversalPairParity dst η x y))
      (Bool.xor (transversalPairParity src χ x z)
        (transversalPairParity dst η x z)))
    (Bool.xor (transversalPairParity src χ y z)
      (transversalPairParity dst η y z)) = false
  exact xor_triangle_discrepancy_of_equal _ _ _ _ _ _ h

/-- The technical cut lemma: preserving raw triple parity gives
a potential c whose cut is exactly the source-target pair discrepancy.
No finiteness hypothesis is necessary. -/
theorem exists_transversalCutPotential [Nonempty D]
    (src dst : D → X) (χ η : D → Valuation X)
    (hpres : ∀ x y z,
      rawTripleParity (src x) (src y) (src z) (χ x) (χ y) (χ z) =
      rawTripleParity (dst x) (dst y) (dst z) (η x) (η y) (η z)) :
    ∃ c : D → Bool, ∀ x y,
      transversalPairDiscrepancy src dst χ η x y =
        Bool.xor (c x) (c y) := by
  exact exists_cutPotential
    (transversalPairDiscrepancy src dst χ η)
    (transversalDiscrepancy_isTriangleCocycle src dst χ η hpres)

end EPPAReducts.TwoGraphs

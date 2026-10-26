import EPPAReducts.TwoGraphs.TransversalRowPrescription
import EPPAReducts.TwoGraphs.SymmetricRowShift

/-!
# Constructing a symmetric extension matrix from compatible row data

A cut potential determines the matrix entries on the rows belonging
to the source transversal. The cut equation is precisely the needed
agreement where two prescribed rows intersect. Fill every remaining
matrix entry with false. The resulting matrix is symmetric and has
the prescribed rows.

This is the matrix-assembly portion of transversal EPPA. It is not
yet the final statement that its quotient action extends a given
partial isomorphism.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u} [DecidableEq X]

/-- Assemble a Boolean matrix by prescribing the row at each vertex
in a finite subset s and setting the other entries to false. -/
noncomputable def assembleTransversalMatrix
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (c : {x : X // x ∈ s} → Bool) :
    X → X → Bool :=
  fun x y =>
    if hx : x ∈ s then
      prescribedTransversalRow σ χ η c ⟨x, hx⟩ y
    else if hy : y ∈ s then
      prescribedTransversalRow σ χ η c ⟨y, hy⟩ x
    else false

/-- Every prescribed row of the assembled matrix has exactly the
required values, including entries outside the source transversal. -/
theorem assembleTransversalMatrix_on_source
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (c : {x : X // x ∈ s} → Bool)
    (x : {z : X // z ∈ s}) (y : X) :
    assembleTransversalMatrix s σ χ η c x.val y =
      prescribedTransversalRow σ χ η c x y := by
  simp [assembleTransversalMatrix, x.property]

/-- If the source-target discrepancy is a cut, the assembled matrix
is symmetric, with no cardinality or nonemptiness assumption. -/
theorem assembleTransversalMatrix_symmetric
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (c : {x : X // x ∈ s} → Bool)
    (hcut : ∀ x y : {z : X // z ∈ s},
      transversalPairDiscrepancy
        (fun z : {w : X // w ∈ s} => z.val)
        (fun z : {w : X // w ∈ s} => σ z.val)
        χ η x y = Bool.xor (c x) (c y)) :
    IsSymmetricBoolMatrix (assembleTransversalMatrix s σ χ η c) := by
  intro x y
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hcompat :=
        prescribedTransversalRow_symmetric
          (fun z : {w : X // w ∈ s} => z.val)
          σ χ η c hcut ⟨x, hx⟩ ⟨y, hy⟩
      change prescribedTransversalRow σ χ η c ⟨x, hx⟩ y =
        prescribedTransversalRow σ χ η c ⟨y, hy⟩ x at hcompat
      simpa [assembleTransversalMatrix, hx, hy] using hcompat
    · simp [assembleTransversalMatrix, hx, hy]
  · by_cases hy : y ∈ s
    · simp [assembleTransversalMatrix, hx, hy]
    · simp [assembleTransversalMatrix, hx, hy]

/-- A cut potential gives a symmetric matrix with precisely the
rows prescribed by the transversal extension construction. -/
theorem exists_symmetricMatrix_with_cut_rows
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (c : {x : X // x ∈ s} → Bool)
    (hcut : ∀ x y : {z : X // z ∈ s},
      transversalPairDiscrepancy
        (fun z : {w : X // w ∈ s} => z.val)
        (fun z : {w : X // w ∈ s} => σ z.val)
        χ η x y = Bool.xor (c x) (c y)) :
    ∃ F : X → X → Bool,
      IsSymmetricBoolMatrix F ∧
      ∀ (x : {z : X // z ∈ s}) (y : X),
        F x.val y = prescribedTransversalRow σ χ η c x y := by
  refine ⟨assembleTransversalMatrix s σ χ η c, ?_, ?_⟩
  · exact assembleTransversalMatrix_symmetric s σ χ η c hcut
  · intro x y
    exact assembleTransversalMatrix_on_source s σ χ η c x y

/-- Under raw parity preservation, one can obtain a symmetric
matrix with the prescribed extension rows on every nonempty finite
transversal, without yet claiming an automorphism extension. -/
theorem exists_symmetricMatrix_of_transversalParity
    (s : Finset X) (hne : s.Nonempty)
    (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (hpres : ∀ x y z : {w : X // w ∈ s},
      rawTripleParity x.val y.val z.val (χ x) (χ y) (χ z) =
      rawTripleParity (σ x.val) (σ y.val) (σ z.val)
        (η x) (η y) (η z)) :
    ∃ c : {x : X // x ∈ s} → Bool,
      ∃ F : X → X → Bool,
        IsSymmetricBoolMatrix F ∧
        ∀ (x : {z : X // z ∈ s}) (y : X),
          F x.val y = prescribedTransversalRow σ χ η c x y := by
  obtain ⟨x, hx⟩ := hne
  letI : Nonempty {z : X // z ∈ s} := ⟨⟨x, hx⟩⟩
  obtain ⟨c, hcut⟩ := exists_transversalCutPotential
    (fun z : {w : X // w ∈ s} => z.val)
    (fun z : {w : X // w ∈ s} => σ z.val)
    χ η hpres
  obtain ⟨F, hF, hrows⟩ :=
    exists_symmetricMatrix_with_cut_rows s σ χ η c hcut
  exact ⟨c, F, hF, hrows⟩

end EPPAReducts.TwoGraphs

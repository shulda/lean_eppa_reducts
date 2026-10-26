import EPPAReducts.TwoGraphs.TransversalMatrixAssembly
import EPPAReducts.TwoGraphs.CombinedAutomorphism

/-!
# Matrix row prescriptions actually extend the required valuation map

The prescribed symmetric matrix has the property that at each domain
vertex its output valuation equals the desired target valuation up to
one constant Boolean bit. Such a bit disappears in the quotient Q_X.

This is the final algebraic conversion from cut-compatible matrix rows
to the genuine combined action on the prescribed transversal.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u} [DecidableEq X]

/-- Adding one constant Boolean bit to all coordinates of a valuation
does not change its complement-equivalence class. -/
theorem valuationClass_xor_constant
    (a : Valuation X) (bit : Bool) :
    valuationClass (fun y => Bool.xor (a y) bit) = valuationClass a := by
  cases bit with
  | false =>
      have heq : (fun y => Bool.xor (a y) false) = a := by
        funext y
        cases h : a y <;> simp [flipValuation, h]
      rw [heq]
  | true =>
      have heq :
          (fun y => Bool.xor (a y) true) = flipValuation a := by
        funext y
        cases a y <;> rfl
      rw [heq, valuationClass_flip]

/-- From the prescribed row formula, the raw output valuation after
reindexing agrees with the target valuation up to the cut constant. -/
theorem prescribedRows_reindex_output
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {z : X // z ∈ s} → Valuation X)
    (c : {z : X // z ∈ s} → Bool)
    (F : X → X → Bool)
    (hrows : ∀ (x : {z : X // z ∈ s}) (y : X),
      F x.val y = prescribedTransversalRow σ χ η c x y)
    (x : {z : X // z ∈ s}) :
    reindexValuation σ (shiftValuationByRow F x.val (χ x)) =
      (fun y => Bool.xor (η x y) (c x)) := by
  funext y
  have hrow := hrows x (σ.symm y)
  change F x.val (σ.symm y) =
    Bool.xor
      (Bool.xor (χ x (σ.symm y)) (η x (σ (σ.symm y))))
      (c x) at hrow
  change
    Bool.xor (χ x (σ.symm y)) (F x.val (σ.symm y)) =
      Bool.xor (η x y) (c x)
  rw [hrow]
  simp only [σ.apply_symm_apply]
  cases ha : χ x (σ.symm y) <;>
    cases hb : η x y <;> cases hc : c x <;> simp_all

/-- The combined action with the prescribed rows maps each old
transversal vertex to the required new vertex in X × Q_X. -/
theorem matrixIndexPerm_maps_prescribed_vertex
    (s : Finset X) (σ : Equiv.Perm X)
    (χ η : {z : X // z ∈ s} → Valuation X)
    (c : {z : X // z ∈ s} → Bool)
    (F : X → X → Bool)
    (hrows : ∀ (x : {z : X // z ∈ s}) (y : X),
      F x.val y = prescribedTransversalRow σ χ η c x y)
    (x : {z : X // z ∈ s}) :
    matrixIndexPerm σ F (x.val, valuationClass (χ x)) =
      (σ x.val, valuationClass (η x)) := by
  have hclass :
      valuationClass (reindexValuation σ
        (shiftValuationByRow F x.val (χ x))) =
      valuationClass (η x) := by
    calc
      valuationClass (reindexValuation σ
        (shiftValuationByRow F x.val (χ x))) =
        valuationClass (fun y => Bool.xor (η x y) (c x)) :=
          congrArg valuationClass
            (prescribedRows_reindex_output s σ χ η c F hrows x)
      _ = valuationClass (η x) :=
          valuationClass_xor_constant (η x) (c x)
  apply Prod.ext
  · rfl
  · change
      valuationClass (reindexValuation σ
        (shiftValuationByRow F x.val (χ x))) =
      valuationClass (η x)
    exact hclass

/-- Actual lifting consequence of cut equation and matrix assembly:
every parity-preserving map between nonempty prescribed transversals,
with a chosen extension σ of its coordinate injection, is implemented
by a symmetric-matrix automorphism of the valuation carrier. -/
theorem exists_matrixIndexPerm_extending_raw_transversal
    (s : Finset X) (hne : s.Nonempty)
    (σ : Equiv.Perm X)
    (χ η : {x : X // x ∈ s} → Valuation X)
    (hpres : ∀ x y z : {w : X // w ∈ s},
      rawTripleParity x.val y.val z.val (χ x) (χ y) (χ z) =
      rawTripleParity (σ x.val) (σ y.val) (σ z.val)
        (η x) (η y) (η z)) :
    ∃ F : X → X → Bool,
      IsSymmetricBoolMatrix F ∧
      ∀ x : {z : X // z ∈ s},
        matrixIndexPerm σ F (x.val, valuationClass (χ x)) =
          (σ x.val, valuationClass (η x)) := by
  obtain ⟨c, F, hsym, hrows⟩ :=
    exists_symmetricMatrix_of_transversalParity s hne σ χ η hpres
  refine ⟨F, hsym, ?_⟩
  intro x
  exact matrixIndexPerm_maps_prescribed_vertex s σ χ η c F hrows x

end EPPAReducts.TwoGraphs

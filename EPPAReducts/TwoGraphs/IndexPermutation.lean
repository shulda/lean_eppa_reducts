import EPPAReducts.TwoGraphs.MatrixAutomorphism

/-!
# Reindexing the finite valuation witness by permutations of X

A permutation σ of the first coordinates acts on valuations by
precomposing with σ⁻¹. This operation is compatible with the quotient
by pointwise complement. It induces a genuine permutation of the
valuation-vertex carrier, preserving the original two-graph relation.

This is the second required family of automorphisms. Matrix
translations and index permutations will subsequently be combined.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- Reindex the coordinates of a Boolean valuation via a permutation. -/
def reindexValuation (σ : Equiv.Perm X) (a : Valuation X) : Valuation X :=
  fun y => a (σ.symm y)

/-- Reindexing commutes with simultaneous Boolean complement. -/
theorem reindexValuation_flip (σ : Equiv.Perm X) (a : Valuation X) :
    reindexValuation σ (flipValuation a) =
      flipValuation (reindexValuation σ a) := by
  rfl

/-- Reindexing followed by the inverse permutation gives the old valuation. -/
theorem reindexValuation_symm_left
    (σ : Equiv.Perm X) (a : Valuation X) :
    reindexValuation σ.symm (reindexValuation σ a) = a := by
  funext y
  simp [reindexValuation]

theorem reindexValuation_symm_right
    (σ : Equiv.Perm X) (a : Valuation X) :
    reindexValuation σ (reindexValuation σ.symm a) = a := by
  funext y
  simp [reindexValuation]

/-- Reindexing is well-defined on the quotient of valuations by complement. -/
def reindexValuationClass
    (σ : Equiv.Perm X) (q : ValuationClass X) : ValuationClass X :=
  Quotient.liftOn q
    (fun a => valuationClass (reindexValuation σ a))
    (by
      intro a b h
      rcases h with hab | hab
      · rw [hab]
      · rw [hab, reindexValuation_flip, valuationClass_flip])

@[simp] theorem reindexValuationClass_mk
    (σ : Equiv.Perm X) (a : Valuation X) :
    reindexValuationClass σ (valuationClass a) =
      valuationClass (reindexValuation σ a) := by
  rfl

theorem reindexValuationClass_symm_left
    (σ : Equiv.Perm X) (q : ValuationClass X) :
    reindexValuationClass σ.symm (reindexValuationClass σ q) = q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass
      (reindexValuation σ.symm (reindexValuation σ a)) = valuationClass a
    rw [reindexValuation_symm_left]

theorem reindexValuationClass_symm_right
    (σ : Equiv.Perm X) (q : ValuationClass X) :
    reindexValuationClass σ (reindexValuationClass σ.symm q) = q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change valuationClass
      (reindexValuation σ (reindexValuation σ.symm a)) = valuationClass a
    rw [reindexValuation_symm_right]

/-- A genuine permutation of the entire valuation witness carrier. -/
def indexPermVertex (σ : Equiv.Perm X) : Equiv.Perm (ValuationVertex X) where
  toFun := fun v => (σ v.1, reindexValuationClass σ v.2)
  invFun := fun v => (σ.symm v.1, reindexValuationClass σ.symm v.2)
  left_inv := by
    rintro ⟨x, q⟩
    change (σ.symm (σ x), reindexValuationClass σ.symm
      (reindexValuationClass σ q)) = (x, q)
    simp [reindexValuationClass_symm_left]
  right_inv := by
    rintro ⟨x, q⟩
    change (σ (σ.symm x), reindexValuationClass σ
      (reindexValuationClass σ.symm q)) = (x, q)
    simp [reindexValuationClass_symm_right]

/-- The raw six-entry parity is invariant under simultaneous reindexing. -/
theorem rawTripleParity_reindex
    (σ : Equiv.Perm X)
    (x y z : X) (a b c : Valuation X) :
    rawTripleParity (σ x) (σ y) (σ z)
      (reindexValuation σ a) (reindexValuation σ b) (reindexValuation σ c) =
      rawTripleParity x y z a b c := by
  simp [rawTripleParity, reindexValuation]

/-- The same formula for three quotient valuation classes. -/
theorem quotientTripleParity_reindex
    (σ : Equiv.Perm X)
    (x y z : X) (a b c : ValuationClass X) :
    quotientTripleParity (σ x) (σ y) (σ z)
      (reindexValuationClass σ a) (reindexValuationClass σ b)
      (reindexValuationClass σ c) =
        quotientTripleParity x y z a b c := by
  induction a using Quotient.inductionOn with
  | _ va =>
    induction b using Quotient.inductionOn with
    | _ vb =>
      induction c using Quotient.inductionOn with
      | _ vc =>
        change rawTripleParity (σ x) (σ y) (σ z)
          (reindexValuation σ va) (reindexValuation σ vb)
          (reindexValuation σ vc) =
            rawTripleParity x y z va vb vc
        exact rawTripleParity_reindex σ x y z va vb vc

/-- Fibre reindexing preserves ternary parity of valuation vertices. -/
theorem vertexTripleParity_reindex
    (σ : Equiv.Perm X)
    (a b c : ValuationVertex X) :
    vertexTripleParity (indexPermVertex σ a)
      (indexPermVertex σ b) (indexPermVertex σ c) =
        vertexTripleParity a b c := by
  rcases a with ⟨x, va⟩
  rcases b with ⟨y, vb⟩
  rcases c with ⟨z, vc⟩
  exact quotientTripleParity_reindex σ x y z va vb vc

/-- Any permutation of the index set induces an automorphism of the
author-approved valuation two-graph. -/
theorem indexPermVertex_isTwoGraphAutomorphism
    {X : Type} [DecidableEq (ValuationVertex X)]
    (σ : Equiv.Perm X) :
    HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X)
      (indexPermVertex σ) := by
  apply valuationTwoGraph_automorphism_of_ternary
  intro a b c
  exact vertexTripleParity_reindex σ a b c

end EPPAReducts.TwoGraphs

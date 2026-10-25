import Mathlib.Data.Bool.Basic

/-!
# The valuation quotient for two-graph witnesses

Each vertex of the eventual witness is a first-coordinate x together with
a valuation χ : X → Bool, identified with its pointwise complement.

This is the *per-vertex valuation equivalence*, not the distinct quotient
of all symmetric matrices by one globally constant matrix.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {X : Type u}

/-- An F₂-valued valuation, represented by Bool. -/
abbrev Valuation (X : Type u) := X → Bool

/-- Simultaneously complement every entry of one valuation. -/
def flipValuation (χ : Valuation X) : Valuation X :=
  fun x => !χ x

@[simp] theorem flipValuation_flip (χ : Valuation X) :
    flipValuation (flipValuation χ) = χ := by
  funext x
  simp [flipValuation]

/-- Two valuations represent the same quotient point exactly when they are
equal or differ by the constant-one valuation. -/
def valuationSetoid (X : Type u) : Setoid (Valuation X) where
  r χ ξ := χ = ξ ∨ χ = flipValuation ξ
  iseqv := {
    refl := fun χ => Or.inl rfl
    symm := by
      intro χ ξ h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        calc
          ξ = flipValuation (flipValuation ξ) :=
            (flipValuation_flip ξ).symm
          _ = flipValuation χ := (congrArg flipValuation h).symm
    trans := by
      intro χ ξ ζ hχξ hξζ
      rcases hχξ with hχξ | hχξ
      · subst χ
        exact hξζ
      · rcases hξζ with hξζ | hξζ
        · subst ζ
          exact Or.inr hχξ
        · left
          calc
            χ = flipValuation ξ := hχξ
            _ = flipValuation (flipValuation ζ) := congrArg flipValuation hξζ
            _ = ζ := flipValuation_flip ζ
  }

/-- Quotient of X-valuations by complementing the entire valuation. -/
abbrev ValuationClass (X : Type u) :=
  Quotient (valuationSetoid X)

/-- The quotient map. -/
def valuationClass (χ : Valuation X) : ValuationClass X :=
  Quotient.mk (valuationSetoid X) χ

/-- Complementing one representative does not change its quotient class. -/
theorem valuationClass_flip (χ : Valuation X) :
    valuationClass (flipValuation χ) = valuationClass χ :=
  Quotient.sound (Or.inr rfl)

end EPPAReducts.TwoGraphs

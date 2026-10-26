import EPPAReducts.TwoGraphs.RootedTransversalEmbedding
import Mathlib.Logic.Equiv.Fintype

/-!
# Removing the auxiliary order from finite rooted representations

The previous induced-transversal construction only requires a linear
order on the original carrier.  Every finite type has such an order
by transporting the usual order from Fin (card V) along the standard
finite equivalence.

For nonempty finite V, choose an arbitrary root; the resulting
valuation embedding is induced in the author's exact TwoGraph API.
The empty carrier remains a separate final-witness case.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Choose a linear order on any finite type, with no pre-existing
order assumption on the input two-graph. -/
noncomputable def finiteCarrierLinearOrder
    (V : Type) [Fintype V] : LinearOrder V := by
  classical
  exact LinearOrder.lift'
    (Fintype.equivFin V) (Fintype.equivFin V).injective

/-- The author-approved finite two-graph, on any nonempty carrier,
admits an induced embedding into its full valuation transversal C_V.
This makes no mathematical hypothesis about a pre-chosen order. -/
theorem exists_induced_rootedValuation_embedding
    {V : Type} [Fintype V] [Nonempty V]
    [DecidableEq (ValuationVertex V)]
    (A : TwoGraph V) :
    ∃ ι : V ↪ ValuationVertex V,
      IsInducedTwoGraphEmbedding A (valuationTwoGraph V) ι := by
  letI : LinearOrder V := finiteCarrierLinearOrder V
  let o : V := Classical.choice ‹Nonempty V›
  exact ⟨orderedRootTransversalEmbedding A o,
    orderedRootTransversalEmbedding_induced A o⟩

end EPPAReducts.TwoGraphs

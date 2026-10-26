import EPPAReducts.TwoGraphs.FiniteRootedTransversal
import EPPAReducts.TwoGraphs.ValuationBlockInflation

/-!
# Induced rooted-transversal embeddings at any divisible index size

Start with an arbitrary nonempty finite two-graph A on V and a
specified injection ι : V ↪ X, with |V| dividing |X|. Choose marked
block coordinates B with distinguished embedding exactly ι.

Inflate the canonical V-valuations along B.projection.  The resulting
map v ↦ (ι v, [inflated χ_v]) is an induced embedding into the exact
HumanTargets valuation two-graph C_X.  It uses the earlier induced
embedding of C_V into C_X, rather than repeating parity arguments.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- The embedding associated with an injective index map and a chosen
valuation at each old vertex. -/
def indexedTransversalEmbedding {V X : Type}
    (ι : V ↪ X) (χ : V → Valuation X) :
    V ↪ ValuationVertex X where
  toFun := fun v => (ι v, valuationClass (χ v))
  inj' := by
    intro v w h
    exact ι.injective (congrArg Prod.fst h)

/-- **Induced representation at arbitrary divisible index size.**
Every finite nonempty original two-graph admits an induced valuation
transversal in C_X over *any specified injection* V ↪ X whose
cardinality is divisible by |V|. -/
theorem exists_indexed_rootedTransversal
    {V X : Type} [Fintype V] [Fintype X] [Nonempty V]
    [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X)
    (hdiv : Fintype.card V ∣ Fintype.card X) :
    ∃ χ : V → Valuation X,
      IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
        (indexedTransversalEmbedding ι χ) := by
  classical
  letI : LinearOrder V := finiteCarrierLinearOrder V
  let o : V := Classical.choice ‹Nonempty V›
  obtain ⟨B, hB⟩ := exists_markedBlockCoordinates_of_dvd ι hdiv
  let χ : V → Valuation X :=
    fun v => inflateValuation B.projection (orderedRootValuation A o v)
  let j : V ↪ ValuationVertex V := orderedRootTransversalEmbedding A o
  have heq (v : V) :
      indexedTransversalEmbedding ι χ v =
        B.inflateValuationVertex (j v) := by
    apply Prod.ext
    · exact (hB v).symm
    · rfl
  refine ⟨χ, ?_⟩
  intro x y z
  rw [heq x, heq y, heq z]
  exact ((orderedRootTransversalEmbedding_induced A o) x y z).trans
    ((B.inflateValuationVertex_induced) (j x) (j y) (j z))

end EPPAReducts.TwoGraphs

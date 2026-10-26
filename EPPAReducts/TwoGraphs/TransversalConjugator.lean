import EPPAReducts.TwoGraphs.RestrictedTransversal
import EPPAReducts.TwoGraphs.TransversalCoordinateExtension

/-!
# A single conjugating automorphism for a marked transversal

The restriction-and-inflation construction produces a full D-transversal
embedded into C_X.  Its corresponding original transversal (using the
unrestricted X-valuations) is induced-isomorphic.  The already certified
transversal EPPA lemma extends this isomorphism to one ambient
automorphism γ of C_X.

That same γ can subsequently conjugate all homomorphic subgroup lifts.
-/

namespace EPPAReducts.TwoGraphs

variable {D X : Type}

/-- The finite set of coordinates in the distinguished marked block. -/
def BlockCoordinates.markedFinset
    (B : BlockCoordinates D X) [Fintype D] [DecidableEq X] :
    Finset X :=
  Finset.univ.image B.markedEmbedding

/-- Every marked coordinate lies in the distinguished block's finite set. -/
theorem BlockCoordinates.marked_mem_markedFinset
    (B : BlockCoordinates D X) [Fintype D] [DecidableEq X]
    (d : D) :
    B.markedEmbedding d ∈ B.markedFinset := by
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩

/-- The block projection is a true inverse to the marked inclusion,
also when the argument is presented only as an element of its image. -/
theorem BlockCoordinates.marked_projection_of_mem
    (B : BlockCoordinates D X) [Fintype D] [DecidableEq X]
    (x : X) (hx : x ∈ B.markedFinset) :
    B.markedEmbedding (B.projection x) = x := by
  change x ∈ Finset.univ.image B.markedEmbedding at hx
  obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hx
  rw [← hd, B.projection_marked]

/-- The two induced-isomorphic D-indexed transversals of C_X can be
connected by one global automorphism.  This conjugator is chosen
*once* for all later automorphisms of the small transversal. -/
theorem BlockCoordinates.exists_conjugatingAutomorphism
    (B : BlockCoordinates D X)
    [Fintype D] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (χ : D → Valuation X) :
    ∃ γ : Equiv.Perm (ValuationVertex X),
      HumanTargets.IsTwoGraphAutomorphism (valuationTwoGraph X) γ ∧
      ∀ d : D,
        γ (B.inflateValuationVertex
          (d, valuationClass (restrictedTransversalValuations
            B.markedEmbedding χ d))) =
          (B.markedEmbedding d, valuationClass (χ d)) := by
  classical
  let s : Finset X := B.markedFinset
  let χD : D → Valuation D :=
    restrictedTransversalValuations B.markedEmbedding χ
  let f : {x : X // x ∈ s} ↪ X :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let α : {x : X // x ∈ s} → Valuation X :=
    fun x => inflateValuation B.projection (χD (B.projection x.val))
  let β : {x : X // x ∈ s} → Valuation X :=
    fun x => χ (B.projection x.val)
  have hmarked (x : {x : X // x ∈ s}) :
      B.markedEmbedding (B.projection x.val) = x.val := by
    exact B.marked_projection_of_mem x.val x.property
  have hsource (x : {x : X // x ∈ s}) :
      sourceTransversalVertex s α x =
        B.inflateValuationVertex
          (B.projection x.val, valuationClass (χD (B.projection x.val))) := by
    apply Prod.ext
    · exact (hmarked x).symm
    · rfl
  have htarget (x : {x : X // x ∈ s}) :
      (f x, valuationClass (β x)) =
        (B.markedEmbedding (B.projection x.val),
          valuationClass (χ (B.projection x.val))) := by
    apply Prod.ext
    · exact (hmarked x).symm
    · rfl
  have hpres : PreservesTransversalEmbeddingTwoGraph s f α β := by
    intro x y z
    change (valuationTwoGraph X).isTriple
        (HumanTargets.triple
          (sourceTransversalVertex s α x)
          (sourceTransversalVertex s α y)
          (sourceTransversalVertex s α z)) =
      (valuationTwoGraph X).isTriple
        (HumanTargets.triple
          (f x, valuationClass (β x))
          (f y, valuationClass (β y))
          (f z, valuationClass (β z)))
    rw [hsource x, hsource y, hsource z,
      htarget x, htarget y, htarget z]
    exact B.restrictedTransversal_induced_iso χ
      (B.projection x.val) (B.projection y.val) (B.projection z.val)
  obtain ⟨γ, hγ, hmaps⟩ :=
    exists_twoGraphAutomorphism_extending_any_transversal_embedding
      s f α β hpres
  refine ⟨γ, hγ, ?_⟩
  intro d
  have hmem : B.markedEmbedding d ∈ s :=
    B.marked_mem_markedFinset d
  have hd := hmaps ⟨B.markedEmbedding d, hmem⟩
  change γ
    (B.markedEmbedding d, valuationClass
      (inflateValuation B.projection
        (χD (B.projection (B.markedEmbedding d))))) =
    (B.markedEmbedding d,
      valuationClass (χ (B.projection (B.markedEmbedding d)))) at hd
  change γ (B.markedEmbedding d,
      valuationClass (inflateValuation B.projection (χD d))) =
    (B.markedEmbedding d, valuationClass (χ d))
  simpa only [B.projection_marked] using hd

end EPPAReducts.TwoGraphs

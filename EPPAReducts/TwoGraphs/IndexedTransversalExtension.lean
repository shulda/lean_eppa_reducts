import EPPAReducts.TwoGraphs.InducedSubtypeSection
import EPPAReducts.TwoGraphs.TransversalCoordinateExtension

/-!
# Arbitrarily indexed transversal isomorphisms extend

A finite source transversal may be indexed by an arbitrary finite type D,
not necessarily by a subset of X.  The injection ι : D ↪ X identifies
D with the subtype of its image.  Transporting the source and target
valuations along this equivalence allows direct application of the
already-certified extension theorem for index subsets of X.

This avoids choosing or extending a coordinate permutation by hand.
The resulting extension is a genuine automorphism of the literal
valuation two-graph in the approved HumanTargets interface.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- An injection of a finite type is a bijection onto the subtype
of its finite image in the target. -/
noncomputable def imageSubtypeEquiv
    {D X : Type} [Fintype D] [DecidableEq X] (ι : D ↪ X) :
    D ≃ {x : X // x ∈ Finset.univ.image ι} := by
  classical
  refine Equiv.ofBijective
    (fun d : D =>
      (⟨ι d, Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩⟩ :
        {x : X // x ∈ Finset.univ.image ι})) ?_
  constructor
  · intro d e h
    exact ι.injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hx
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact hd

/-- The inverse of the image equivalence recovers the original
coordinate of every point in the image. -/
theorem imageSubtypeEquiv_symm_val
    {D X : Type} [Fintype D] [DecidableEq X] (ι : D ↪ X)
    (x : {x : X // x ∈ Finset.univ.image ι}) :
    ι ((imageSubtypeEquiv ι).symm x) = x.val := by
  exact congrArg Subtype.val ((imageSubtypeEquiv ι).apply_symm_apply x)

/-- Extend any induced isomorphism of two finite transversals
with arbitrary injected source and target coordinates. -/
theorem exists_twoGraphAutomorphism_extending_indexedTransversalIso
    {D X : Type} [Fintype D] [DecidableEq X]
    [DecidableEq (ValuationVertex X)]
    (ι τ : D ↪ X) (χ η : D → Valuation X)
    (h : ∀ d e f : D,
      (valuationTwoGraph X).isTriple
        (triple (ι d, valuationClass (χ d))
                (ι e, valuationClass (χ e))
                (ι f, valuationClass (χ f))) =
      (valuationTwoGraph X).isTriple
        (triple (τ d, valuationClass (η d))
                (τ e, valuationClass (η e))
                (τ f, valuationClass (η f)))) :
    ∃ g : Equiv.Perm (ValuationVertex X),
      IsTwoGraphAutomorphism (valuationTwoGraph X) g ∧
      ∀ d : D, g (ι d, valuationClass (χ d)) =
        (τ d, valuationClass (η d)) := by
  classical
  let s : Finset X := Finset.univ.image ι
  let e : D ≃ {x : X // x ∈ s} := imageSubtypeEquiv ι
  let f : {x : X // x ∈ s} ↪ X :=
    ⟨fun x => τ (e.symm x), by
      intro x y hxy
      exact e.symm.injective (τ.injective hxy)⟩
  let χs : {x : X // x ∈ s} → Valuation X :=
    fun x => χ (e.symm x)
  let ηs : {x : X // x ∈ s} → Valuation X :=
    fun x => η (e.symm x)
  have hpres : PreservesTransversalEmbeddingTwoGraph s f χs ηs := by
    intro x y z
    have hx : ι (e.symm x) = x.val := imageSubtypeEquiv_symm_val ι x
    have hy : ι (e.symm y) = y.val := imageSubtypeEquiv_symm_val ι y
    have hz : ι (e.symm z) = z.val := imageSubtypeEquiv_symm_val ι z
    change (valuationTwoGraph X).isTriple
      (triple
        (x.val, valuationClass (χ (e.symm x)))
        (y.val, valuationClass (χ (e.symm y)))
        (z.val, valuationClass (χ (e.symm z)))) =
      (valuationTwoGraph X).isTriple
        (triple
          (τ (e.symm x), valuationClass (η (e.symm x)))
          (τ (e.symm y), valuationClass (η (e.symm y)))
          (τ (e.symm z), valuationClass (η (e.symm z))))
    rw [← hx, ← hy, ← hz]
    exact h (e.symm x) (e.symm y) (e.symm z)
  obtain ⟨g, hg, hmaps⟩ :=
    exists_twoGraphAutomorphism_extending_any_transversal_embedding
      s f χs ηs hpres
  refine ⟨g, hg, ?_⟩
  intro d
  have hd := hmaps (e d)
  change g ((e d).val, valuationClass (χ (e.symm (e d)))) =
    (τ (e.symm (e d)), valuationClass (η (e.symm (e d)))) at hd
  have hed : (e d).val = ι d := rfl
  simpa only [Equiv.symm_apply_apply, hed] using hd

end EPPAReducts.TwoGraphs

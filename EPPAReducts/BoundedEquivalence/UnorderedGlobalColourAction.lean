import EPPAReducts.BoundedEquivalence.UnorderedCoreTransport
import EPPAReducts.BoundedEquivalence.CoreLabelAction

namespace EPPAReducts.BoundedEquivalence

theorem permuteRSubset_map_core
    {V S : Type} {r : ℕ}
    (ι : S ↪ V) (p : Equiv.Perm S) (g : Equiv.Perm V)
    (hcore : ∀ s : S, g (ι s) = ι (p s))
    (t : RSubsets S r) :
    permuteRSubset g (mapRSubset ι t) =
      mapRSubset ι (permuteRSubset p t) := by
  apply Subtype.ext
  change (t.val.map ι).map (⟨g, g.injective⟩ : V ↪ V) =
    (t.val.map (⟨p, p.injective⟩ : S ↪ S)).map ι
  rw [Finset.map_map, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro x
  exact hcore x

theorem unorderedKernel_core_shift_all_colours
    {V S κ : Type} [AddGroup κ] {r : ℕ}
    (f : RSubsets V r → κ) (ι : S ↪ V)
    (g : Equiv.Perm V) (p : Equiv.Perm S) (δ : κ)
    (hg : g ∈ unorderedSubsetKernelAutSubgroup f)
    (hcore : ∀ s : S, g (ι s) = ι (p s))
    (hsurj : Function.Surjective
      (fun t : RSubsets S r => f (mapRSubset ι t)))
    (hshiftCore : ∀ t : RSubsets S r,
      f (mapRSubset ι (permuteRSubset p t)) =
        f (mapRSubset ι t) + δ) :
    ∀ t : RSubsets V r,
      f (permuteRSubset g t) = f t + δ := by
  have hkernel : ∀ t u : RSubsets V r,
      f t = f u →
        f (permuteRSubset g t) =
          f (permuteRSubset g u) := by
    intro t u h
    exact (hg t u).mp h
  apply core_constant_shift_determines_all_labels
    (mapRSubset ι) f hsurj
    (permuteRSubset g) hkernel δ
  intro t
  rw [permuteRSubset_map_core ι p g hcore t]
  exact hshiftCore t

end EPPAReducts.BoundedEquivalence

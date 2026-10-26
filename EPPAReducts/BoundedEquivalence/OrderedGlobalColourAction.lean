import EPPAReducts.BoundedEquivalence.OrderedClassShiftFixed
import EPPAReducts.BoundedEquivalence.CoreLabelAction

namespace EPPAReducts.BoundedEquivalence

theorem permuteOrderedTuple_map_core
    {V S : Type} {r : ℕ}
    (ι : S ↪ V) (p : Equiv.Perm S) (g : Equiv.Perm V)
    (hcore : ∀ s : S, g (ι s) = ι (p s))
    (t : InjectiveTuples S r) :
    permuteOrderedTuple g (mapInjectiveTuple ι t) =
      mapInjectiveTuple ι (permuteOrderedTuple p t) := by
  apply Subtype.ext
  funext j
  exact hcore (t.val j)

theorem orderedKernel_core_shift_all_colours
    {V S κ : Type} [AddGroup κ] {r : ℕ}
    (f : InjectiveTuples V r → κ) (ι : S ↪ V)
    (g : Equiv.Perm V) (p : Equiv.Perm S) (δ : κ)
    (hg : g ∈ orderedTupleKernelAutSubgroup f)
    (hcore : ∀ s : S, g (ι s) = ι (p s))
    (hsurj : Function.Surjective
      (fun t : InjectiveTuples S r => f (mapInjectiveTuple ι t)))
    (hshiftCore : ∀ t : InjectiveTuples S r,
      f (mapInjectiveTuple ι (permuteOrderedTuple p t)) =
        f (mapInjectiveTuple ι t) + δ) :
    ∀ t : InjectiveTuples V r,
      f (permuteOrderedTuple g t) = f t + δ := by
  have hkernel : ∀ t u : InjectiveTuples V r,
      f t = f u →
        f (permuteOrderedTuple g t) =
          f (permuteOrderedTuple g u) := by
    intro t u h
    exact (hg t u).mp h
  apply core_constant_shift_determines_all_labels
    (mapInjectiveTuple ι) f hsurj
    (permuteOrderedTuple g) hkernel δ
  intro t
  rw [permuteOrderedTuple_map_core ι p g hcore t]
  exact hshiftCore t

end EPPAReducts.BoundedEquivalence

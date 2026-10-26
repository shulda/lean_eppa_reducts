import EPPAReducts.BoundedEquivalence.OrderedCoreTransport
import EPPAReducts.BoundedEquivalence.OrderedColourTranslationFixed
import EPPAReducts.BoundedEquivalence.CosetOrbitCollision

/-!
# The normalizer-coset collision from a common old-core shift

This combines the finite coset-orbit lemma with the unlabelled
ordered tuple class-action theorem. Any family of b+1 full
automorphisms extending the same shift on an old core, each fixing
one distinguished vertex, forces two such vertices into a single
orbit of the core's pointwise fixer.

The hypothesis that the old core realizes every auxiliary colour
is essential. Colour names are a proof device only.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Any b+1 full unlabelled kernel automorphisms extending a common
old-core permutation which shifts all realized colours by a nonzero
δ have two distinguished fixed vertices in the same orbit of the
old-core pointwise stabilizer. -/
theorem orderedKernel_core_extension_orbit_collision
    {W S κ : Type} [Fintype W] [DecidableEq W]
    [AddGroup κ] (b : ℕ)
    (f : InjectiveTuples W (b + 1) → κ)
    (ι : S ↪ W) (p : Equiv.Perm S)
    (δ : κ) (hδ : δ ≠ 0)
    (hsurj : Function.Surjective
      (fun t : InjectiveTuples S (b + 1) =>
        f (mapInjectiveTuple ι t)))
    (hshiftCore : ∀ t : InjectiveTuples S (b + 1),
      f (mapInjectiveTuple ι (permuteOrderedTuple p t)) =
        f (mapInjectiveTuple ι t) + δ)
    (a : Fin (b + 1) ↪ W)
    (g : Fin (b + 1) → Equiv.Perm W)
    (hg : ∀ i, g i ∈ orderedTupleKernelAutSubgroup f)
    (hgcore : ∀ i s, g i (ι s) = ι (p s))
    (hfix : ∀ i, g i (a i) = a i) :
    ∃ i j : Fin (b + 1), i ≠ j ∧
      ∃ l : orderedKernelCorePointwiseFixer f ι,
        l.val (a i) = a j := by
  classical
  let i0 : Fin (b + 1) := ⟨0, Nat.zero_lt_succ b⟩
  let L := orderedKernelCorePointwiseFixer f ι
  have hnormal : g i0 ∈ Subgroup.normalizer L :=
    orderedCoreExtension_normalizes f ι p (g i0)
      (hg i0) (hgcore i0)
  have hcap : ∀ l : L,
      (Finset.univ.filter
        (fun x : W => l.val ((g i0) x) = x)).card ≤ b := by
    intro l
    have hlAut : l.val * g i0 ∈ orderedTupleKernelAutSubgroup f :=
      (orderedTupleKernelAutSubgroup f).mul_mem l.property.1 (hg i0)
    have hlcore : ∀ s : S,
        (l.val * g i0) (ι s) = ι (p s) := by
      intro s
      calc
        (l.val * g i0) (ι s) = l.val (g i0 (ι s)) := rfl
        _ = l.val (ι (p s)) := congrArg l.val (hgcore i0 s)
        _ = ι (p s) := l.property.2 (p s)
    have hglobal := orderedKernel_core_shift_all_colours
      f ι (l.val * g i0) p δ hlAut hlcore hsurj hshiftCore
    have hbound := orderedKernel_shift_fixedVertices_card_lt
      f (l.val * g i0) δ hδ hglobal
    exact Nat.lt_succ_iff.mp hbound
  have hfixable : ∀ i : Fin (b + 1),
      ∃ l : L, l.val (g i0 (a i)) = a i := by
    intro i
    obtain ⟨l, hl⟩ := orderedCoreExtensions_same_coset
      f ι p (g i0) (g i) (hg i0) (hg i)
      (hgcore i0) (hgcore i)
    refine ⟨l, ?_⟩
    calc
      l.val (g i0 (a i)) = (l.val * g i0) (a i) := rfl
      _ = g i (a i) := congrArg (fun q : Equiv.Perm W => q (a i)) hl
      _ = a i := hfix i
  exact coset_fixed_vertices_orbit_collision
    L (g i0) hnormal b hcap a hfixable

end EPPAReducts.BoundedEquivalence

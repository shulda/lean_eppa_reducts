import EPPAReducts.BoundedEquivalence.OrderedGlobalColourAction

namespace EPPAReducts.BoundedEquivalence

/-- Translation of an additive group is an actual permutation. -/
def orderedColourTranslationPerm
    {κ : Type} [AddGroup κ] (δ : κ) : Equiv.Perm κ where
  toFun c := c + δ
  invFun c := c - δ
  left_inv := by intro c; simp
  right_inv := by intro c; simp

theorem orderedColourTranslationPerm_no_fixed
    {κ : Type} [AddGroup κ] (δ : κ) (hδ : δ ≠ 0) :
    ∀ c : κ, orderedColourTranslationPerm δ c ≠ c := by
  intro c h
  change c + δ = c at h
  have h' : c + δ = c + 0 := by simpa only [add_zero] using h
  exact hδ (add_left_cancel h')

/-- An automorphism shifting every auxiliary colour by a nonzero
constant fixes strictly fewer than r vertices. The conclusion
concerns actual vertex permutations preserving the unlabelled
kernel; no colour names belong to its language. -/
theorem orderedKernel_shift_fixedVertices_card_lt
    {V κ : Type} [Fintype V] [DecidableEq V]
    [AddGroup κ] {r : ℕ}
    (f : InjectiveTuples V r → κ)
    (g : Equiv.Perm V) (δ : κ) (hδ : δ ≠ 0)
    (hshift : ∀ t : InjectiveTuples V r,
      f (permuteOrderedTuple g t) = f t + δ) :
    (Finset.univ.filter (fun x : V => g x = x)).card < r := by
  exact orderedClassShift_fixedVertices_card_lt f g
    (orderedColourTranslationPerm δ)
    (orderedColourTranslationPerm_no_fixed δ hδ) hshift

end EPPAReducts.BoundedEquivalence

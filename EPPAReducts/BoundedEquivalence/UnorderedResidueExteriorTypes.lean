import EPPAReducts.BoundedEquivalence.UnorderedCyclicSumColour

/-!
# Translation-invariant residues and distinct unordered exterior types

For a t-element subset of a cyclic group whose order is divisible
by t, its vertex sum reduced modulo t is fixed by unit translation.
Distinct nonempty residue fibres can therefore be used to perturb a
common equivariant colouring into several different equivariant types.

The injectivity result below explicitly assumes the residue map is
surjective; proving that hypothesis for the common cyclic core is a
separate constructive obligation.
-/

namespace EPPAReducts.BoundedEquivalence

/-- The sum of a t-subset, reduced modulo its cardinality t.
This is a numerical proof device, not a named structural relation. -/
def unorderedSubsetResidue
    {N t : ℕ} (hdiv : t ∣ N)
    (s : RSubsets (ZMod N) t) : ZMod t :=
  (ZMod.castHom hdiv (ZMod t)) (unorderedSubsetSum s)

/-- The residue is invariant under adding one to every member of
the t-subset. -/
theorem unorderedSubsetResidue_translate_one
    (N t : ℕ) (hdiv : t ∣ N)
    (s : RSubsets (ZMod N) t) :
    unorderedSubsetResidue hdiv
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedSubsetResidue hdiv s := by
  unfold unorderedSubsetResidue
  rw [unorderedSubsetSum_translate_one]
  change (ZMod.cast (unorderedSubsetSum s + (t : ZMod N)) : ZMod t) =
    (ZMod.cast (unorderedSubsetSum s) : ZMod t)
  rw [ZMod.cast_add hdiv, ZMod.cast_natCast hdiv,
    ZMod.natCast_self, add_zero]

/-- A translation-invariant indicator of one numerical residue. -/
def unorderedResidueIndicator
    {N t m : ℕ} (hdiv : t ∣ N) (i : Fin t)
    (s : RSubsets (ZMod N) t) : ZMod m :=
  if unorderedSubsetResidue hdiv s = (i.val : ZMod t) then 1 else 0

theorem unorderedResidueIndicator_translate_one
    (N t m : ℕ) (hdiv : t ∣ N) (i : Fin t)
    (s : RSubsets (ZMod N) t) :
    unorderedResidueIndicator (m := m) hdiv i
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedResidueIndicator (m := m) hdiv i s := by
  unfold unorderedResidueIndicator
  rw [unorderedSubsetResidue_translate_one]

/-- Perturb an equivariant base colour by a translation-invariant
residue indicator; the result stays equivariant. -/
def unorderedResidueExteriorType
    {N t m : ℕ} (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m)
    (i : Fin t) (s : RSubsets (ZMod N) t) : ZMod m :=
  base s + unorderedResidueIndicator hdiv i s

theorem unorderedResidueExteriorType_translate_one
    (N t m : ℕ) (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m)
    (hbase : ∀ s : RSubsets (ZMod N) t,
      base (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
        base s + 1)
    (i : Fin t) (s : RSubsets (ZMod N) t) :
    unorderedResidueExteriorType hdiv base i
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedResidueExteriorType hdiv base i s + 1 := by
  unfold unorderedResidueExteriorType
  rw [hbase, unorderedResidueIndicator_translate_one]
  ac_rfl

/-- If every residue value occurs and m >= 2, the t perturbed
exterior types are pairwise distinct. -/
theorem unorderedResidueExteriorTypes_injective
    (N t m : ℕ) (hm : 2 ≤ m)
    (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m)
    (hres : Function.Surjective (unorderedSubsetResidue hdiv)) :
    Function.Injective
      (fun i : Fin t => unorderedResidueExteriorType hdiv base i) := by
  classical
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have hm1 := ZMod.one_eq_zero_iff.mp h
    omega
  intro i j heq
  by_contra hij
  have ht : 0 < t := by omega
  letI : NeZero t := ⟨Nat.ne_of_gt ht⟩
  have hcast : (i.val : ZMod t) ≠ (j.val : ZMod t) := by
    intro h
    apply hij
    apply Fin.ext
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt i.isLt,
      ZMod.val_natCast_of_lt j.isLt] using hh
  obtain ⟨s, hs⟩ := hres (i.val : ZMod t)
  have hpoint := congrFun heq s
  have hbad : base s + (1 : ZMod m) = base s + 0 := by
    simpa [unorderedResidueExteriorType, unorderedResidueIndicator,
      hs, hcast] using hpoint
  exact hone (add_left_cancel hbad)

end EPPAReducts.BoundedEquivalence

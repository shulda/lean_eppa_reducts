import EPPAReducts.BoundedEquivalence.UnorderedResidueExteriorTypes

/-!
# One base exterior type and t residue-modified exterior types

An equivariant t-subset colouring together with a surjective
translation-invariant residue function yields t+1 pairwise distinct
equivariant colourings. This is exactly the number needed when
t=r-1 in the unordered non-EPPA obstruction.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Inserting a new value before an injective family remains
injective when every family element differs from that value. -/
theorem finCases_injective_of_ne
    {α : Type} {t : ℕ} (a : α) (f : Fin t → α)
    (hneq : ∀ i, f i ≠ a) (hinj : Function.Injective f) :
    Function.Injective (Fin.cases a f) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          have h : a = f j := by simpa using hij
          exact False.elim ((hneq j) h.symm)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have h : f i = a := by simpa using hij
          exact False.elim ((hneq i) h)
      | succ j =>
          have h : f i = f j := by simpa using hij
          exact congrArg Fin.succ (hinj h)

/-- Any residue indicator differs from the unmodified base colour
if the residue is realized and 1 is nonzero in ZMod m. -/
theorem unorderedResidueExteriorType_ne_base
    (N t m : ℕ) (hm : 2 ≤ m)
    (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m)
    (hres : Function.Surjective (unorderedSubsetResidue hdiv))
    (i : Fin t) :
    unorderedResidueExteriorType hdiv base i ≠ base := by
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have hm1 := ZMod.one_eq_zero_iff.mp h
    omega
  obtain ⟨s, hs⟩ := hres (i.val : ZMod t)
  intro heq
  have hpoint := congrFun heq s
  have hbad : base s + (1 : ZMod m) = base s + 0 := by
    simpa [unorderedResidueExteriorType,
      unorderedResidueIndicator, hs] using hpoint
  exact hone (add_left_cancel hbad)

/-- A full family indexed by t+1 exterior labels: the base
colour and one perturbation for each residue. -/
def unorderedAllExteriorTypes
    {N t m : ℕ} (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m) :
    Fin (t + 1) → (RSubsets (ZMod N) t → ZMod m) :=
  Fin.cases base (fun i => unorderedResidueExteriorType hdiv base i)

theorem unorderedAllExteriorTypes_injective
    (N t m : ℕ) (hm : 2 ≤ m)
    (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m)
    (hres : Function.Surjective (unorderedSubsetResidue hdiv)) :
    Function.Injective (unorderedAllExteriorTypes hdiv base) :=
  finCases_injective_of_ne base
    (fun i => unorderedResidueExteriorType hdiv base i)
    (unorderedResidueExteriorType_ne_base N t m hm hdiv base hres)
    (unorderedResidueExteriorTypes_injective N t m hm hdiv base hres)

/-- Every one of these t+1 types obeys the same unit-translation
equivariance as the base. -/
theorem unorderedAllExteriorTypes_translate_one
    (N t m : ℕ) (hdiv : t ∣ N)
    (base : RSubsets (ZMod N) t → ZMod m)
    (hbase : ∀ s : RSubsets (ZMod N) t,
      base (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
        base s + 1)
    (i : Fin (t + 1)) (s : RSubsets (ZMod N) t) :
    unorderedAllExteriorTypes hdiv base i
        (permuteRSubset (orderedColourTranslationPerm (1 : ZMod N)) s) =
      unorderedAllExteriorTypes hdiv base i s + 1 := by
  cases i using Fin.cases with
  | zero => exact hbase s
  | succ i =>
      exact unorderedResidueExteriorType_translate_one
        N t m hdiv base hbase i s

end EPPAReducts.BoundedEquivalence

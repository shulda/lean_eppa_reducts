import EPPAReducts.BoundedEquivalence.OrderedCoreExteriorColour
import EPPAReducts.BoundedEquivalence.OrderedCyclicCore

/-!
# Distinguishing the actual exterior colours

In the explicit cyclic-core-plus-exterior colouring, replacing the
external vertex a_i in the i-th position by a different a_j changes
the positional correction from one to zero, while leaving the base
colour unchanged.

The remaining positions are populated by a *single fixed* injective
ordered core tuple; no noncanonical orbit representatives are needed.
This is the concrete exterior-type separation that an automorphism
fixing the old core and each unlabelled class will contradict.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Insert a specified exterior label into a fixed slot of an injective
core tuple, keeping every other core entry unchanged. -/
def orderedInsertExterior
    {N r : ℕ} (core : InjectiveTuples (ZMod N) r)
    (slot label : Fin r) :
    InjectiveTuples (Sum (ZMod N) (Fin r)) r := by
  classical
  refine ⟨fun j => if j = slot then Sum.inr label else
    Sum.inl (core.val j), ?_⟩
  intro j k h
  by_cases hj : j = slot
  · by_cases hk : k = slot
    · exact hj.trans hk.symm
    · simp [hj, hk] at h
  · by_cases hk : k = slot
    · simp [hj, hk] at h
    · apply core.property
      simpa [hj, hk] using h

@[simp] theorem orderedInsertExterior_at_slot
    {N r : ℕ} (core : InjectiveTuples (ZMod N) r)
    (slot label : Fin r) :
    (orderedInsertExterior core slot label).val slot =
      Sum.inr label := by
  simp [orderedInsertExterior]

@[simp] theorem orderedInsertExterior_at_ne
    {N r : ℕ} (core : InjectiveTuples (ZMod N) r)
    (slot label j : Fin r) (hj : j ≠ slot) :
    (orderedInsertExterior core slot label).val j =
      Sum.inl (core.val j) := by
  simp [orderedInsertExterior, hj]

/-- Exactly one possible external coordinate occurs, at slot; its
label matches the slot iff the positional correction is one. -/
theorem orderedExteriorCorrection_insert
    (m : ℕ) {N r : ℕ}
    (core : InjectiveTuples (ZMod N) r)
    (slot label : Fin r) :
    orderedExteriorCorrection m
      (orderedInsertExterior core slot label).val =
        if label = slot then 1 else 0 := by
  classical
  have hex :
      (∃ j : Fin r,
        (orderedInsertExterior core slot label).val j = Sum.inr j) ↔
        label = slot := by
    constructor
    · rintro ⟨j, hj⟩
      by_cases h : j = slot
      · subst j
        simpa [orderedInsertExterior] using hj
      · have hn :=
          orderedInsertExterior_at_ne core slot label j h
        rw [hn] at hj
        cases hj
    · intro h
      exact ⟨slot, by simpa [h] using
        (orderedInsertExterior_at_slot core slot label)⟩
  by_cases h : label = slot
  · have hh : ∃ j : Fin r,
        (orderedInsertExterior core slot label).val j = Sum.inr j :=
      hex.mpr h
    change
      (if ∃ j : Fin r,
        (orderedInsertExterior core slot label).val j = Sum.inr j
        then (1 : ZMod m) else 0) =
      (if label = slot then (1 : ZMod m) else 0)
    rw [if_pos hh, if_pos h]
  · have hh : ¬∃ j : Fin r,
        (orderedInsertExterior core slot label).val j = Sum.inr j :=
      fun hx => h (hex.mp hx)
    change
      (if ∃ j : Fin r,
        (orderedInsertExterior core slot label).val j = Sum.inr j
        then (1 : ZMod m) else 0) =
      (if label = slot then (1 : ZMod m) else 0)
    rw [if_neg hh, if_neg h]

/-- The base colour depends only on the core entries and the
exterior *position*, never on its exterior label. -/
theorem orderedCoreBase_insert_independent_label
    (m N r : ℕ) (hmN : m ∣ N) (hr : 1 < r)
    (core : InjectiveTuples (ZMod N) r)
    (slot a b : Fin r) :
    orderedCoreBase m N r hmN hr
      (orderedInsertExterior core slot a).val =
    orderedCoreBase m N r hmN hr
      (orderedInsertExterior core slot b).val := by
  classical
  let z : Fin r := ⟨0, Nat.zero_lt_of_lt hr⟩
  let o : Fin r := ⟨1, hr⟩
  by_cases hz : z = slot
  · have ho : o ≠ slot := by
      intro heq
      have hzo : z = o := hz.trans heq.symm
      exact Nat.zero_ne_one (congrArg Fin.val hzo)
    simp [orderedCoreBase, orderedInsertExterior, z, o, hz, ho]
  · simp [orderedCoreBase, orderedInsertExterior, z, hz]

/-- An external vertex whose label matches its insertion position
has a different colour from one with any other label, using exactly
the same core coordinates.  This works also for r=2. -/
theorem orderedCoreExteriorColour_distinct_at_slot
    (m N r : ℕ) (hmN : m ∣ N)
    (hm : 2 ≤ m) (hr : 1 < r)
    (core : InjectiveTuples (ZMod N) r)
    (slot label : Fin r) (hne : slot ≠ label) :
    orderedCoreExteriorColour m N r hmN hr
      (orderedInsertExterior core slot slot).val ≠
    orderedCoreExteriorColour m N r hmN hr
      (orderedInsertExterior core slot label).val := by
  have hb := orderedCoreBase_insert_independent_label
    m N r hmN hr core slot slot label
  have hc1 : orderedExteriorCorrection m
      (orderedInsertExterior core slot slot).val = 1 := by
    simpa using orderedExteriorCorrection_insert m core slot slot
  have hc0 : orderedExteriorCorrection m
      (orderedInsertExterior core slot label).val = 0 := by
    simpa [hne.symm] using
      orderedExteriorCorrection_insert m core slot label
  intro h
  change orderedCoreBase m N r hmN hr
      (orderedInsertExterior core slot slot).val +
        orderedExteriorCorrection m
          (orderedInsertExterior core slot slot).val =
    orderedCoreBase m N r hmN hr
      (orderedInsertExterior core slot label).val +
        orderedExteriorCorrection m
          (orderedInsertExterior core slot label).val at h
  rw [hb, hc1, hc0, add_zero] at h
  have h' :
      orderedCoreBase m N r hmN hr
        (orderedInsertExterior core slot label).val + 1 =
      orderedCoreBase m N r hmN hr
        (orderedInsertExterior core slot label).val + (0 : ZMod m) := by
    simpa only [add_zero] using h
  have hOne : (1 : ZMod m) = 0 := add_left_cancel h'
  have hM : m = 1 := ZMod.one_eq_zero_iff.mp hOne
  exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hm)) hM

/-- The concrete cyclic core ZMod(m*r) has an injective core tuple,
so these contrasting colours can be witnessed for every pair of
distinct exterior labels whenever r,m >= 2. -/
theorem orderedCyclicExteriorColour_distinct
    (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r)
    (slot label : Fin r) (hne : slot ≠ label) :
    ∃ core : InjectiveTuples (ZMod (m * r)) r,
      orderedCoreExteriorColour m (m * r) r
        (show m ∣ m * r from ⟨r, rfl⟩) (lt_of_lt_of_le (by decide : 1 < 2) hr)
        (orderedInsertExterior core slot slot).val ≠
      orderedCoreExteriorColour m (m * r) r
        (show m ∣ m * r from ⟨r, rfl⟩) (lt_of_lt_of_le (by decide : 1 < 2) hr)
        (orderedInsertExterior core slot label).val := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hrpos : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  obtain ⟨core⟩ := cyclicCoreInjectiveTuple_nonempty
    m r r hmpos hrpos (le_refl r)
  exact ⟨core, orderedCoreExteriorColour_distinct_at_slot
    m (m * r) r (show m ∣ m * r from ⟨r, rfl⟩) hm
    (lt_of_lt_of_le (by decide : 1 < 2) hr)
    core slot label hne⟩

end EPPAReducts.BoundedEquivalence

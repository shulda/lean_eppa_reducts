import EPPAReducts.BoundedEquivalence.OrderedCoreExteriorSupport
import EPPAReducts.BoundedEquivalence.OrderedTupleKernelPartial

/-!
# Genuine partial shifts on the cyclic core with one exterior vertex

For each exterior vertex a, restrict the permutation shifting the
cyclic core by one (and fixing all exterior vertices) to the induced
domain containing the core and a alone.  This produces a *literal*
HumanTargets.PartialBijection, rather than merely a map on colours.

The certified support lemma implies that all ordered injective
r-tuples from this domain increase their auxiliary colour by one.
Thus the partial shift preserves the unlabelled kernel relation.
-/

namespace EPPAReducts.BoundedEquivalence

open EPPAReducts.HumanTargets

/-- Inverse cyclic translation on core vertices, leaving all exterior
vertices untouched. -/
def orderedCoreUnshift {N r : ℕ}
    (v : Sum (ZMod N) (Fin r)) : Sum (ZMod N) (Fin r) :=
  match v with
  | .inl x => .inl (x - 1)
  | .inr a => .inr a

@[simp] theorem orderedCoreUnshift_shift {N r : ℕ}
    (v : Sum (ZMod N) (Fin r)) :
    orderedCoreUnshift (orderedCoreShift v) = v := by
  cases v <;> simp [orderedCoreUnshift, orderedCoreShift]

@[simp] theorem orderedCoreShift_unshift {N r : ℕ}
    (v : Sum (ZMod N) (Fin r)) :
    orderedCoreShift (orderedCoreUnshift v) = v := by
  cases v <;> simp [orderedCoreUnshift, orderedCoreShift]

/-- The finite vertex domain consisting of the full cyclic core and
one specified external vertex. -/
noncomputable def orderedCoreOne {N r : ℕ} [Fintype (ZMod N)]
    (a : Fin r) : Finset (Sum (ZMod N) (Fin r)) := by
  classical
  exact Finset.univ.filter
    (fun v => match v with
      | .inl _ => True
      | .inr j => j = a)

@[simp] theorem mem_orderedCoreOne_inl {N r : ℕ} [Fintype (ZMod N)]
    (a : Fin r) (x : ZMod N) :
    (Sum.inl x : Sum (ZMod N) (Fin r)) ∈ orderedCoreOne a := by
  classical
  simp [orderedCoreOne]

@[simp] theorem mem_orderedCoreOne_inr {N r : ℕ} [Fintype (ZMod N)]
    (a j : Fin r) :
    (Sum.inr j : Sum (ZMod N) (Fin r)) ∈ orderedCoreOne a ↔ j = a := by
  classical
  simp [orderedCoreOne]

theorem orderedCoreShift_mem_coreOne_iff {N r : ℕ} [Fintype (ZMod N)]
    (a : Fin r) (v : Sum (ZMod N) (Fin r)) :
    orderedCoreShift v ∈ orderedCoreOne a ↔ v ∈ orderedCoreOne a := by
  cases v with
  | inl x => simp
  | inr j => simp [orderedCoreShift]

theorem orderedCoreUnshift_mem_coreOne_iff {N r : ℕ} [Fintype (ZMod N)]
    (a : Fin r) (v : Sum (ZMod N) (Fin r)) :
    orderedCoreUnshift v ∈ orderedCoreOne a ↔ v ∈ orderedCoreOne a := by
  cases v with
  | inl x => simp [orderedCoreUnshift]
  | inr j => simp [orderedCoreUnshift]

/-- A genuine equivalence of induced vertex domains, acting by
translation on all cyclic-core vertices and fixing the exterior
vertex. -/
noncomputable def orderedCoreOneShiftEquiv {N r : ℕ}
    [Fintype (ZMod N)] (a : Fin r) :
    {v : Sum (ZMod N) (Fin r) // v ∈ orderedCoreOne a} ≃
      {v : Sum (ZMod N) (Fin r) // v ∈ orderedCoreOne a} where
  toFun v := ⟨orderedCoreShift v.val,
    (orderedCoreShift_mem_coreOne_iff a v.val).mpr v.property⟩
  invFun v := ⟨orderedCoreUnshift v.val,
    (orderedCoreUnshift_mem_coreOne_iff a v.val).mpr v.property⟩
  left_inv v := by
    apply Subtype.ext
    exact orderedCoreUnshift_shift v.val
  right_inv v := by
    apply Subtype.ext
    exact orderedCoreShift_unshift v.val

/-- The distinguished literal partial bijection of the finite
core-plus-r-exterior vertex structure. Its source and target are the
SAME induced subset: the cyclic core together with a. -/
noncomputable def orderedCoreOnePartialShift {N r : ℕ}
    [Fintype (ZMod N)] (a : Fin r) :
    PartialBijection (Sum (ZMod N) (Fin r)) where
  source := orderedCoreOne a
  target := orderedCoreOne a
  bijection := orderedCoreOneShiftEquiv a

@[simp] theorem orderedCoreOnePartialShift_apply {N r : ℕ}
    [Fintype (ZMod N)] (a : Fin r)
    (v : {v : Sum (ZMod N) (Fin r) // v ∈ orderedCoreOne a}) :
    ((orderedCoreOnePartialShift a).bijection v).val =
      orderedCoreShift v.val := rfl

/-- Every injective tuple supported on this partial map uses only
the core and its one specified exterior vertex. -/
theorem orderedCoreOneTuple_support {N r : ℕ}
    [Fintype (ZMod N)] (a : Fin r)
    (t : InjectiveTuples
      {v : Sum (ZMod N) (Fin r) // v ∈ orderedCoreOne a} r) :
    ∀ j k : Fin r, (t.val j).val = Sum.inr k → k = a := by
  intro j k h
  have ht : (t.val j).val ∈ orderedCoreOne a := (t.val j).property
  have hk : (Sum.inr k : Sum (ZMod N) (Fin r)) ∈
      orderedCoreOne a := by
    rw [← h]
    exact ht
  exact (mem_orderedCoreOne_inr a k).mp hk

/-- The concrete partial bijection on the old core and a fixed
external vertex increases all auxiliary tuple colours by one. -/
theorem orderedCoreOnePartialShift_colour_shift
    (m N r : ℕ) [Fintype (ZMod N)]
    (hmN : m ∣ N) (hr : 1 < r) (a : Fin r)
    (t : InjectiveTuples
      {v : Sum (ZMod N) (Fin r) //
        v ∈ (orderedCoreOnePartialShift a).source} r) :
    orderedCoreExteriorColour m N r hmN hr
      (fun j => ((orderedCoreOnePartialShift a).bijection (t.val j)).val) =
    orderedCoreExteriorColour m N r hmN hr
      (fun j => (t.val j).val) + 1 := by
  let raw : InjectiveTuples (Sum (ZMod N) (Fin r)) r :=
    mapInjectiveTuple (subtypeEmbedding (orderedCoreOne a)) t
  have hsup : ∀ j k : Fin r, raw.val j = Sum.inr k → k = a :=
    orderedCoreOneTuple_support a t
  have hs := orderedCoreExteriorColour_shift_of_one_external
    m N r hmN hr raw a hsup
  change orderedCoreExteriorColour m N r hmN hr
      (fun j => orderedCoreShift ((t.val j).val)) =
    orderedCoreExteriorColour m N r hmN hr
      (fun j => (t.val j).val) + 1
  exact hs

/-- Each core-plus-one-exterior shift is a genuine partial
automorphism of the UNLABELLED ordered tuple equivalence. -/
theorem orderedCoreOnePartialShift_isPartialAutomorphism
    (m N r : ℕ) [Fintype (ZMod N)]
    (hmN : m ∣ N) (hr : 1 < r) (a : Fin r) :
    IsOrderedTupleKernelPartialAutomorphism
      (fun t : InjectiveTuples (Sum (ZMod N) (Fin r)) r =>
        orderedCoreExteriorColour m N r hmN hr t.val)
      (orderedCoreOnePartialShift a) := by
  apply isOrderedTupleKernelPartialAutomorphism_of_shift
    (fun t : InjectiveTuples (Sum (ZMod N) (Fin r)) r =>
      orderedCoreExteriorColour m N r hmN hr t.val)
    (orderedCoreOnePartialShift a) (1 : ZMod m)
  intro t
  change orderedCoreExteriorColour m N r hmN hr
      (fun j => ((orderedCoreOnePartialShift a).bijection (t.val j)).val) =
    orderedCoreExteriorColour m N r hmN hr
      (fun j => (t.val j).val) + 1
  exact orderedCoreOnePartialShift_colour_shift m N r hmN hr a t

end EPPAReducts.BoundedEquivalence

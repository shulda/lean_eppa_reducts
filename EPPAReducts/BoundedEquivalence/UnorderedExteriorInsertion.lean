import EPPAReducts.BoundedEquivalence.UnorderedWitnessAPI

/-!
# Inserting one exterior vertex into an unordered subset

An unordered t-subset of a core, together with one exterior vertex,
is canonically an unordered (t+1)-subset. The transport lemma says
that a permutation fixing the embedded core pointwise and sending
one exterior vertex to another sends the corresponding enlarged
subsets to one another. This is required for exterior-type rigidity.
-/

namespace EPPAReducts.BoundedEquivalence

/-- Canonical inclusion of a core into a disjoint union. -/
def unorderedCoreInclusion {S E : Type} : S ↪ Sum S E :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Insert one exterior vertex into a core t-subset. -/
noncomputable def unorderedInsertExterior
    {S E : Type} {t : ℕ}
    (core : RSubsets S t) (i : E) :
    RSubsets (Sum S E) (t + 1) := by
  classical
  let s := core.val.map (unorderedCoreInclusion (S := S) (E := E))
  have hnot : (Sum.inr i : Sum S E) ∉ s := by
    intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp h
    cases hx
  refine ⟨insert (Sum.inr i) s, ?_⟩
  rw [Finset.card_insert_of_notMem hnot]
  simp [s, core.property]

/-- The carrier of the inserted subset is the literal insertion,
not merely an abstract isomorphic copy. -/
theorem unorderedInsertExterior_val
    {S E : Type} [DecidableEq S] [DecidableEq E]
    {t : ℕ} (core : RSubsets S t) (i : E) :
    (unorderedInsertExterior core i).val =
      insert (Sum.inr i)
        (core.val.map (unorderedCoreInclusion (S := S) (E := E))) := by
  classical
  rfl

/-- A pointwise core-fixing ambient permutation transporting one
exterior vertex transports every corresponding core-plus-exterior
unordered subset, with no ordering of its vertices. -/
theorem unorderedInsertExterior_transport
    {S E W : Type} {t : ℕ}
    (ι : Sum S E ↪ W) (g : Equiv.Perm W)
    (hcore : ∀ s : S, g (ι (Sum.inl s)) = ι (Sum.inl s))
    (i j : E)
    (hij : g (ι (Sum.inr i)) = ι (Sum.inr j))
    (core : RSubsets S t) :
    permuteRSubset g
      (mapRSubset ι (unorderedInsertExterior core i)) =
        mapRSubset ι (unorderedInsertExterior core j) := by
  classical
  apply Subtype.ext
  change
    ((unorderedInsertExterior core i).val.map ι).map
      (⟨g, g.injective⟩ : W ↪ W) =
    (unorderedInsertExterior core j).val.map ι
  rw [unorderedInsertExterior_val core i,
      unorderedInsertExterior_val core j]
  simp only [Finset.map_insert]
  rw [hij]
  congr 1
  simp only [Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro x
  exact hcore x

end EPPAReducts.BoundedEquivalence

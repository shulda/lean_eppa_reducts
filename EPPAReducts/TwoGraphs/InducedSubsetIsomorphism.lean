import EPPAReducts.TwoGraphs.FiniteValuationEPPA

/-!
# Isomorphism classes of induced sub-two-graphs

Two finite vertex subsets are related when their induced two-graph
structures are isomorphic.  This defines an equivalence relation
on Finset V, using the literal author-approved TwoGraph triple
predicate, and hence a quotient of the family of induced substructures.

Choosing a canonical representative for each quotient class is
the first independent ingredient of generic coherentisation.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Two induced subsets of the same two-graph are isomorphic. -/
def IsomorphicInducedSubsets {V : Type}
    (A : TwoGraph V) (s t : Finset V) : Prop :=
  ∃ u : {v : V // v ∈ s} ≃ {v : V // v ∈ t},
    ∀ x y z : {v : V // v ∈ s},
      A.isTriple (triple x.val y.val z.val) =
        A.isTriple (triple (u x).val (u y).val (u z).val)

/-- The identity map witnesses reflexivity. -/
theorem isomorphicInducedSubsets_refl {V : Type}
    (A : TwoGraph V) (s : Finset V) :
    IsomorphicInducedSubsets A s s := by
  exact ⟨Equiv.refl _, fun _ _ _ => rfl⟩

/-- Inverting an induced-substructure isomorphism preserves triples. -/
theorem isomorphicInducedSubsets_symm {V : Type}
    (A : TwoGraph V) (s t : Finset V)
    (h : IsomorphicInducedSubsets A s t) :
    IsomorphicInducedSubsets A t s := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u.symm, ?_⟩
  intro x y z
  have hxyz := hu (u.symm x) (u.symm y) (u.symm z)
  simpa only [Equiv.apply_symm_apply] using hxyz.symm

/-- Composing two induced-substructure isomorphisms preserves triples. -/
theorem isomorphicInducedSubsets_trans {V : Type}
    (A : TwoGraph V) (s t u : Finset V)
    (hst : IsomorphicInducedSubsets A s t)
    (htu : IsomorphicInducedSubsets A t u) :
    IsomorphicInducedSubsets A s u := by
  obtain ⟨e, he⟩ := hst
  obtain ⟨f, hf⟩ := htu
  refine ⟨e.trans f, ?_⟩
  intro x y z
  exact (he x y z).trans (hf (e x) (e y) (e z))

/-- Genuine setoid of induced two-graph isomorphism classes. -/
def inducedSubsetIsoSetoid {V : Type}
    (A : TwoGraph V) : Setoid (Finset V) where
  r := IsomorphicInducedSubsets A
  iseqv := {
    refl := isomorphicInducedSubsets_refl A
    symm := isomorphicInducedSubsets_symm A
    trans := isomorphicInducedSubsets_trans A
  }

/-- The quotient of finite induced substructures by their
unlabelled two-graph isomorphism types. -/
abbrev InducedSubsetIsoClass {V : Type} (A : TwoGraph V) :=
  Quotient (inducedSubsetIsoSetoid A)

/-- Choose one vertex subset representing each isomorphism class. -/
noncomputable def canonicalInducedSubset {V : Type}
    (A : TwoGraph V) (s : Finset V) : Finset V :=
  Quotient.out (Quotient.mk (inducedSubsetIsoSetoid A) s)

/-- Isomorphic source and target subsets have exactly the same
chosen canonical representative, not merely isomorphic ones. -/
theorem canonicalInducedSubset_eq_of_iso {V : Type}
    (A : TwoGraph V) (s t : Finset V)
    (hst : IsomorphicInducedSubsets A s t) :
    canonicalInducedSubset A s = canonicalInducedSubset A t := by
  exact congrArg Quotient.out (Quotient.sound hst)

end EPPAReducts.TwoGraphs

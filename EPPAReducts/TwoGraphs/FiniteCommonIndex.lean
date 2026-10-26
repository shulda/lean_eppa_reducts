import EPPAReducts.TwoGraphs.IndexedRootedTransversal
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Fintype

/-!
# A finite common-multiple index carrier

The final existence theorem does not need the *optimal* common
multiple lcm(1,...,n): the explicit index set Fin (n!) also works.
This elementary alternative is formalized independently so that the
final EPPA construction can use whichever cardinal arithmetic is
simpler without modifying the accepted mathematical theorem target.

For every finite V, the standard equivalence V ≃ Fin |V| embeds V
into Fin (|V|!).  Every nonempty induced subset of V has cardinality
dividing |V|!.  This includes the small-cardinality boundary cases.
-/

namespace EPPAReducts.TwoGraphs

/-- The canonical injection of a finite type into the index carrier
of factorial size (through Fin(card V)). -/
noncomputable def factorialIndexEmbedding
    {V : Type} [Fintype V] :
    V ↪ Fin (Nat.factorial (Fintype.card V)) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨fun v => Fin.castLE (Nat.self_le_factorial _) (e v), ?_⟩
  intro v w h
  apply e.injective
  apply Fin.ext
  simpa only [Fin.castLE] using congrArg Fin.val h

/-- Each nonempty induced vertex subset has size dividing the
factorial index cardinality.  This will feed directly into the
already-certified divisible-transversal subgroup section. -/
theorem card_nonempty_subtype_dvd_factorial
    {V : Type} [Fintype V]
    (s : Finset V) (hs : s.Nonempty) :
    Fintype.card {v : V // v ∈ s} ∣ Nat.factorial (Fintype.card V) := by
  classical
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  have hle : s.card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  have hdiv : s.card ∣ Nat.factorial (Fintype.card V) :=
    Nat.dvd_factorial hpos hle
  simpa only [Fintype.card_coe] using hdiv

/-- The subgroup-section divisibility statement on the actual finite
index type chosen above. -/
theorem card_nonempty_subtype_dvd_index
    {V : Type} [Fintype V]
    (s : Finset V) (hs : s.Nonempty) :
    Fintype.card {v : V // v ∈ s} ∣
      Fintype.card (Fin (Nat.factorial (Fintype.card V))) := by
  simpa using card_nonempty_subtype_dvd_factorial s hs

end EPPAReducts.TwoGraphs

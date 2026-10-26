import EPPAReducts.TwoGraphs.EmbeddedSubtypePreservation

/-!
# Simultaneous subgroup lifts for induced sub-two-graphs

Given an actual induced copy of A inside the valuation two-graph C_X,
each nonempty induced subset s whose size divides |X| admits one
simultaneous homomorphic extension of *all* automorphisms of A|s.

The automorphism-preservation premise is stated using the literal
HumanTargets.TwoGraph triple relation on the original carrier V.
The proof uses the already certified embedded-subtype preservation
bridge and divisible-transversal subgroup lift; no extra structural
hypothesis is imposed on A.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Every automorphism group of a nonempty induced sub-two-graph
has simultaneous identity- and composition-preserving extensions in
C_X, provided its cardinality divides the index-set size. -/
theorem exists_inducedSubtype_coherentLift
    {V X : Type} [Fintype V] [Fintype X]
    [DecidableEq X] [DecidableEq (ValuationVertex X)]
    (A : TwoGraph V) (ι : V ↪ X)
    (χ : V → Valuation X)
    (hind : IsInducedTwoGraphEmbedding A (valuationTwoGraph X)
      (indexedTransversalEmbedding ι χ))
    (s : Finset V) (hs : s.Nonempty)
    (hdiv : Fintype.card {v : V // v ∈ s} ∣ Fintype.card X) :
    ∃ lift :
      (p : Equiv.Perm {v : V // v ∈ s}) →
      (∀ x y z : {v : V // v ∈ s},
        A.isTriple (triple x.val y.val z.val) =
          A.isTriple (triple (p x).val (p y).val (p z).val)) →
      Equiv.Perm (ValuationVertex X),
      (∀ p hp,
        IsTwoGraphAutomorphism (valuationTwoGraph X) (lift p hp)) ∧
      (∀ p hp d,
        lift p hp (ι d.val, valuationClass (χ d.val)) =
          (ι (p d).val, valuationClass (χ (p d).val))) ∧
      (lift (Equiv.refl _) (fun _ _ _ => rfl) =
        Equiv.refl (ValuationVertex X)) ∧
      (∀ p q
        (hp : ∀ x y z : {v : V // v ∈ s},
          A.isTriple (triple x.val y.val z.val) =
            A.isTriple (triple (p x).val (p y).val (p z).val))
        (hq : ∀ x y z : {v : V // v ∈ s},
          A.isTriple (triple x.val y.val z.val) =
            A.isTriple (triple (q x).val (q y).val (q z).val)),
        (lift p hp).trans (lift q hq) =
          lift (p.trans q)
            (fun x y z => (hp x y z).trans (hq (p x) (p y) (p z)))) := by
  classical
  obtain ⟨d, hd⟩ := hs
  letI : Nonempty {v : V // v ∈ s} := ⟨⟨d, hd⟩⟩
  let ιs : {v : V // v ∈ s} ↪ X :=
    (subtypeEmbedding s).trans ι
  let χs : {v : V // v ∈ s} → Valuation X :=
    fun v => χ v.val
  have convert (p : Equiv.Perm {v : V // v ∈ s})
      (hp : ∀ x y z : {v : V // v ∈ s},
        A.isTriple (triple x.val y.val z.val) =
          A.isTriple (triple (p x).val (p y).val (p z).val)) :
      PreservesEmbeddedTransversal ιs χs p :=
    preservesEmbeddedTransversal_of_inducedSubtype
      A ι χ hind s p hp
  obtain ⟨lift0, hauto, hmap, hid, hcomp⟩ :=
    exists_divisibleTransversal_coherentLift ιs hdiv χs
  let lift :
      (p : Equiv.Perm {v : V // v ∈ s}) →
      (∀ x y z : {v : V // v ∈ s},
        A.isTriple (triple x.val y.val z.val) =
          A.isTriple (triple (p x).val (p y).val (p z).val)) →
      Equiv.Perm (ValuationVertex X) :=
    fun p hp => lift0 p (convert p hp)
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hauto p (convert p hp)
  · intro p hp v
    exact hmap p (convert p hp) v
  · change lift0 (Equiv.refl _) _ = Equiv.refl (ValuationVertex X)
    exact hid
  · intro p q hp hq
    change (lift0 p (convert p hp)).trans
        (lift0 q (convert q hq)) =
      lift0 (p.trans q) _
    exact hcomp p q (convert p hp) (convert q hq)

end EPPAReducts.TwoGraphs

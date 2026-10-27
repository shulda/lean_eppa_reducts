import EPPAReducts.TwoGraphs.RootingPartialLift

/-!
# Normalizing the two unlabelled colours of a partial automorphism

Preservation of equality of two Boolean class labels forces either
preservation of the two labels or their *global* interchange. The
proof works also when the domain has no pairs or only one pair, and
does not add a colour name to the structure.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

/-- Two Boolean presentations of the same unlabelled equivalence
differ by one global XOR bit, even if their domain is empty. -/
theorem boolKernelHasGlobalShift
    {X : Type} (f g : X → Bool)
    (h : ∀ x y : X, f x = f y ↔ g x = g y) :
    ∃ δ : Bool, ∀ x, g x = Bool.xor (f x) δ := by
  classical
  by_cases hn : Nonempty X
  · obtain ⟨x₀⟩ := hn
    refine ⟨Bool.xor (f x₀) (g x₀), ?_⟩
    intro x
    have hh := h x x₀
    cases hf : f x <;> cases hf0 : f x₀ <;>
      cases hg : g x <;> cases hg0 : g x₀ <;>
      simp_all [Bool.xor]
  · refine ⟨false, ?_⟩
    intro x
    exact False.elim (hn ⟨x⟩)

/-- Every actual partial automorphism of a pair-class equivalence
induces a single XOR bit on all old pairs in its domain. -/
theorem pairPartialHasGlobalShift
    {V : Type} (A : GraphModuloComplementation V)
    (c : UnorderedPairs V → Bool)
    (hc : ∀ e f : UnorderedPairs V,
      A.sameClass.r e f ↔ c e = c f)
    (p : PartialBijection V)
    (hp : IsPairPartialAutomorphism A p) :
    ∃ δ : Bool,
      ∀ e : UnorderedPairs {v : V // v ∈ p.source},
        c (mapPair (equivThenEmbedding p.bijection
          (subtypeEmbedding p.target)) e) =
        Bool.xor
          (c (mapPair (subtypeEmbedding p.source) e)) δ := by
  let f : UnorderedPairs {v : V // v ∈ p.source} → Bool :=
    fun e => c (mapPair (subtypeEmbedding p.source) e)
  let g : UnorderedPairs {v : V // v ∈ p.source} → Bool :=
    fun e => c (mapPair (equivThenEmbedding p.bijection
      (subtypeEmbedding p.target)) e)
  have hkernel : ∀ e e' : UnorderedPairs {v : V // v ∈ p.source},
      f e = f e' ↔ g e = g e' := by
    intro e e'
    exact ((hc _ _).symm).trans ((hp e e').trans (hc _ _))
  exact boolKernelHasGlobalShift f g hkernel

end EPPAReducts.TwoGraphs

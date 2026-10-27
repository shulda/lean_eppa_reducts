import EPPAReducts.TwoGraphs.RootShadowInduced

/-!
# Restricting a root-fixing automorphism to its graph shadow

A genuine automorphism of an unlabelled triple equivalence fixing
the distinguished root induces a genuine automorphism of its rooted
pair-class shadow. The conclusion does not fix any numerical class
name, so it permits the global complementing action.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

variable {W V : Type}

/-- Restrict a permutation fixing a root to the remaining vertices. -/
noncomputable def restrictAutToOutside
    (o : W) (g : Equiv.Perm W) (hfix : g o = o) :
    Equiv.Perm (OutsideRoot o) where
  toFun := fun x => ⟨g x.val, by
    intro h
    exact x.property (g.injective (h.trans hfix.symm))⟩
  invFun := fun x => ⟨g.symm x.val, by
    intro h
    apply x.property
    calc
      x.val = g (g.symm x.val) := (g.apply_symm_apply _).symm
      _ = g o := congrArg g h
      _ = o := hfix⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp

/-- Rooted unordered triples commute with a root-fixing permutation. -/
theorem tripleAboveRoot_transport
    (o : W) (g : Equiv.Perm W) (hfix : g o = o)
    (e : UnorderedPairs (OutsideRoot o)) :
    permuteRSubset g (tripleAboveRoot o e) =
      tripleAboveRoot o
        (mapPair (embeddingOfEquiv (restrictAutToOutside o g hfix)) e) := by
  classical
  rcases e with ⟨s, hs⟩
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hs
  subst s
  apply Subtype.ext
  simp [permuteRSubset, tripleAboveRoot, mapPair,
    embeddingOfEquiv, restrictAutToOutside, outsideEmbedding, hfix]

/-- A root-fixing triple-class automorphism genuinely preserves
the equality of classes in the graph shadow. -/
theorem restrictAutToOutside_isPairAutomorphism
    (C : TwoGraphModuloComplementation W)
    (o : W) (g : Equiv.Perm W) (hfix : g o = o)
    (hg : IsTripleClassAutomorphism C g) :
    IsPairAutomorphism (shadowAtRoot C o)
      (restrictAutToOutside o g hfix) := by
  intro e f
  change C.sameClass.r (tripleAboveRoot o e) (tripleAboveRoot o f) ↔
    C.sameClass.r
      (tripleAboveRoot o
        (mapPair (embeddingOfEquiv (restrictAutToOutside o g hfix)) e))
      (tripleAboveRoot o
        (mapPair (embeddingOfEquiv (restrictAutToOutside o g hfix)) f))
  rw [← tripleAboveRoot_transport o g hfix e,
      ← tripleAboveRoot_transport o g hfix f]
  exact hg (tripleAboveRoot o e) (tripleAboveRoot o f)

/-- An extension of the lifted root-fixing partial bijection must
fix the new root. -/
theorem extends_liftRootPartial_fixesRoot
    (ι : Option V ↪ W) (p : PartialBijection V)
    (g : Equiv.Perm W)
    (hg : Extends ι (liftRootPartial p) g) :
    g (ι none) = ι none := by
  calc
    g (ι none) =
        ι (((liftRootPartial p).bijection
          ⟨none, mem_rootedSupport_none p.source⟩).val) :=
      hg none (mem_rootedSupport_none p.source)
    _ = ι none := by rw [liftRootPartial_root]

/-- Restriction of the full rooted extension extends the original
partial bijection along the shadow embedding. -/
theorem restrictAutToOutside_extendsOld
    (ι : Option V ↪ W) (p : PartialBijection V)
    (g : Equiv.Perm W)
    (hg : Extends ι (liftRootPartial p) g) :
    Extends (shadowEmbedding ι) p
      (restrictAutToOutside (ι none) g
        (extends_liftRootPartial_fixesRoot ι p g hg)) := by
  intro x hx
  apply Subtype.ext
  change g (ι (some x)) =
    ι (some ((p.bijection ⟨x, hx⟩).val))
  calc
    g (ι (some x)) =
        ι (((liftRootPartial p).bijection
          ⟨some x, (mem_rootedSupport_some p.source x).mpr hx⟩).val) :=
      hg (some x) ((mem_rootedSupport_some p.source x).mpr hx)
    _ = ι (some ((p.bijection ⟨x, hx⟩).val)) := by
      rw [liftRootPartial_old]

end EPPAReducts.TwoGraphs

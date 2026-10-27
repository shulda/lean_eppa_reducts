import EPPAReducts.TwoGraphs.RootingColourShift

/-!
# Removing the fixed root from a triple-class equivalence

Every unlabelled two-graph-modulo-complementation structure, with a
distinguished root, canonically induces an unlabelled pair equivalence
on the remaining vertices. A chosen representative is used only as
an existence witness that there are at most two classes.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets
open EPPAReducts.BoundedEquivalence

variable {W V : Type}

/-- The vertices different from a chosen root. -/
abbrev OutsideRoot (o : W) := {w : W // w ≠ o}

/-- Canonical injection from the carrier with its root removed. -/
def outsideEmbedding (o : W) : OutsideRoot o ↪ W :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Insert the fixed root into an unordered pair of non-root vertices. -/
noncomputable def tripleAboveRoot
    (o : W) (e : UnorderedPairs (OutsideRoot o)) :
    UnorderedTriples W := by
  classical
  have hnot : o ∉ e.val.map (outsideEmbedding o) := by
    intro ho
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp ho
    exact x.property hx
  refine ⟨insert o (e.val.map (outsideEmbedding o)), ?_⟩
  simp [hnot, e.property]

/-- The root shadow is a genuine graph modulo complementation.
This definition never selects a named triple class in the language. -/
noncomputable def shadowAtRoot
    (C : TwoGraphModuloComplementation W) (o : W) :
    GraphModuloComplementation (OutsideRoot o) := by
  classical
  refine {
    sameClass := {
      r := fun e f => C.sameClass.r (tripleAboveRoot o e) (tripleAboveRoot o f)
      iseqv := ⟨(by intro e; exact C.sameClass.iseqv.refl _),
        (by intro e f h; exact C.sameClass.iseqv.symm h),
        (by intro e f g h k; exact C.sameClass.iseqv.trans h k)⟩
    }
    atMostTwoClasses := ?_
  }
  obtain ⟨T, hT⟩ := C.representative
  refine ⟨fun e => T.isTriple (tripleAboveRoot o e).val, ?_⟩
  intro e f
  exact hT (tripleAboveRoot o e) (tripleAboveRoot o f)

/-- The restriction of a rooted induced embedding of Option V avoids
the distinguished root and therefore lands in the root shadow. -/
def shadowEmbedding (ι : Option V ↪ W) :
    V ↪ OutsideRoot (ι none) where
  toFun := fun v => ⟨ι (some v), by
    intro heq
    have h := ι.injective heq
    cases h⟩
  inj' := by
    intro a b h
    have hab : ι (some a) = ι (some b) :=
      congrArg Subtype.val h
    exact Option.some.inj (ι.injective hab)

end EPPAReducts.TwoGraphs

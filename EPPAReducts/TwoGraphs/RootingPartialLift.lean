import EPPAReducts.TwoGraphs.RootedTripleKernel

/-!
# Literal star-fixed partial bijections for the rooting reduction

Given an old partial vertex bijection p:D→E, adjoin a fresh root
to both domains and fix it. This constructs a genuine
HumanTargets.PartialBijection on the enlarged carrier, with no
unverified totalization of p.
-/

namespace EPPAReducts.TwoGraphs

open EPPAReducts.HumanTargets

variable {V : Type}

private def someEmbedding : V ↪ Option V :=
  ⟨some, by intro a b h; exact Option.some.inj h⟩

/-- The root and the old vertices in the chosen finite domain. -/
noncomputable def rootedSupport (D : Finset V) : Finset (Option V) := by
  classical
  exact insert none (D.map someEmbedding)

@[simp] theorem mem_rootedSupport_none (D : Finset V) :
    none ∈ rootedSupport D := by
  classical
  simp [rootedSupport]

@[simp] theorem mem_rootedSupport_some (D : Finset V) (v : V) :
    some v ∈ rootedSupport D ↔ v ∈ D := by
  classical
  simp [rootedSupport, someEmbedding]

/-- An actual equivalence of the subtype of the rooted domain
with an option of the old subtype. -/
noncomputable def rootedSupportEquiv (D : Finset V) :
    {u : Option V // u ∈ rootedSupport D} ≃
      Option {v : V // v ∈ D} := by
  classical
  refine {
    toFun := ?_
    invFun := ?_
    left_inv := ?_
    right_inv := ?_
  }
  · intro u
    cases u with
    | mk none h => exact none
    | mk (some v) h =>
        exact some ⟨v, (mem_rootedSupport_some D v).mp h⟩
  · intro u
    cases u with
    | none =>
        exact ⟨none, mem_rootedSupport_none D⟩
    | some v =>
        exact ⟨some v.val, (mem_rootedSupport_some D v.val).mpr v.property⟩
  · rintro ⟨u, hu⟩
    cases u with
    | none => rfl
    | some v =>
        apply Subtype.ext
        rfl
  · intro u
    cases u with
    | none => rfl
    | some v =>
        congr 1
        apply Subtype.ext
        rfl

/-- Lift an ordinary equiv to the corresponding equiv on Option. -/
def optionCongrEquiv {X Y : Type} (e : X ≃ Y) :
    Option X ≃ Option Y where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

/-- Fix the new root while acting by p on the old partial domain. -/
noncomputable def liftRootPartial (p : PartialBijection V) :
    PartialBijection (Option V) where
  source := rootedSupport p.source
  target := rootedSupport p.target
  bijection :=
    (rootedSupportEquiv p.source).trans
      ((optionCongrEquiv p.bijection).trans
        (rootedSupportEquiv p.target).symm)

/-- The lifted partial map fixes the added root. -/
@[simp] theorem liftRootPartial_root (p : PartialBijection V) :
    ((liftRootPartial p).bijection
      ⟨none, mem_rootedSupport_none p.source⟩).val = none := by
  rfl

/-- It acts on each old domain vertex exactly as p does. -/
@[simp] theorem liftRootPartial_old
    (p : PartialBijection V) (x : V) (hx : x ∈ p.source) :
    ((liftRootPartial p).bijection
      ⟨some x, (mem_rootedSupport_some p.source x).mpr hx⟩).val =
      some ((p.bijection ⟨x, hx⟩).val) := by
  rfl

end EPPAReducts.TwoGraphs

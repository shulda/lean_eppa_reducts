import EPPAReducts.BoundedEquivalence.CosetOrbitIncidence

/-!
# Disjoint subgroup orbits give distinct twisted incidence pairs

A set of pairwise orbit-inequivalent representatives indexes a
disjoint family of coset fixed-point incidences. Forgetting the orbit
tag is therefore injective. This is the finiteness-free combinatorial
step preceding the cardinal bound.
-/

namespace EPPAReducts.BoundedEquivalence

universe u

/-- Label each twisted incidence by a chosen orbit representative. -/
abbrev OrbitTaggedIncidence {Ω : Type u}
    (L : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (R : Finset Ω) :=
  Σ r : {x : Ω // x ∈ R},
    Σ y : MulAction.orbit L r.val,
      {l : L // l.val (g y.val) = y.val}

/-- The full type of twisted fixed-point incidences. -/
abbrev CosetFixedIncidence {Ω : Type u}
    (L : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω) :=
  Σ l : L, {y : Ω // l.val (g y) = y}

/-- Different representatives belong to different subgroup orbits,
so an incidence remembers its orbit label uniquely. -/
noncomputable def orbitTaggedIncidenceEmbedding
    {Ω : Type u}
    (L : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (R : Finset Ω)
    (hsep : ∀ (x y : Ω), x ∈ R → y ∈ R →
      (∃ a : L, a.val x = y) → x = y) :
    OrbitTaggedIncidence L g R ↪ CosetFixedIncidence L g where
  toFun p := ⟨p.2.2.val, ⟨p.2.1.val, p.2.2.property⟩⟩
  inj' := by
    intro p q hpq
    rcases p with ⟨rp, yp, lp⟩
    rcases q with ⟨rq, yq, lq⟩
    have hz : yp.val = yq.val := by
      exact congrArg (fun t : CosetFixedIncidence L g => t.2.val) hpq
    have horbit : ∃ a : L, a.val rp.val = rq.val := by
      obtain ⟨a, ha⟩ := yp.property
      obtain ⟨b, hb⟩ := yq.property
      have ha' : a.val rp.val = yp.val := by
        change a.val rp.val = yp.val at ha
        exact ha
      have hb' : b.val rq.val = yq.val := by
        change b.val rq.val = yq.val at hb
        exact hb
      refine ⟨b⁻¹ * a, ?_⟩
      calc
        (b⁻¹ * a).val rp.val = b.val.symm (a.val rp.val) := by
          simp [Equiv.Perm.mul_apply]
        _ = b.val.symm yp.val := by rw [ha']
        _ = b.val.symm yq.val := by rw [hz]
        _ = rq.val := by rw [← hb']; simp
    have hr : rp = rq :=
      Subtype.ext (hsep rp.val rq.val rp.property rq.property horbit)
    cases hr
    have hy : yp = yq := Subtype.ext hz
    cases hy
    have hl : lp = lq := by
      apply Subtype.ext
      exact congrArg (fun t : CosetFixedIncidence L g => t.1) hpq
    cases hl
    rfl

end EPPAReducts.BoundedEquivalence

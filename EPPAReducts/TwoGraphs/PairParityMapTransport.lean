import EPPAReducts.TwoGraphs.PairTriangleTwoGraph
import EPPAReducts.TwoGraphs.GaugeParityIdentity

/-!
# Triple-parity transport along vertex injections

The Boolean sum of the three unordered edge colours commutes with
injective transport of the vertices. Consequently a uniform F₂ edge
shift plus a vertex gauge induces exactly a uniform triple-parity shift.
This is the finite-set transport bridge for the rooting reduction.
-/

namespace EPPAReducts.TwoGraphs

/-- The parity of an image of three vertices is the triangle sum of
the corresponding three edge colours. -/
theorem pairParityTriple_map_three
    {X Y : Type}
    (c : Finset Y → Bool) (ι : X ↪ Y)
    (x y z : X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    boolBit (pairParityTriple c
      (({x, y, z} : Finset X).map ι)) =
      pairTriangleSum
        (fun u v : X => boolBit (c {ι u, ι v})) x y z := by
  classical
  have hm :
      (({x, y, z} : Finset X).map ι) =
        ({ι x, ι y, ι z} : Finset Y) := by
    simp
  rw [hm]
  change boolBit (pairParityTriple c ({ι x, ι y, ι z} : Finset Y)) =
    boolBit (c {ι x, ι y}) +
      boolBit (c {ι x, ι z}) +
      boolBit (c {ι y, ι z})
  exact boolBit_pairParityTriple_three c (ι x) (ι y) (ι z)
    (ι.injective.ne hxy) (ι.injective.ne hxz) (ι.injective.ne hyz)

/-- If the pair colours of the images of every distinct pair differ
by a constant plus two vertex-gauge terms, then the parity of every
three-element subset differs by exactly that same constant. -/
theorem pairParityTriple_map_gauge
    {X Y : Type}
    (c : Finset Y → Bool) (src dst : X ↪ Y)
    (δ : ZMod 2) (f : X → ZMod 2)
    (hpair : ∀ x y : X, x ≠ y →
      boolBit (c {dst x, dst y}) =
        boolBit (c {src x, src y}) + δ + f x + f y)
    (s : Finset X) (hs : s.card = 3) :
    boolBit (pairParityTriple c (s.map dst)) =
      boolBit (pairParityTriple c (s.map src)) + δ := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
    Finset.card_eq_three.mp hs
  rw [pairParityTriple_map_three c dst x y z hxy hxz hyz,
    pairParityTriple_map_three c src x y z hxy hxz hyz]
  exact pairTriangleSum_gaugeShift
    (fun u v : X => boolBit (c {src u, src v}))
    (fun u v : X => boolBit (c {dst u, dst v}))
    δ f hpair x y z hxy hxz hyz

end EPPAReducts.TwoGraphs

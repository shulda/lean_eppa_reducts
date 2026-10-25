import EPPAReducts.TwoGraphs.FourSubsetEnumeration
import Mathlib.Data.Bool.Basic

/-!
# Even cardinality of four Boolean-marked objects

This is the finite arithmetic bridge used to turn the four-point XOR
equation into the *literal cardinality-mod-two* condition in the
approved human-readable TwoGraph definition.
-/

namespace EPPAReducts.TwoGraphs

universe u
variable {V : Type u} [DecidableEq V]

/-- Among four pairwise distinct objects, an even number are marked
if and only if the XOR of their Boolean marks is false. -/
theorem four_filter_even_iff_xor
    (f : V → Bool) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ((({a, b, c, d} : Finset V).filter
        (fun x => f x = true)).card % 2 = 0) ↔
      Bool.xor (Bool.xor (Bool.xor (f a) (f b)) (f c)) (f d) = false := by
  classical
  cases ha : f a <;> cases hb : f b <;>
    cases hc : f c <;> cases hd : f d <;>
    simp only [Finset.filter_insert, Finset.filter_singleton] <;>
    simp [ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd]

end EPPAReducts.TwoGraphs

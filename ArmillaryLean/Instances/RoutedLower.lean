module

public import ArmillaryLean.Certificates.Stabilizer
public import ArmillaryLean.Instances.Routed

@[expose] public section

/-!
# The six-overlap criterion for concrete Armillary checks

The generic CSS reduction applies to the routed rows with exactly twelve
entries. A lower certificate only needs to test supports that meet each
stabilizer row in at most six data coordinates.
-/

namespace ArmillaryLean.Routed

open ArmillaryLean.Stabilizer (RowReduced support)
open Qatlib.Concepts.CodingDecoding.CssTesters (bitWeight)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)
open Qatlib.Concepts.CodeCert.PermBlocks (matRowWt permBlocks_rwt)
open scoped Matrix

variable {p q : ℕ} [NeZero p]

/-- The twelve coordinates reached by a stabilizer row, one per data block. -/
def neighbors (a : ArmParam p q) (groups : Fin 3 → Fin 12) (r : Check p q) :
    Finset (Coord p q) :=
  Finset.univ.image fun b => (b, armEff a (groups r.1) b r.2)

/-- The routed neighborhood is exactly the support of the corresponding row. -/
theorem support_row (a : ArmParam p q) (groups : Fin 3 → Fin 12) (r : Check p q) :
    support (checks a groups r) = neighbors a groups r := by
  ext v
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
    neighbors, Finset.mem_image]
  change (if armEff a (groups r.1) v.1 r.2 = v.2 then (1 : ZMod 2) else 0) ≠ 0 ↔
    ∃ b : Fin 12, (b, armEff a (groups r.1) b r.2) = v
  constructor
  · intro h
    by_contra hnot
    have hv : armEff a (groups r.1) v.1 r.2 ≠ v.2 := by
      intro he
      exact hnot ⟨v.1, Prod.ext rfl he⟩
    exact h (ite_eq_right hv)
  · rintro ⟨b, rfl⟩
    rw [ite_eq_left rfl]
    decide

/-- Every routed stabilizer row has binary weight twelve. -/
theorem row_weight (a : ArmParam p q) (groups : Fin 3 → Fin 12) (r : Check p q) :
    bitWeight (checks a groups r) = 12 := by
  have hb : ∀ b : ZMod 2, b ≠ 0 ↔ b = 1 := by decide
  simp only [bitWeight, hb]
  change matRowWt (checks a groups) r = 12
  simpa [checks] using
    (permBlocks_rwt (K := ZMod 2) (fun i => armEff a (groups i)) r.1 r.2)

/-- For routed stabilizers, row reduction means at most six overlaps per row. -/
theorem row_reduced_iff (a : ArmParam p q) (groups : Fin 3 → Fin 12) (v : Coord p q → ZMod 2) :
    RowReduced (checks a groups) v ↔
      ∀ r, ((support v) ∩ neighbors a groups r).card ≤ 6 := by
  simp only [RowReduced, support_row, row_weight]
  constructor <;> intro h r <;> have hr := h r <;> omega

/-- Two six-overlap exclusions at the target weight give the routed CSS lower bound. -/
theorem distance_ge_of_six (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (c : CssData (Coord p q) (Check p q) (Check p q))
    (hx : c.hX = checks a x) (hz : c.hZ = checks a z) (d : ℕ)
    (xCert : ∀ v, checks a z *ᵥ v = 0 → bitWeight v < d →
      (∀ r, ((support v) ∩ neighbors a x r).card ≤ 6) → v = 0)
    (zCert : ∀ v, checks a x *ᵥ v = 0 → bitWeight v < d →
      (∀ r, ((support v) ∩ neighbors a z r).card ≤ 6) → v = 0) :
    (d : ℕ∞) ≤ cssDistance c := by
  apply Stabilizer.distance_ge_of_reduced c d
  · rw [hx, hz]
    intro v hzero hwt hr
    exact xCert v hzero hwt ((row_reduced_iff a x v).mp hr)
  · rw [hx, hz]
    intro v hzero hwt hr
    exact zCert v hzero hwt ((row_reduced_iff a z v).mp hr)

end ArmillaryLean.Routed

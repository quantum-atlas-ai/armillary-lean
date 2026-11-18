module

public import ArmillaryLean.Instances.ReducedNumeric

@[expose] public section

/-!
# Fast row words from station-zero routed tables

A small station-zero table is checked against the actual route. Cyclic
translation then proves the values at all stations. The numeric row table
can be checked without reevaluating the original routing at every station.
-/

namespace ArmillaryLean.Routed

open ArmillaryLean.Exclusion
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)

variable {p q : ℕ} [NeZero p]

/-- The output cells of the source route at station zero. -/
abbrev ZeroTable (p q : ℕ) := Fin 3 → Fin 12 → Fin q → Cell p q

/-- Use station translation to read a reference row word from a station-zero table. -/
def fastCertWord (table : ZeroTable p q) (r : Nat) : Nat :=
  if h : r < 3 * (p * q) then
    let row : Check p q := addressEquiv.symm ⟨r, h⟩
    Numeric.ofList ((List.finRange 12).map (fun b =>
      let z := table row.1 b row.2.2
      address (b, (z.1 + row.2.1, z.2))))
  else 0

/-- Checking the station-zero table suffices to certify the fast reference word. -/
theorem fastCertWord_eq (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (table : ZeroTable p q) (hzero : ∀ g b j, table g b j = armEff a (groups g) b (0, j))
    (r : Nat) : fastCertWord table r = certWord a groups r := by
  by_cases h : r < 3 * (p * q)
  · simp only [fastCertWord, certWord, dite_eq_left h]
    congr 1
    apply List.map_congr_left
    intro b _
    let row : Check p q := addressEquiv.symm ⟨r, h⟩
    change address (b, ((table row.1 b row.2.2).1 + row.2.1, (table row.1 b row.2.2).2)) =
      address (b, armEff a (groups row.1) b row.2)
    rw [hzero]
    have he := visit_translate a (groups row.1) b 0 row.2.1 row.2.2
    simp only [zero_add, Prod.mk.eta] at he
    rw [he]
  · simp [fastCertWord, certWord, h]

end ArmillaryLean.Routed

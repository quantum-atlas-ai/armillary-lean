module

public import ArmillaryLean.Instances.Data8749
public import Qatlib.Papers.Armillary26.Instances.Routed

@[expose] public section

/-!
# Armillary instance 8749

The frozen Table S2 data instantiate the published twelve-group routing construction.
-/

namespace ArmillaryLean.Code8749

open Qatlib.Concepts.CodeCert.PermBlocks (matColWt permBlocks permBlocks_cwt)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff armEff_eq_intAct)
open Qatlib.Papers.Armillary26.Pairing (intAct)

/-- The internal station and channel coordinate. -/
abbrev Cell := ZMod 101 × Fin 3

/-- A physical data coordinate `(block, (station, channel))`. -/
abbrev Coord := Fin 12 × Cell

/-- A check coordinate `(retained group index, (station, channel))`. -/
abbrev Check := Fin 3 × Cell

/-- Interpret a Table S2 permutation as an equivalence of the three channels. -/
def ChannelPerm.toEquiv : ChannelPerm → Equiv.Perm (Fin 3)
  | .p012 => Equiv.refl _
  | .p021 => Equiv.swap 1 2
  | .p102 => Equiv.swap 0 1
  | .p120 => (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 2)
  | .p201 => (Equiv.swap (0 : Fin 3) 2).trans (Equiv.swap 0 1)
  | .p210 => Equiv.swap 0 2

/-- Instantiate the published twelve-group route with the audited source table. -/
def params : ArmParam 101 3 where
  hp := by decide
  hq := by decide
  perm a h := ((permTable.get ((ZMod.finEquiv 12).symm a)).get h).toEquiv
  shift a h _ := (shiftTable.get ((ZMod.finEquiv 12).symm a)).get h

/-- The data coordinate reached by a retained check in the specified block. -/
def visit (group : Fin 12) (u : Cell) (block : Fin 12) : Coord :=
  (block, armEff params group block u)

/-- The binary check matrix for a retained group list, assembled from the actual route. -/
def checks (groups : Fin 3 → Fin 12) : Matrix Check Coord (ZMod 2) :=
  permBlocks fun row => armEff params (groups row)

/-- The X-check matrix for the retained X groups in Table S2. -/
def xChecks : Matrix Check Coord (ZMod 2) := checks xGroups.get

/-- The Z-check matrix for the retained Z groups in Table S2. -/
def zChecks : Matrix Check Coord (ZMod 2) := checks zGroups.get

/-- An entry is one exactly when the routed check visits the data coordinate. -/
theorem check_iff (groups : Fin 3 → Fin 12) (r : Check) (v : Coord) :
    checks groups r v = 1 ↔ visit (groups r.1) r.2 v.1 = v := by
  obtain ⟨block, cell⟩ := v
  by_cases same : armEff params (groups r.1) block r.2 = cell <;>
    simp [checks, permBlocks, visit, same]

/-- Every data coordinate is incident to three checks in either retained sector. -/
theorem column_weight (groups : Fin 3 → Fin 12) (v : Coord) :
    matColWt (checks groups) v = 3 := by
  simpa [checks] using
    (permBlocks_cwt (K := ZMod 2) (fun row => armEff params (groups row)) v.1 v.2)

/-- Translating the initial station by `t` translates the output station by `t`. -/
theorem visit_translate (group block : Fin 12) (u : Cell) (t : ZMod 101) :
    visit group (u.1 + t, u.2) block =
      (block, ((visit group u block).2.1 + t, (visit group u block).2.2)) := by
  simp [visit, armEff_eq_intAct, intAct, add_right_comm]

/-- The Table S2 instance has 3636 physical data coordinates. -/
theorem code_length : Fintype.card Coord = 3636 := by
  simp [Coord, Cell, Fintype.card_prod, ZMod.card]

/-- The proposed upper witness in the published route's physical coordinates. -/
def upperSupport : List Coord := upperCoords

/-- The proposed upper witness has physical weight 12. -/
theorem upper_weight : upperSupport.toFinset.card = 12 :=
  (List.toFinset_card_of_nodup (show upperSupport.Nodup from upper_nodup)).trans upper_length

end ArmillaryLean.Code8749

module

public import ArmillaryLean.Certificates.Masked
public import ArmillaryLean.Instances.Rows8749
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Packed anchor certificates for Armillary 8749

The decoder uses block-major data addresses and group-major check addresses.
Acceptance is transported from the executable sparse rows to the source matrix.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion

/-- Decode a physical column address, rejecting out-of-range words. -/
def decodeCol (address : Nat) : Option Coord :=
  if address < 3636 then
    some (Fin.ofNat 12 (address / 303), (Fin.ofNat 101 (address / 3), Fin.ofNat 3 address))
  else none

/-- Decode a retained check row address, rejecting out-of-range words. -/
def decodeRow (address : Nat) : Option Check :=
  if address < 909 then
    some (Fin.ofNat 3 (address / 303), (Fin.ofNat 101 (address / 3), Fin.ofNat 3 address))
  else none

/-- Verify a packed exclusion program for one check sector and station-zero anchor. -/
def checkAnchor (sector : Fin 2) (budget : Nat) (b : Fin 12) (j : Fin 3)
    (program : Program) : Bool :=
  checkProgram (fastRows sector) decodeRow decodeCol budget 128 (b, (0, j)) program

/-- An accepted anchor program excludes small zero-syndrome supports for the source rows. -/
theorem checkedAnchor {sector : Fin 2} {budget : Nat} {b : Fin 12} {j : Fin 3}
    {program : Program} (hcheck : checkAnchor sector budget b j program = true)
    {s : Finset Coord} (ha : (b, (0, j)) ∈ s) (hz : ZeroSyndrome (neighbors (retained sector)) s)
    (hw : s.card ≤ budget) : False := by
  rw [← fastRows_eq sector] at hz
  exact program_excludes hcheck ha hz hw

/-- Encode a physical coordinate as a column-major bit address. -/
def encodeCol (v : Coord) : Fin 4096 :=
  ⟨v.1.val * 303 + v.2.1.val * 3 + v.2.2.val, by
    have hb := v.1.isLt
    have hi := v.2.1.val_lt
    have hj := v.2.2.isLt
    omega⟩

/-- Distinct physical coordinates have distinct column addresses. -/
theorem encodeCol_inj : Function.Injective encodeCol := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ he
  have h := congrArg Fin.val he
  change b.val * 303 + i.val * 3 + j.val = b'.val * 303 + i'.val * 3 + j'.val at h
  have hb := b.isLt
  have hb' := b'.isLt
  have hi := i.val_lt
  have hi' := i'.val_lt
  have hj := j.isLt
  have hj' := j'.isLt
  have heB : b.val = b'.val := by omega
  have heI : i.val = i'.val := by omega
  have heJ : j.val = j'.val := by omega
  exact Prod.ext (Fin.ext heB) (Prod.ext (ZMod.val_injective 101 heI) (Fin.ext heJ))

/-- Represent the twelve actual row neighbours as eight bitmask chunks. -/
def fastMask (sector : Fin 2) (r : Check) : Mask :=
  Mask.ofList ((List.finRange 12).map fun b => encodeCol (fastVisit sector r b))

/-- Fast mask membership is equivalent in both directions to actual routed incidence. -/
theorem fastMask_rep (sector : Fin 2) (r : Check) :
    Represents encodeCol (fastMask sector r) (fastRows sector r) := by
  intro v
  rw [fastMask, Mask.has_ofList, List.mem_map, fastRows, Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, _, he⟩
    exact ⟨b, Finset.mem_univ _, encodeCol_inj he⟩
  · rintro ⟨b, _, he⟩
    exact ⟨b, List.mem_finRange _, congrArg encodeCol he⟩

/-- Verify an anchor program using the chunked-mask checker. -/
def checkMasked (sector : Fin 2) (budget : Nat) (b : Fin 12) (j : Fin 3)
    (program : Program) : Bool :=
  maskProgram encodeCol (fastMask sector) decodeRow decodeCol budget 128 (b, (0, j)) program

/-- The mask checker excludes anchored supports in the source matrix. -/
theorem checkedMasked {sector : Fin 2} {budget : Nat} {b : Fin 12} {j : Fin 3}
    {program : Program} (hcheck : checkMasked sector budget b j program = true)
    {s : Finset Coord} (ha : (b, (0, j)) ∈ s) (hz : ZeroSyndrome (neighbors (retained sector)) s)
    (hw : s.card ≤ budget) : False := by
  rw [← fastRows_eq sector] at hz
  exact maskProgram_excludes encodeCol_inj (fastMask_rep sector) hcheck ha hz hw

/-- Check an independent fragment from an explicit list of selected and decided columns. -/
def checkFragment (sector : Fin 2) (budget : Nat) (selected decided : List Coord)
    (program : Program) : Bool :=
  maskProgramFrom encodeCol (fastMask sector) decodeRow decodeCol budget 128 selected
    (Mask.ofList (decided.map encodeCol)) program

/-- A verified fragment provides a reusable exclusion for the actual source rows. -/
theorem checkedFragment {sector : Fin 2} {budget : Nat} {selected decided : List Coord}
    {program : Program} (hn : selected.Nodup) (hs : selected.toFinset ⊆ decided.toFinset)
    (hc : checkFragment sector budget selected decided program = true) :
    Excluded (neighbors (retained sector)) budget selected.toFinset decided.toFinset := by
  have hm : Represents encodeCol (Mask.ofList (decided.map encodeCol)) decided.toFinset := by
    intro c
    rw [Mask.has_ofList, List.mem_map, List.mem_toFinset]
    exact ⟨fun ⟨d, hd, he⟩ => (encodeCol_inj he) ▸ hd, fun h => ⟨c, h, rfl⟩⟩
  rw [← fastRows_eq sector]
  exact maskProgramFrom_excludes encodeCol_inj (fastMask_rep sector) hn hs hm hc

end ArmillaryLean.Code8749

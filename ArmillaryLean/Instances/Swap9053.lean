module

public import ArmillaryLean.Instances.Code9053
public import ArmillaryLean.Instances.RoutedSwap
import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The 9053 check-sector swap

A common involution on the coordinates exchanges the X and Z row families.
It reverses the station and applies a block-dependent offset and channel map.
-/

namespace ArmillaryLean.Code9053

open ArmillaryLean.Routed
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)
open Qatlib.Papers.Armillary26.Instances (armEff)

set_option maxRecDepth 8192

/-- The data block images under the sector swap. -/
def blockImage (b : Fin 12) : Fin 12 :=
  (#v[5, 4, 3, 2, 1, 0, 10, 11, 9, 8, 6, 7] : Vector (Fin 12) 12).get b

/-- The block images form an involution. -/
theorem block_invol : ∀ b, blockImage (blockImage b) = b := by decide

/-- The block equivalence used by the sector swap. -/
def blockIso : Fin 12 ≃ Fin 12 :=
  ⟨blockImage, blockImage, block_invol, block_invol⟩

/-- The station offsets for the source data blocks. -/
def dataOffset (b : Fin 12) : ZMod 137 :=
  (#v[120, 122, 125, 125, 122, 120, 125, 128, 124, 124, 125, 128] :
    Vector (ZMod 137) 12).get b

/-- The channel actions for the source data blocks. -/
def dataChannel (b : Fin 12) : Equiv.Perm (Fin 3) :=
  (#v[p210, p102, p021, p021, p102, p210, p120, p021, p120, p201, p201, p021] :
    Vector (Equiv.Perm (Fin 3)) 12).get b

/-- Reverse and relabel a data coordinate. -/
def dataImage (c : Coord 137 3) : Coord 137 3 :=
  (blockImage c.1, (dataOffset c.1 - c.2.1, dataChannel c.1 c.2.2))

/-- A second application of the data correspondence returns the original coordinate. -/
theorem data_invol : Function.Involutive dataImage := by
  rintro ⟨b, i, j⟩
  have h₁ : ∀ b, dataOffset (blockImage b) = dataOffset b := by decide
  have h₂ : ∀ b j, dataChannel (blockImage b) (dataChannel b j) = j := by decide
  simp only [dataImage, block_invol, h₁, sub_sub_cancel, h₂]

/-- The data equivalence common to the X-to-Z and Z-to-X diagrams. -/
def dataIso : Coord 137 3 ≃ Coord 137 3 :=
  ⟨dataImage, dataImage, data_invol, data_invol⟩

/-- Match retained group indices in reverse order. -/
def checkGroup : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- The station offsets of the source check groups. -/
def checkOffset (g : Fin 3) : ZMod 137 :=
  (#v[0, 134, 136] : Vector (ZMod 137) 3).get g

/-- The row channel action in each source check group. -/
def checkChannel (g : Fin 3) : Equiv.Perm (Fin 3) :=
  (#v[p102, p120, p120] : Vector (Equiv.Perm (Fin 3)) 3).get g

/-- The row equivalence from the X checks to the Z checks. -/
def checkIso : Check 137 3 ≃ Check 137 3 where
  toFun r := (checkGroup r.1, (checkOffset r.1 - r.2.1, checkChannel r.1 r.2.2))
  invFun r := let g := checkGroup.symm r.1
              (g, (checkOffset g - r.2.1, (checkChannel g).symm r.2.2))
  left_inv r := by simp
  right_inv r := by simp

set_option maxHeartbeats 0 in
/-- The affine row diagram agrees at station zero in every group, block and channel. -/
private theorem visit_zero : ∀ (g : Fin 3) (j : Fin 3) (b : Fin 12),
    dataIso (b, armEff params (xGroups.get g) b (0, j)) =
      (blockIso b, armEff params (zGroups.get (checkGroup g)) (blockIso b)
        (checkOffset g, checkChannel g j)) := by
  decide +kernel

/-- Extend the station-zero diagram by station translation. -/
theorem visits_swap (r : Check 137 3) (b : Fin 12) :
    dataIso (b, armEff params (xGroups.get r.1) b r.2) =
      (blockIso b, armEff params (zGroups.get (checkIso r).1) (blockIso b) (checkIso r).2) := by
  obtain ⟨g, i, j⟩ := r
  let u := armEff params (xGroups.get g) b (0, j)
  let v := armEff params (zGroups.get (checkGroup g)) (blockIso b)
    (checkOffset g, checkChannel g j)
  have tx := visit_translate params (xGroups.get g) b 0 i j
  simp only [zero_add] at tx
  have tz := visit_translate params (zGroups.get (checkGroup g)) (blockIso b)
    (checkOffset g) (-i) (checkChannel g j)
  have h := visit_zero g j b
  have hp : dataOffset b - u.1 = v.1 := congrArg (fun c : Coord 137 3 => c.2.1) h
  have hc : dataChannel b u.2 = v.2 := congrArg (fun c : Coord 137 3 => c.2.2) h
  have hp' : dataOffset b - (u.1 + i) = v.1 + -i := by
    calc
      _ = (dataOffset b - u.1) + -i := by abel
      _ = _ := by rw [hp]
  change dataIso (b, armEff params (xGroups.get g) b (i, j)) =
    (blockIso b, armEff params (zGroups.get (checkGroup g)) (blockIso b)
      (checkOffset g - i, checkChannel g j))
  rw [sub_eq_add_neg, tx, tz]
  change (blockIso b, (dataOffset b - (u.1 + i), dataChannel b u.2)) =
    (blockIso b, (v.1 + -i, v.2))
  rw [hp', hc]

/-- The same involution transports both check families and their overlaps. -/
def sectorSwap : SectorSwap params xGroups.get zGroups.get where
  dataMap := dataIso
  xToZ := checkIso
  zToX := checkIso.symm
  mapX := neighbors_of_visits params xGroups.get zGroups.get dataIso checkIso blockIso visits_swap
  mapZ r := by
    have hh := neighbors_of_visits params xGroups.get zGroups.get
      dataIso checkIso blockIso visits_swap (checkIso.symm r)
    rw [Equiv.apply_symm_apply] at hh
    rw [hh]
    ext c
    simp only [Finset.mem_map_equiv]
    exact Iff.of_eq (congrArg (fun v => v ∈ neighbors params xGroups.get (checkIso.symm r))
      (data_invol c).symm)

/-- The 9053 distance follows from reduced anchors for X checks alone. -/
theorem distance_eq_fourteen_of_x
    (cert : ReducedAnchors params zGroups.get xGroups.get 12) : cssDistance code = 14 := by
  apply le_antisymm distance_le_fourteen
  exact distance_ge_of_swap params xGroups.get zGroups.get code rfl rfl sectorSwap 14 (by decide) cert

end ArmillaryLean.Code9053

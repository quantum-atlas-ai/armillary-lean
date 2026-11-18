module

public import ArmillaryLean.Instances.Data9053
public import ArmillaryLean.Instances.RoutedUpper

@[expose] public section

/-!
# Concrete CSS code and upper distance witness for 9053

The source route certifies both CSS orthogonality and the opposite-sector
syndrome of the proposed pure X witness.
-/

namespace ArmillaryLean.Code9053

open ArmillaryLean.Routed
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Papers.Armillary26.Instances (armEff)
open Qatlib.Papers.Armillary26.Pairing (Kchi)
open scoped Matrix

/-- A pairing of blocks with equal relative routes and equal visit order. -/
def blockPair (x z : Fin 3) (b : Fin 12) : Fin 12 :=
  (((#v[#v[#v[9, 10, 6, 4, 3, 7, 2, 5, 11, 0, 1, 8], #v[1, 0, 11, 8, 9, 10, 7, 6, 3, 4, 5, 2], #v[5, 4, 3, 2, 1, 0, 10, 11, 9, 8, 6, 7]],
    #v[#v[1, 0, 11, 8, 9, 10, 7, 6, 3, 4, 5, 2], #v[5, 4, 3, 2, 1, 0, 10, 11, 9, 8, 6, 7], #v[6, 8, 9, 7, 5, 4, 0, 3, 1, 2, 11, 10]],
    #v[#v[5, 4, 3, 2, 1, 0, 10, 11, 9, 8, 6, 7], #v[6, 8, 9, 7, 5, 4, 0, 3, 1, 2, 11, 10], #v[11, 2, 1, 10, 6, 8, 4, 9, 5, 7, 3, 0]]] :
      Vector (Vector (Vector (Fin 12) 12) 3) 3).get x).get z).get b

set_option maxHeartbeats 0 in
/-- The two relative routes in each block pair agree at station zero. -/
private theorem relative_zero : ∀ (x z : Fin 3) (b : Fin 12) (k : Fin 3),
    relative params (xGroups.get x) (zGroups.get z) (blockPair x z b) (0, k) =
      relative params (xGroups.get x) (zGroups.get z) b (0, k) := by
  decide +kernel

/-- The certified source pairing is fixed-point-free and order-preserving. -/
theorem source_pair : Kchi xGroups.get zGroups.get
    (fun x => armEff params (xGroups.get x)) (fun z => armEff params (zGroups.get z)) blockPair :=
  paired params xGroups.get zGroups.get blockPair
    (by
      change ∀ (x z : Fin 3) (b : Fin 12), blockPair x z (blockPair x z b) = b
      decide)
    (by decide)
    relative_zero
    (by decide)

/-- The CSS code constructed from the frozen retained checks. -/
def code : CssData (Coord 137 3) (Check 137 3) (Check 137 3) :=
  Routed.code params xGroups.get zGroups.get blockPair source_pair

/-- The physical coordinate count of this source instance. -/
theorem code_length : Fintype.card (Coord 137 3) = 4932 := by
  simp [Coord, Cell, Fintype.card_prod, ZMod.card]

/-- Within each retained Z group, witness indices pair on the same row. -/
def witnessPair (z : Fin 3) (i : Fin 14) : Fin 14 :=
  ((#v[#v[11, 12, 13, 9, 6, 10, 4, 8, 7, 3, 5, 0, 1, 2],
    #v[3, 5, 11, 0, 12, 1, 9, 10, 13, 6, 7, 2, 4, 8],
    #v[12, 6, 4, 11, 2, 8, 1, 9, 5, 7, 13, 3, 0, 10]] :
    Vector (Vector (Fin 14) 14) 3).get z).get i

/-- The proposed witness enumerates distinct physical coordinates. -/
private theorem witness_injective : Function.Injective upperCoords.get := by
  change ∀ (i j : Fin 14), upperCoords.get i = upperCoords.get j → i = j
  decide +kernel

set_option maxHeartbeats 0 in
/-- Paired coordinates trace back to the same actual row. -/
private theorem witness_rows : ∀ (z : Fin 3) (i : Fin 14),
    incoming params (zGroups.get z) (upperCoords.get (witnessPair z i)) =
      incoming params (zGroups.get z) (upperCoords.get i) := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The paired support and the block 0/1 separator bound CSS distance by 14. -/
theorem distance_le_fourteen : cssDistance code ≤ 14 := by
  refine distance_le_of_witness params xGroups.get zGroups.get code rfl rfl
    upperCoords.get witness_injective ?_ 0 1 ?_ ?_
  · apply witness_zero params zGroups.get upperCoords.get witness_injective witnessPair
    · change ∀ (z : Fin 3) (i : Fin 14), witnessPair z (witnessPair z i) = i
      decide
    · decide
    · exact witness_rows
  · decide +kernel
  · decide +kernel

end ArmillaryLean.Code9053

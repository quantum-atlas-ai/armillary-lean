module

public import ArmillaryLean.Instances.DataP181
public import ArmillaryLean.Instances.RoutedUpper

@[expose] public section

/-!
# Concrete CSS code and upper distance witness for P181

The source route certifies both CSS orthogonality and the opposite-sector
syndrome of the proposed pure X witness.
-/

namespace ArmillaryLean.CodeP181

open ArmillaryLean.Routed
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Papers.Armillary26.Instances (armEff)
open Qatlib.Papers.Armillary26.Pairing (Kchi)
open scoped Matrix

/-- A pairing of blocks with equal relative routes and equal visit order. -/
def blockPair (x z : Fin 3) (b : Fin 12) : Fin 12 :=
  (((#v[#v[#v[7, 2, 1, 5, 10, 3, 11, 0, 9, 8, 4, 6], #v[3, 10, 11, 0, 8, 9, 7, 6, 4, 5, 1, 2], #v[9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11, 10]],
    #v[#v[3, 10, 11, 0, 8, 9, 7, 6, 4, 5, 1, 2], #v[9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11, 10], #v[4, 5, 3, 2, 0, 1, 9, 10, 11, 6, 7, 8]],
    #v[#v[9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 11, 10], #v[4, 5, 3, 2, 0, 1, 9, 10, 11, 6, 7, 8], #v[1, 0, 9, 10, 6, 11, 4, 8, 7, 2, 3, 5]]] :
      Vector (Vector (Vector (Fin 12) 12) 3) 3).get x).get z).get b

set_option maxHeartbeats 0 in
/-- The two relative routes in each block pair agree at station zero. -/
private theorem relative_zero : ∀ (x z : Fin 3) (b : Fin 12) (k : Fin 4),
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
def code : CssData (Coord 181 4) (Check 181 4) (Check 181 4) :=
  Routed.code params xGroups.get zGroups.get blockPair source_pair

/-- The physical coordinate count of this source instance. -/
theorem code_length : Fintype.card (Coord 181 4) = 8688 := by
  simp [Coord, Cell, Fintype.card_prod, ZMod.card]

/-- Within each retained Z group, witness indices pair on the same row. -/
def witnessPair (z : Fin 3) (i : Fin 16) : Fin 16 :=
  ((#v[#v[15, 12, 7, 14, 8, 13, 11, 2, 4, 10, 9, 6, 1, 5, 3, 0],
    #v[9, 4, 5, 7, 1, 2, 8, 3, 6, 0, 12, 13, 10, 11, 15, 14],
    #v[14, 11, 6, 12, 9, 8, 2, 10, 5, 4, 7, 1, 3, 15, 0, 13]] :
    Vector (Vector (Fin 16) 16) 3).get z).get i

/-- The proposed witness enumerates distinct physical coordinates. -/
private theorem witness_injective : Function.Injective upperCoords.get := by
  change ∀ (i j : Fin 16), upperCoords.get i = upperCoords.get j → i = j
  decide +kernel

set_option maxHeartbeats 0 in
/-- Paired coordinates trace back to the same actual row. -/
private theorem witness_rows : ∀ (z : Fin 3) (i : Fin 16),
    incoming params (zGroups.get z) (upperCoords.get (witnessPair z i)) =
      incoming params (zGroups.get z) (upperCoords.get i) := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The paired support and the block 0/1 separator bound CSS distance by 16. -/
theorem distance_le_sixteen : cssDistance code ≤ 16 := by
  refine distance_le_of_witness params xGroups.get zGroups.get code rfl rfl
    upperCoords.get witness_injective ?_ 0 1 ?_ ?_
  · apply witness_zero params zGroups.get upperCoords.get witness_injective witnessPair
    · change ∀ (z : Fin 3) (i : Fin 16), witnessPair z (witnessPair z i) = i
      decide
    · decide
    · exact witness_rows
  · decide +kernel
  · decide +kernel

end ArmillaryLean.CodeP181

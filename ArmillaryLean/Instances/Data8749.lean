module

@[expose] public section

/-!
# Armillary instance 8749 source data

Table S2 fixes the retained groups, channel permutations and station shifts.
The permutation names give the images of channels `0`, `1` and `2` in order.
-/

namespace ArmillaryLean.Code8749

/-- The retained X-check groups, in source order. -/
def xGroups : Vector (Fin 12) 3 := #v[4, 0, 8]

/-- The retained Z-check groups, in source order. -/
def zGroups : Vector (Fin 12) 3 := #v[6, 2, 10]

/-- The six possible channel permutations in the Table S2 transcription. -/
inductive ChannelPerm where
  | p012 | p021 | p102 | p120 | p201 | p210

open ChannelPerm

/-- Table S2 channel permutations, indexed by initial group and round pair. -/
def permTable : Vector (Vector ChannelPerm 6) 12 :=
  #v[#v[p021, p021, p021, p210, p012, p120],
    #v[p201, p210, p210, p210, p120, p120],
    #v[p201, p012, p210, p021, p102, p012],
    #v[p120, p120, p012, p120, p210, p021],
    #v[p102, p021, p102, p210, p012, p102],
    #v[p012, p120, p210, p102, p021, p120],
    #v[p120, p012, p012, p201, p102, p012],
    #v[p210, p021, p201, p201, p012, p012],
    #v[p102, p021, p201, p021, p120, p012],
    #v[p012, p102, p021, p201, p012, p012],
    #v[p012, p012, p210, p021, p012, p120],
    #v[p021, p120, p021, p012, p201, p021]]

/-- Table S2 station shifts are scalar and apply equally to all three channels. -/
def shiftTable : Vector (Vector Int 6) 12 :=
  #v[#v[1, 1, 2, 1, 3, -1],
    #v[0, 3, 1, 4, -2, -2],
    #v[-1, 0, 4, 2, -1, 2],
    #v[4, 0, -1, -2, -2, 0],
    #v[-1, 2, 2, 0, 0, -1],
    #v[-2, -2, 0, -1, 0, 3],
    #v[1, 0, 0, 4, 0, 1],
    #v[2, 1, 4, 1, 3, -1],
    #v[2, 1, 3, -1, 3, -1],
    #v[2, 4, -1, -1, 3, -2],
    #v[-1, -2, 3, 4, -2, 0],
    #v[2, 2, 1, 2, 4, -2]]

/-- Physical-coordinate support supplied for the proposed distance upper witness. -/
def upperCoords : List (Fin 12 × (Fin 101 × Fin 3)) :=
  [(2, (75, 0)), (2, (79, 1)), (3, (75, 2)), (4, (83, 2)),
   (5, (82, 2)), (5, (86, 1)), (6, (81, 0)), (6, (85, 2)),
   (8, (82, 0)), (9, (84, 0)), (9, (88, 1)), (11, (80, 2))]

/-- The distance upper candidate lists twelve physical coordinates. -/
theorem upper_length : upperCoords.length = 12 := by decide

/-- The coordinates of the distance upper candidate are pairwise distinct. -/
theorem upper_nodup : upperCoords.Nodup := by decide

end ArmillaryLean.Code8749

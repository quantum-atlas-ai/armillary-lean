module

public import ArmillaryLean.Instances.Routed

@[expose] public section

/-!
# Armillary instance P181 source data

Table S4 of the frozen manuscript transcription supplies the retained groups,
channel permutations and shifts. Permutation names list the images in order.
The upper witness support is from qatlib-dev issue #553.
-/

namespace ArmillaryLean.CodeP181

open ArmillaryLean.Routed (Coord channelPerm)
open Qatlib.Papers.Armillary26.Instances (ArmParam)

/-- The retained X-check groups in source order. -/
def xGroups : Vector (Fin 12) 3 := #v[8, 4, 0]

/-- The retained Z-check groups in source order. -/
def zGroups : Vector (Fin 12) 3 := #v[10, 6, 2]

/-- The channel permutation with images `p0123` in order. -/
def p0123 : Equiv.Perm (Fin 4) :=
  channelPerm #v[0, 1, 2, 3] #v[0, 1, 2, 3] (by decide)

/-- The channel permutation with images `p0132` in order. -/
def p0132 : Equiv.Perm (Fin 4) :=
  channelPerm #v[0, 1, 3, 2] #v[0, 1, 3, 2] (by decide)

/-- The channel permutation with images `p0213` in order. -/
def p0213 : Equiv.Perm (Fin 4) :=
  channelPerm #v[0, 2, 1, 3] #v[0, 2, 1, 3] (by decide)

/-- The channel permutation with images `p0231` in order. -/
def p0231 : Equiv.Perm (Fin 4) :=
  channelPerm #v[0, 2, 3, 1] #v[0, 3, 1, 2] (by decide)

/-- The channel permutation with images `p1023` in order. -/
def p1023 : Equiv.Perm (Fin 4) :=
  channelPerm #v[1, 0, 2, 3] #v[1, 0, 2, 3] (by decide)

/-- The channel permutation with images `p1032` in order. -/
def p1032 : Equiv.Perm (Fin 4) :=
  channelPerm #v[1, 0, 3, 2] #v[1, 0, 3, 2] (by decide)

/-- The channel permutation with images `p1230` in order. -/
def p1230 : Equiv.Perm (Fin 4) :=
  channelPerm #v[1, 2, 3, 0] #v[3, 0, 1, 2] (by decide)

/-- The channel permutation with images `p1320` in order. -/
def p1320 : Equiv.Perm (Fin 4) :=
  channelPerm #v[1, 3, 2, 0] #v[3, 0, 2, 1] (by decide)

/-- The channel permutation with images `p2130` in order. -/
def p2130 : Equiv.Perm (Fin 4) :=
  channelPerm #v[2, 1, 3, 0] #v[3, 1, 0, 2] (by decide)

/-- The channel permutation with images `p2301` in order. -/
def p2301 : Equiv.Perm (Fin 4) :=
  channelPerm #v[2, 3, 0, 1] #v[2, 3, 0, 1] (by decide)

/-- The channel permutation with images `p2310` in order. -/
def p2310 : Equiv.Perm (Fin 4) :=
  channelPerm #v[2, 3, 1, 0] #v[3, 2, 0, 1] (by decide)

/-- The channel permutation with images `p3012` in order. -/
def p3012 : Equiv.Perm (Fin 4) :=
  channelPerm #v[3, 0, 1, 2] #v[1, 2, 3, 0] (by decide)

/-- The channel permutation with images `p3021` in order. -/
def p3021 : Equiv.Perm (Fin 4) :=
  channelPerm #v[3, 0, 2, 1] #v[1, 3, 2, 0] (by decide)

/-- The channel permutation with images `p3102` in order. -/
def p3102 : Equiv.Perm (Fin 4) :=
  channelPerm #v[3, 1, 0, 2] #v[2, 1, 3, 0] (by decide)

/-- The channel permutation with images `p3201` in order. -/
def p3201 : Equiv.Perm (Fin 4) :=
  channelPerm #v[3, 2, 0, 1] #v[2, 3, 1, 0] (by decide)

/-- Source channel permutations, indexed by initial group and round pair. -/
def permTable : Vector (Vector (Equiv.Perm (Fin 4)) 6) 12 :=
  #v[#v[p0123, p0123, p3012, p0123, p2301, p1320],
    #v[p0123, p2130, p0123, p2301, p0123, p1032],
    #v[p0123, p0123, p1230, p0123, p2310, p3201],
    #v[p3102, p1230, p3021, p3012, p3201, p3012],
    #v[p1230, p0123, p3012, p1230, p3012, p2130],
    #v[p0123, p1320, p0123, p0123, p3012, p3201],
    #v[p0123, p0123, p0123, p3012, p0213, p1320],
    #v[p3012, p0123, p2310, p1230, p1320, p3021],
    #v[p0123, p3012, p1230, p0123, p3021, p0132],
    #v[p0123, p3201, p0123, p3021, p1320, p0231],
    #v[p0123, p0123, p0213, p1320, p2301, p0123],
    #v[p0123, p0123, p0213, p3012, p1023, p2301]]

/-- Source station shifts, indexed by initial group and round pair. -/
def shiftTable : Vector (Vector (Vector Int 4) 6) 12 :=
  #v[#v[#v[3, -1, 0, -2], #v[7, 5, -1, 7], #v[-3, 2, 1, -4], #v[5, 2, 3, 1], #v[5, 7, 7, 7], #v[0, -2, -4, 2]],
    #v[#v[5, 2, 7, 5], #v[-5, 0, -3, -6], #v[5, 4, 3, 5], #v[-3, -3, -1, -1], #v[6, 1, 7, -1], #v[0, 0, 0, 0]],
    #v[#v[2, 7, -3, 7], #v[7, 6, 7, 7], #v[-3, -3, -1, -1], #v[6, 4, 4, 0], #v[2, -2, 2, 2], #v[2, 6, 4, 7]],
    #v[#v[3, 2, 4, 3], #v[-4, -6, 0, -2], #v[7, 6, 5, 0], #v[7, -4, -3, 4], #v[-2, 2, 0, 4], #v[0, 0, 0, 0]],
    #v[#v[2, 1, 3, 3], #v[7, 7, 3, 1], #v[0, -3, 2, 1], #v[-3, 1, 2, 2], #v[6, 7, 5, 7], #v[7, 4, 5, 7]],
    #v[#v[5, 7, 0, 7], #v[2, -1, 5, 4], #v[-3, 1, 2, 2], #v[4, 5, 2, 4], #v[7, 7, 3, 5], #v[0, 0, 0, 0]],
    #v[#v[6, 7, 7, 7], #v[3, 3, 3, -1], #v[2, 4, 1, 2], #v[-2, 2, 2, 3], #v[-6, -2, -5, -6], #v[3, 3, 3, 4]],
    #v[#v[7, 7, 7, 2], #v[6, -2, 3, 2], #v[-3, 1, 2, 1], #v[-3, -3, -6, -3], #v[7, 7, 7, 7], #v[0, 0, 0, 0]],
    #v[#v[7, -4, 4, 4], #v[4, 0, 2, -1], #v[-4, -5, -4, -2], #v[0, 4, 1, 2], #v[3, 3, 5, 5], #v[5, 6, 7, 4]],
    #v[#v[0, -6, -6, 0], #v[6, 3, 4, 6], #v[-2, 2, 5, -4], #v[5, 7, 7, 7], #v[2, 6, 6, 7], #v[0, 0, 0, 0]],
    #v[#v[7, 3, 7, 1], #v[-2, 2, 5, -4], #v[3, 3, 5, 5], #v[2, 1, -3, -6], #v[3, 7, 7, 5], #v[0, -2, -6, -4]],
    #v[#v[-4, 1, 4, -5], #v[6, 2, 4, 6], #v[2, 1, -3, -6], #v[5, 7, 6, 2], #v[1, -1, -5, -2], #v[0, 0, 0, 0]]]

/-- The actual twelve-group route applied to the frozen table. -/
def params : ArmParam 181 4 where
  hp := by decide
  hq := by decide
  perm a h := (permTable.get ((ZMod.finEquiv 12).symm a)).get h
  shift a h j := ((shiftTable.get ((ZMod.finEquiv 12).symm a)).get h).get j

/-- The physical support of the proposed weight-16 logical label. -/
def upperCoords : Vector (Coord 181 4) 16 :=
  #v[(0, (35, 2)), (2, (4, 1)), (2, (6, 1)), (4, (7, 3)),
     (4, (9, 2)), (4, (11, 2)), (4, (15, 2)), (5, (10, 3)),
     (5, (18, 2)), (7, (22, 1)), (8, (18, 2)), (8, (27, 1)),
     (9, (18, 2)), (9, (19, 1)), (9, (27, 2)), (11, (31, 2))]

end ArmillaryLean.CodeP181

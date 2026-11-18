module

public import ArmillaryLean.Instances.Routed

@[expose] public section

/-!
# Armillary instance 9053 source data

Table S3 of the frozen manuscript transcription supplies the retained groups,
channel permutations and shifts. Permutation names list the images in order.
The upper witness support is from qatlib-dev issue #553.
-/

namespace ArmillaryLean.Code9053

open ArmillaryLean.Routed (Coord channelPerm)
open Qatlib.Papers.Armillary26.Instances (ArmParam)

/-- The retained X-check groups in source order. -/
def xGroups : Vector (Fin 12) 3 := #v[8, 0, 4]

/-- The retained Z-check groups in source order. -/
def zGroups : Vector (Fin 12) 3 := #v[2, 6, 10]

/-- The channel permutation with images `p012` in order. -/
def p012 : Equiv.Perm (Fin 3) :=
  channelPerm #v[0, 1, 2] #v[0, 1, 2] (by decide)

/-- The channel permutation with images `p021` in order. -/
def p021 : Equiv.Perm (Fin 3) :=
  channelPerm #v[0, 2, 1] #v[0, 2, 1] (by decide)

/-- The channel permutation with images `p102` in order. -/
def p102 : Equiv.Perm (Fin 3) :=
  channelPerm #v[1, 0, 2] #v[1, 0, 2] (by decide)

/-- The channel permutation with images `p120` in order. -/
def p120 : Equiv.Perm (Fin 3) :=
  channelPerm #v[1, 2, 0] #v[2, 0, 1] (by decide)

/-- The channel permutation with images `p201` in order. -/
def p201 : Equiv.Perm (Fin 3) :=
  channelPerm #v[2, 0, 1] #v[1, 2, 0] (by decide)

/-- The channel permutation with images `p210` in order. -/
def p210 : Equiv.Perm (Fin 3) :=
  channelPerm #v[2, 1, 0] #v[2, 1, 0] (by decide)

/-- Source channel permutations, indexed by initial group and round pair. -/
def permTable : Vector (Vector (Equiv.Perm (Fin 3)) 6) 12 :=
  #v[#v[p120, p201, p102, p120, p012, p021],
    #v[p102, p102, p012, p120, p021, p021],
    #v[p102, p012, p120, p021, p021, p012],
    #v[p021, p120, p120, p120, p201, p210],
    #v[p012, p201, p120, p012, p102, p021],
    #v[p210, p120, p201, p021, p021, p120],
    #v[p120, p201, p021, p021, p120, p012],
    #v[p201, p201, p201, p021, p102, p012],
    #v[p102, p102, p021, p012, p021, p021],
    #v[p102, p201, p102, p201, p021, p012],
    #v[p021, p201, p201, p201, p210, p102],
    #v[p210, p021, p102, p102, p102, p102]]

/-- Source station shifts, indexed by initial group and round pair. -/
def shiftTable : Vector (Vector Int 6) 12 :=
  #v[#v[3, -1, -4, -4, 1, 3],
    #v[4, -3, -4, 2, -4, 2],
    #v[-2, -3, -1, -3, 4, 0],
    #v[-1, -1, -3, 4, -2, -2],
    #v[1, 4, -3, -4, -2, 3],
    #v[-3, -4, -4, -3, -2, 0],
    #v[2, -1, -4, -3, 1, -3],
    #v[-3, 2, -3, -4, -2, 0],
    #v[3, -3, -4, -4, 1, 0],
    #v[-2, 0, -4, -3, 1, -3],
    #v[1, -3, -4, -1, -4, 1],
    #v[-4, 1, -1, 2, 3, -3]]

/-- The actual twelve-group route applied to the frozen table. -/
def params : ArmParam 137 3 where
  hp := by decide
  hq := by decide
  perm a h := (permTable.get ((ZMod.finEquiv 12).symm a)).get h
  shift a h _ := (shiftTable.get ((ZMod.finEquiv 12).symm a)).get h

/-- The physical support of the proposed weight-14 logical label. -/
def upperCoords : Vector (Coord 137 3) 14 :=
  #v[(1, (1, 1)), (1, (2, 1)), (1, (132, 2)), (2, (2, 0)),
     (2, (134, 2)), (5, (135, 0)), (6, (125, 0)), (6, (129, 0)),
     (7, (1, 1)), (9, (129, 0)), (10, (130, 0)), (11, (0, 1)),
     (11, (1, 1)), (11, (131, 2))]

end ArmillaryLean.Code9053

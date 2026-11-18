module

meta import ArmillaryLean.Instances.Data9053
meta import ArmillaryLean.Instances.DataP181
meta import ArmillaryLean.Instances.ReducedNumeric

open ArmillaryLean.Routed (Check address addressEquiv)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)

meta def exportRows {p q : Nat} [NeZero p] (a : ArmParam p q)
    (groups : Fin 3 → Fin 12) (sector : String) : IO Unit := do
  let root := System.FilePath.mk ".lake/reduced"
  IO.FS.createDirAll root
  let rows := (List.finRange (3 * (p * q))).map fun r =>
    let row : Check p q := addressEquiv.symm r
    String.intercalate " " ((List.finRange 12).map fun b =>
      toString (address (b, armEff a (groups row.1) b row.2)))
  IO.FS.writeFile (root / s!"{p}-{sector}.rows") (String.intercalate "\n" rows ++ "\n")

#eval exportRows ArmillaryLean.Code9053.params ArmillaryLean.Code9053.xGroups.get "X"
#eval exportRows ArmillaryLean.Code9053.params ArmillaryLean.Code9053.zGroups.get "Z"
#eval exportRows ArmillaryLean.CodeP181.params ArmillaryLean.CodeP181.xGroups.get "X"
#eval exportRows ArmillaryLean.CodeP181.params ArmillaryLean.CodeP181.zGroups.get "Z"

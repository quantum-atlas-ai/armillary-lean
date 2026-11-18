module

meta import ArmillaryLean.Instances.Anchor8749

open ArmillaryLean.Code8749

#eval do
  let root := System.FilePath.mk ".lake/dist8749"
  IO.FS.createDirAll root
  for sector in List.finRange 2 do
    let name := if sector = 0 then "X.rows" else "Z.rows"
    let rows := (List.finRange 909).map fun (index : Fin 909) =>
      match decodeRow index.val with
      | none => ""
      | some row => String.intercalate " " ((List.finRange 12).map fun block =>
          toString (encodeCol (fastVisit sector row block)).val)
    IO.FS.writeFile (root / name) (String.intercalate "\n" rows ++ "\n")

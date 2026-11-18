module

public import ArmillaryLean.Instances.Code9053
public import ArmillaryLean.Instances.CodeP181
public import ArmillaryLean.Instances.RoutedAnchors

@[expose] public section

/-!
# Exact distance obligations for 9053 and p181

The routed upper witnesses and the generic stabilizer reduction leave only
the stated finite reduced-anchor certificate families for each equality.
-/

namespace ArmillaryLean

open Routed (ReducedAnchors distance_ge_of_anchors)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)

namespace Code9053

/-- Two reduced anchor families at weight twelve suffice for distance fourteen. -/
theorem distance_eq_fourteen_of_anchors
    (xCert : ReducedAnchors params xGroups.get zGroups.get 12)
    (zCert : ReducedAnchors params zGroups.get xGroups.get 12) :
    cssDistance code = 14 := by
  apply le_antisymm distance_le_fourteen
  exact distance_ge_of_anchors params xGroups.get zGroups.get code rfl rfl
    14 (by decide) xCert zCert

end Code9053

namespace CodeP181

/-- Two reduced anchor families at weight fourteen suffice for distance sixteen. -/
theorem distance_eq_sixteen_of_anchors
    (xCert : ReducedAnchors params xGroups.get zGroups.get 14)
    (zCert : ReducedAnchors params zGroups.get xGroups.get 14) :
    cssDistance code = 16 := by
  apply le_antisymm distance_le_sixteen
  exact distance_ge_of_anchors params xGroups.get zGroups.get code rfl rfl
    16 (by decide) xCert zCert

end CodeP181

end ArmillaryLean

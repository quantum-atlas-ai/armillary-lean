module

public import ArmillaryLean.Instances.Exact8749
public import ArmillaryLean.Instances.MinProof8749.HeadX00
public import ArmillaryLean.Instances.MinProof8749.HeadX01
public import ArmillaryLean.Instances.MinProof8749.HeadX02
public import ArmillaryLean.Instances.MinProof8749.HeadX03
public import ArmillaryLean.Instances.MinProof8749.HeadX04
public import ArmillaryLean.Instances.MinProof8749.HeadX05
public import ArmillaryLean.Instances.MinProof8749.HeadX06
public import ArmillaryLean.Instances.MinProof8749.HeadX07
public import ArmillaryLean.Instances.MinProof8749.HeadX08
public import ArmillaryLean.Instances.MinProof8749.HeadX09
public import ArmillaryLean.Instances.MinProof8749.HeadX10
public import ArmillaryLean.Instances.MinProof8749.HeadX11
public import ArmillaryLean.Instances.MinProof8749.HeadX12
public import ArmillaryLean.Instances.MinProof8749.HeadX13
public import ArmillaryLean.Instances.MinProof8749.HeadX14
public import ArmillaryLean.Instances.MinProof8749.HeadX15
public import ArmillaryLean.Instances.MinProof8749.LateX
public import ArmillaryLean.Instances.MinProof8749.TailX
import Mathlib.Tactic.FinCases

@[expose] public section

namespace ArmillaryLean.Code8749

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)

set_option maxRecDepth 8192 in
/-- All minimum-rank obligations for the X-check matrix. -/
theorem minX : MinAnchorExclusions 0 := by
  intro b j s ha hm hz hw
  fin_cases b <;> fin_cases j
  · exact MinX00.verified s ha hm hz hw
  · exact MinX01.verified s ha hm hz hw
  · exact MinX02.verified s ha hm hz hw
  · exact MinX03.verified s ha hm hz hw
  · exact MinX04.verified s ha hm hz hw
  · exact MinX05.verified s ha hm hz hw
  · exact MinX06.verified s ha hm hz hw
  · exact MinX07.verified s ha hm hz hw
  · exact MinX08.verified s ha hm hz hw
  · exact MinX09.verified s ha hm hz hw
  · exact MinX10.verified s ha hm hz hw
  · exact MinX11.verified s ha hm hz hw
  · exact MinX12.verified s ha hm hz hw
  · exact MinX13.verified s ha hm hz hw
  · exact MinX14.verified s ha hm hz hw
  · exact MinX15.verified s ha hm hz hw
  · exact MinX16.verified s ha hm hz hw
  · exact MinX17.verified s ha hm hz hw
  · exact MinX18.verified s ha hm hz hw
  · exact MinX19.verified s ha hm hz hw
  · exact MinX20.verified s ha hm hz hw
  · exact MinX21.verified s ha hm hz hw
  · exact MinX22.verified s ha hm hz hw
  · exact MinX23.verified s ha hm hz hw
  · exact MinX24.verified s ha hm hz hw
  · exact MinX25.verified s ha hm hz hw
  · exact MinX26.verified s ha hm hz hw
  · exact MinX27.verified s ha hm hz hw
  · exact MinX28.verified s ha hm hz hw
  · exact MinX29.verified s ha hm hz hw
  · exact MinX30.verified s ha hm hz hw
  · exact MinX31.verified s ha hm hz hw
  · exact MinX32.verified s ha hm hz hw
  · exact last_block_anchor 0 _ s ha hm hz
  · exact last_block_anchor 0 _ s ha hm hz
  · exact last_block_anchor 0 _ s ha hm hz

/-- The actual Table S2 code has exact CSS distance twelve. -/
theorem distance_eq_twelve : cssDistance code = 12 := exact_of_min_x minX

#print axioms distance_eq_twelve

end ArmillaryLean.Code8749

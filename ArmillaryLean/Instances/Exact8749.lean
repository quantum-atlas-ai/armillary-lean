module

public import ArmillaryLean.Instances.Anchor8749
public import ArmillaryLean.Instances.Symmetry8749
public import ArmillaryLean.Instances.Upper8749
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Composition of the Armillary 8749 distance bounds

One anchored exclusion family for each check matrix proves the lower bound.
The weight-12 X witness supplies the matching upper bound.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion (ZeroSyndrome)
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)
open Qatlib.Concepts.ErrorCorrection.LogicalOps (distance_eq)
open scoped Matrix

/-- The anchor obligations for one check matrix at weight at most ten. -/
def AnchorExclusions (sector : Fin 2) : Prop :=
  ∀ (b : Fin 12) (j : Fin 3) (s : Finset Coord),
    (b, (0, j)) ∈ s → ZeroSyndrome (neighbors (retained sector)) s → s.card ≤ 10 → False

/-- Only supports whose anchor has minimum block and channel rank need be checked. -/
def MinAnchorExclusions (sector : Fin 2) : Prop :=
  ∀ (b : Fin 12) (j : Fin 3) (s : Finset Coord),
    (b, (0, j)) ∈ s → (∀ v ∈ s, anchorRank (b, (0, j)) ≤ anchorRank v) →
    ZeroSyndrome (neighbors (retained sector)) s → s.card ≤ 10 → False

/-- Minimum-rank anchors in the last block are excluded by the single-block argument. -/
theorem last_block_anchor (sector : Fin 2) (j : Fin 3) (s : Finset Coord)
    (ha : (11, (0, j)) ∈ s) (hm : ∀ v ∈ s, anchorRank (11, (0, j)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained sector)) s) : False := by
  apply single_block_excluded (retained sector) _ s ha _ hz
  intro v hv
  have hr := hm v hv
  change 3 * 11 + j.val ≤ 3 * v.1.val + v.2.2.val at hr
  have hb := v.1.isLt
  have hj := v.2.2.isLt
  apply Fin.ext
  change v.1.val = 11
  omega

set_option maxRecDepth 4096 in
/-- The support of either component is bounded by the Pauli weight. -/
private theorem componentWeights (e : PauliLabel Coord) :
    (supportOf e.1).card ≤ pauliWeight e.1 e.2 ∧
    (supportOf e.2).card ≤ pauliWeight e.1 e.2 := by
  constructor <;> apply Finset.card_le_card <;>
    intro c hc <;> rw [Finset.mem_filter] <;>
    exact ⟨Finset.mem_univ _, by
      have h := (Finset.mem_filter.mp hc).2
      first | exact Or.inl h | exact Or.inr h⟩

/-- A binary vector with empty support is zero. -/
private theorem empty_support_zero (v : Coord → ZMod 2) (h : supportOf v = ∅) : v = 0 := by
  rw [← bits_support v, h]
  funext c
  simp [bits]

set_option maxRecDepth 4096 in
/-- Vanishing of all small kernel supports gives the matching distance lower bound. -/
private theorem exact_of_empty
    (empty : ∀ (sector : Fin 2) (s : Finset Coord),
      ZeroSyndrome (neighbors (retained sector)) s → s.card ≤ 11 → s = ∅) :
    cssDistance code = 12 := by
  apply distance_eq code 12 upperLabel _ upper_syndrome upper_logical upperLabel_weight
  intro e hs hw
  have hweight : pauliWeight e.1 e.2 < 12 := by exact_mod_cast hw
  have hxw := (componentWeights e).1
  have hzw := (componentWeights e).2
  change (xChecks *ᵥ e.2, zChecks *ᵥ e.1) = (0, 0) at hs
  simp only [Prod.mk.injEq] at hs
  have hx : checks (retained 1) *ᵥ e.1 = 0 := by
    change zChecks *ᵥ e.1 = 0
    exact hs.2
  have hz : checks (retained 0) *ᵥ e.2 = 0 := by
    change xChecks *ᵥ e.2 = 0
    exact hs.1
  have hxs : supportOf e.1 = ∅ := by
    apply empty 1
    · apply (zero_iff (retained 1) _).mpr
      rw [bits_support]
      exact hx
    · omega
  have hzs : supportOf e.2 = ∅ := by
    apply empty 0
    · apply (zero_iff (retained 0) _).mpr
      rw [bits_support]
      exact hz
    · omega
  rw [show e = (0, 0) from Prod.ext (empty_support_zero e.1 hxs) (empty_support_zero e.2 hzs)]
  exact ⟨⟨0, map_zero _⟩, ⟨0, map_zero _⟩⟩

/-- The two anchored exclusion families and the verified witness give exact distance twelve. -/
theorem exact_of_anchors (xRows : AnchorExclusions 0) (zRows : AnchorExclusions 1) :
    cssDistance code = 12 := by
  apply exact_of_empty
  intro sector
  have hs : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases hs sector with rfl | rfl
  · exact all_anchors (retained 0) xRows
  · exact all_anchors (retained 1) zRows

/-- Scanning only the minimum-rank anchors also suffices to prove exact distance twelve. -/
theorem exact_of_min_anchors (xRows : MinAnchorExclusions 0) (zRows : MinAnchorExclusions 1) :
    cssDistance code = 12 := by
  apply exact_of_empty
  intro sector
  have hs : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases hs sector with rfl | rfl
  · exact all_min_anchors (retained 0) xRows
  · exact all_min_anchors (retained 1) zRows

/-- The checked graph isomorphism transfers the X-check exclusions to the other sector. -/
theorem exact_of_min_x (xRows : MinAnchorExclusions 0) : cssDistance code = 12 := by
  apply exact_of_empty
  intro sector
  have hs : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases hs sector with rfl | rfl
  · exact all_min_anchors (retained 0) xRows
  · intro s hz hw
    let t := s.map coordIso.symm.toEmbedding
    have h := all_min_anchors (retained 0) xRows t (zero_pullback s hz)
      (by simpa only [t, Finset.card_map] using hw)
    apply Finset.card_eq_zero.mp
    simpa only [t, Finset.card_map, Finset.card_empty] using congrArg Finset.card h

end ArmillaryLean.Code8749

module

public import ArmillaryLean.Instances.Css8749
public import Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance

@[expose] public section

/-!
# A weight-12 logical X operator for Armillary instance 8749

The support is paired within each retained Z group. The indicator of blocks
0 and 3 lies in the X-check kernel and has odd pairing with that support.
-/

namespace ArmillaryLean.Code8749

open Qatlib.Concepts.CodeCert.PermBlocks (permBlocks)
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)
open Qatlib.Concepts.ErrorCorrection.LogicalOps (distance_le)
open Qatlib.Papers.Armillary26.Instances (armEff)
open Qatlib.Papers.Armillary26.Pairing (sum_inv_zero)
open scoped Matrix

/-- Index the twelve entries in the witness support in their source order. -/
def upperAt (i : Fin 12) : Coord := upperSupport.get (Fin.cast upper_length.symm i)

/-- The indexed witness support contains no duplicated coordinates. -/
private theorem upperAt_inj : Function.Injective upperAt := by
  intro i j h
  have hi := upper_nodup.get_inj_iff.mp h
  exact Fin.ext (congrArg Fin.val hi)

/-- The indexed witness enumerates the source support. -/
private theorem upper_image : Finset.univ.image upperAt = upperSupport.toFinset := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem _ _
  · intro hv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
    refine ⟨Fin.cast upper_length i, ?_⟩
    change upperSupport.get i = v
    exact hi

/-- The binary indicator of the weight-12 witness support. -/
def upperBits (v : Coord) : ZMod 2 := if v ∈ upperSupport.toFinset then 1 else 0

/-- Dotting with the witness restricts the sum to the twelve listed coordinates. -/
private theorem upper_dot (v : Coord → ZMod 2) :
    dotProduct v upperBits = ∑ i : Fin 12, v (upperAt i) := by
  have hs : Finset.univ.filter (fun c => c ∈ upperSupport.toFinset) = upperSupport.toFinset := by
    ext c
    simp
  simp only [dotProduct, upperBits, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [hs, ← upper_image, Finset.sum_image upperAt_inj.injOn]

/-- Pair witness indices that hit the same Z row in each retained group. -/
def witnessPair (z : Fin 3) (i : Fin 12) : Fin 12 :=
  ((#v[#v[2, 5, 0, 4, 3, 1, 9, 10, 11, 6, 7, 8],
    #v[9, 10, 11, 8, 6, 7, 4, 5, 3, 0, 1, 2],
    #v[6, 7, 3, 2, 10, 11, 0, 1, 9, 8, 4, 5]] :
    Vector (Vector (Fin 12) 12) 3).get z).get i

/-- The check's internal coordinate reached by tracing a witness entry backwards. -/
def incoming (z : Fin 3) (i : Fin 12) : Cell :=
  (armEff params (zGroups.get z) (upperAt i).1).symm (upperAt i).2

set_option maxHeartbeats 0 in
/-- The paired witness indices trace back to the same actual Z check. -/
private theorem same_incoming : ∀ (z : Fin 3) (i : Fin 12),
    incoming z (witnessPair z i) = incoming z i := by
  decide +kernel

/-- An upper-witness entry contributes to exactly its incoming row in a given group. -/
private theorem witness_entry (r : Check) (i : Fin 12) :
    zChecks r (upperAt i) = if r.2 = incoming r.1 i then 1 else 0 := by
  let perm := armEff params (zGroups.get r.1) (upperAt i).1
  change (if perm r.2 = (upperAt i).2 then (1 : ZMod 2) else 0) = _
  have h : perm r.2 = (upperAt i).2 ↔ r.2 = incoming r.1 i := perm.eq_symm_apply.symm
  by_cases hr : r.2 = incoming r.1 i
  · rw [ite_eq_left (h.mpr hr), ite_eq_left hr]
  · rw [ite_eq_right (fun hp => hr (h.mp hp)), ite_eq_right hr]

/-- The weight-12 X witness has zero Z syndrome by rowwise pair cancellation. -/
theorem upper_zero : zChecks *ᵥ upperBits = 0 := by
  funext r
  change dotProduct (zChecks r) upperBits = 0
  rw [upper_dot]
  have hi : ∀ (z : Fin 3) (i : Fin 12), witnessPair z (witnessPair z i) = i := by decide
  have hf : ∀ (z : Fin 3) (i : Fin 12), witnessPair z i ≠ i := by decide
  refine sum_inv_zero _ (witnessPair r.1) (hi r.1) (hf r.1) ?_
  intro i
  simp only [witness_entry, same_incoming]

/-- The indicator of the two separating data blocks 0 and 3. -/
def separator (v : Coord) : ZMod 2 := if v.1 = 0 ∨ v.1 = 3 then 1 else 0

/-- A routed row reads one data coordinate per block. -/
private theorem check_read (groups : Fin 3 → Fin 12) (r : Check) (v : Coord → ZMod 2) :
    (checks groups *ᵥ v) r = ∑ b : Fin 12, v (visit (groups r.1) r.2 b) := by
  change (∑ c : Coord, checks groups r c * v c) = _
  rw [Fintype.sum_prod_type]
  simp [checks, permBlocks, visit, ite_mul]

/-- Each X row meets the separator twice, so the separator is in the X-check kernel. -/
theorem separator_zero : xChecks *ᵥ separator = 0 := by
  funext r
  change (checks xGroups.get *ᵥ separator) r = 0
  rw [check_read]
  change (∑ b : Fin 12, if b = 0 ∨ b = 3 then (1 : ZMod 2) else 0) = 0
  decide +kernel

/-- The witness intersects the two separating blocks in one coordinate. -/
theorem separator_dot : dotProduct separator upperBits = 1 := by
  rw [upper_dot]
  decide +kernel

/-- The pure X Pauli label given by the source witness. -/
def upperLabel : PauliLabel Coord := (upperBits, 0)

/-- Both components of the witness syndrome vanish. -/
theorem upper_syndrome : pauliSyndrome code upperLabel = (0, 0) := by
  change (xChecks *ᵥ 0, zChecks *ᵥ upperBits) = (0, 0)
  rw [Matrix.mulVec_zero, upper_zero]

set_option maxRecDepth 4096 in
/-- The separator excludes the witness from the X-stabilizer row space. -/
theorem upper_logical : ¬ IsStabilizerLabel code upperLabel := by
  intro hs
  obtain ⟨coeffs, hc⟩ := hs.1
  change xChecksᵀ *ᵥ coeffs = upperBits at hc
  have hz : dotProduct separator upperBits = 0 := by
    rw [← hc, Matrix.dotProduct_transpose_mulVec, separator_zero, dotProduct_zero]
  exact zero_ne_one (hz.symm.trans separator_dot)

set_option maxRecDepth 4096 in
/-- The pure X label has Pauli weight equal to its twelve physical coordinates. -/
theorem upperLabel_weight : pauliWeight upperLabel.1 upperLabel.2 = 12 := by
  have hs : Finset.univ.filter (fun i => upperBits i ≠ 0 ∨ (0 : Coord → ZMod 2) i ≠ 0) =
      upperSupport.toFinset := by
    ext v
    by_cases hv : v ∈ upperSupport.toFinset <;> simp [upperBits, hv, -List.mem_toFinset]
  unfold pauliWeight upperLabel
  rw [hs, upper_weight]

/-- The CSS distance of Armillary instance 8749 is at most 12. -/
theorem distance_le_twelve : cssDistance code ≤ 12 := by
  simpa only [upperLabel_weight, Nat.cast_ofNat] using
    distance_le code upperLabel upper_syndrome upper_logical

end ArmillaryLean.Code8749

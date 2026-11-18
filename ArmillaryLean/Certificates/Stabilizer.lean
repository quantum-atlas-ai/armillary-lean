module

public import Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Row reduction for CSS distance certificates

Toggling a stabilizer row reduces the Hamming weight whenever more than half
of that row is in the support. Each toggle preserves the opposite syndrome
and the stabilizer coset. A lower certificate can therefore check only
vectors that overlap every stabilizer row in at most half of its support.
-/

namespace ArmillaryLean.Stabilizer

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Concepts.ErrorCorrection.LogicalOps (distance_ge_iff)
open scoped Matrix

variable {ι κ κX κZ : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonzero support of a binary vector. -/
def support (v : ι → ZMod 2) : Finset ι := Finset.univ.filter fun i => v i ≠ 0

/-- Every support overlap is at most half of the corresponding stabilizer row. -/
def RowReduced (M : Matrix κ ι (ZMod 2)) (v : ι → ZMod 2) : Prop :=
  ∀ r, 2 * ((support v) ∩ (support (M r))).card ≤ bitWeight (M r)

/-- The support of a sum is the union of the two disjoint differences. -/
private theorem support_add (v w : ι → ZMod 2) :
    support (v + w) = (support v \ support w) ∪ (support w \ support v) := by
  ext i
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h (v i) with hv | hv <;> rcases h (w i) with hw | hw <;>
    simp [support, hv, hw, show (1 : ZMod 2) + 1 = 0 by decide]

/-- Toggling a row decreases weight if its overlap exceeds half of its weight. -/
private theorem toggle_lt (v w : ι → ZMod 2)
    (h : bitWeight w < 2 * ((support v) ∩ (support w)).card) :
    bitWeight (v + w) < bitWeight v := by
  change (support w).card < _ at h
  change (support (v + w)).card < (support v).card
  have hd : Disjoint (support v \ support w) (support w \ support v) := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  rw [support_add, Finset.card_union_of_disjoint hd]
  have hv := Finset.card_sdiff_add_card_inter (support v) (support w)
  have hw := Finset.card_sdiff_add_card_inter (support w) (support v)
  rw [Finset.inter_comm (support w) (support v)] at hw
  omega

variable [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
/-- A row belongs to the range of the transpose, using a unit coefficient vector. -/
private theorem row_mem (M : Matrix κ ι (ZMod 2)) (r : κ) :
    M r ∈ LinearMap.range (Matrix.mulVecLin Mᵀ) := by
  refine ⟨Pi.single r 1, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

/-- Every sufficiently small kernel vector is a stabilizer if its reduced forms are. -/
theorem mem_of_reduced {ρ : Type*} (opposite : Matrix ρ ι (ZMod 2))
    (rows : Matrix κ ι (ZMod 2)) (commute : opposite * rowsᵀ = 0) (d : ℕ)
    (accept : ∀ v, opposite *ᵥ v = 0 → bitWeight v < d → RowReduced rows v →
      v ∈ LinearMap.range (Matrix.mulVecLin rowsᵀ))
    (v : ι → ZMod 2) (zero : opposite *ᵥ v = 0) (weight : bitWeight v < d) :
    v ∈ LinearMap.range (Matrix.mulVecLin rowsᵀ) := by
  classical
  induction v using (measure (fun v : ι → ZMod 2 => bitWeight v)).wf.induction with
  | h v ih =>
    by_cases hr : RowReduced rows v
    · exact accept v zero weight hr
    · change ¬ (∀ r, _) at hr
      obtain ⟨r, hr⟩ := not_forall.mp hr
      obtain ⟨coeffs, hc⟩ := row_mem rows r
      have hrow : opposite *ᵥ rows r = 0 := by
        change rowsᵀ *ᵥ coeffs = rows r at hc
        rw [← hc, Matrix.mulVec_mulVec, commute, Matrix.zero_mulVec]
      have decrease := toggle_lt v (rows r) (Nat.lt_of_not_ge hr)
      have hsmall := ih (v + rows r) decrease
        (by rw [Matrix.mulVec_add, zero, hrow, add_zero])
        (decrease.trans weight)
      have hsum := (LinearMap.range (Matrix.mulVecLin rowsᵀ)).add_mem hsmall (row_mem rows r)
      simpa only [add_assoc, binary_add_self, add_zero] using hsum

variable [Fintype κX] [Fintype κZ] [DecidableEq κX] [DecidableEq κZ]

/-- Reduced checks for the two CSS sectors suffice to bound the Pauli distance. -/
theorem distance_ge_of_reduced (c : CssData ι κX κZ) (d : ℕ)
    (x : ∀ v, c.hZ *ᵥ v = 0 → bitWeight v < d → RowReduced c.hX v → v = 0)
    (z : ∀ v, c.hX *ᵥ v = 0 → bitWeight v < d → RowReduced c.hZ v → v = 0) :
    (d : ℕ∞) ≤ cssDistance c := by
  apply (distance_ge_iff c d).mpr
  intro e hs hw
  have hweight : pauliWeight e.1 e.2 < d := by exact_mod_cast hw
  have hz : c.hZ * c.hXᵀ = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose c.hcompat
  refine ⟨mem_of_reduced c.hZ c.hX hz d ?_ e.1 (congrArg Prod.snd hs)
      ((bitWeight_le_pauliWeight_left _ _).trans_lt hweight),
    mem_of_reduced c.hX c.hZ c.hcompat d ?_ e.2 (congrArg Prod.fst hs)
      ((bitWeight_le_pauliWeight_right _ _).trans_lt hweight)⟩
  · intro v hv hwt hr
    rw [x v hv hwt hr]
    exact Submodule.zero_mem _
  · intro v hv hwt hr
    rw [z v hv hwt hr]
    exact Submodule.zero_mem _

end ArmillaryLean.Stabilizer

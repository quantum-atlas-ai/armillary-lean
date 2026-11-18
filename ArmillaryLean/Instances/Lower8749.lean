module

public import ArmillaryLean.Certificates.Exclusion
public import ArmillaryLean.Instances.Code8749
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Reduction of the 8749 lower bound to anchored exclusions

Each retained row has one routed neighbour per block. Each column has three
checks in either sector, so zero syndrome forces even weight. Cyclic station
translation preserves the row neighbourhoods and moves any nonempty support
to one containing a station-zero anchor.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion (OddRow ZeroSyndrome)
open Qatlib.Concepts.CodeCert.PermBlocks (block_col_sum)
open scoped Matrix

/-- Enumerate a retained row's twelve data neighbours using the source route. -/
def neighbors (groups : Fin 3 → Fin 12) (r : Check) : Finset Coord :=
  Finset.univ.image (visit (groups r.1) r.2)

/-- A listed neighbour is exactly a nonzero entry of the actual check matrix. -/
theorem mem_neighbors (groups : Fin 3 → Fin 12) (r : Check) (v : Coord) :
    v ∈ neighbors groups r ↔ checks groups r v = 1 := by
  rw [check_iff, neighbors, Finset.mem_image]
  refine ⟨?_, fun h => ⟨v.1, Finset.mem_univ _, h⟩⟩
  rintro ⟨b, _, rfl⟩
  rfl

/-- The binary indicator of a finite support. -/
def bits (s : Finset Coord) (v : Coord) : ZMod 2 := if v ∈ s then 1 else 0

/-- The finite support of a binary vector. -/
def supportOf (v : Coord → ZMod 2) : Finset Coord := Finset.univ.filter fun c => v c ≠ 0

/-- The binary indicator recovers the vector from its support. -/
theorem bits_support (v : Coord → ZMod 2) : bits (supportOf v) = v := by
  funext c
  have hbin : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hbin (v c) with h | h <;> simp [bits, supportOf, h]

/-- Summation of a binary indicator counts an intersection modulo two. -/
private theorem sum_bits (s t : Finset Coord) :
    ∑ v ∈ s, bits t v = ((s.filter fun c => c ∈ t).card : ZMod 2) := by
  simp only [bits, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A check on a support is its routed neighbourhood's intersection parity. -/
theorem row_parity (groups : Fin 3 → Fin 12) (r : Check) (s : Finset Coord) :
    (checks groups *ᵥ bits s) r = (((neighbors groups r).filter fun c => c ∈ s).card : ZMod 2) := by
  rw [check_read]
  have hinj : Function.Injective (visit (groups r.1) r.2) :=
    fun _ _ h => congrArg Prod.fst h
  rw [← Finset.sum_image hinj.injOn, sum_bits]
  rfl

/-- The checker syndrome equals the actual binary matrix syndrome. -/
theorem zero_iff (groups : Fin 3 → Fin 12) (s : Finset Coord) :
    ZeroSyndrome (neighbors groups) s ↔ checks groups *ᵥ bits s = 0 := by
  simp only [ZeroSyndrome, OddRow, funext_iff, Pi.zero_apply, row_parity,
    ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  constructor <;> intro h r <;> have hr := h r <;> omega

/-- In either retained sector, the sum of any column is three in the binary field. -/
private theorem col_sum (groups : Fin 3 → Fin 12) (v : Coord) :
    (∑ r : Check, checks groups r v) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [checks, block_col_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  decide

/-- Every zero-syndrome support has even cardinality. -/
theorem card_even (groups : Fin 3 → Fin 12) (s : Finset Coord)
    (hz : ZeroSyndrome (neighbors groups) s) : s.card % 2 = 0 := by
  have hm := (zero_iff groups s).mp hz
  have htotal : (∑ r : Check, (checks groups *ᵥ bits s) r) = (s.card : ZMod 2) := by
    change (∑ r : Check, ∑ c : Coord, checks groups r c * bits s c) = _
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, col_sum, one_mul]
    simpa using sum_bits (Finset.univ : Finset Coord) s
  have hzero : (s.card : ZMod 2) = 0 := by simpa [hm] using htotal.symm
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hzero)

/-- Translation by a fixed amount is a bijection on the internal coordinates. -/
def cellShift (t : ZMod 101) : Cell ≃ Cell where
  toFun u := (u.1 + t, u.2)
  invFun u := (u.1 - t, u.2)
  left_inv u := by simp
  right_inv u := by simp

/-- Translate the station of every physical coordinate by the same amount. -/
def dataShift (t : ZMod 101) : Coord ≃ Coord := Equiv.prodCongr (Equiv.refl _) (cellShift t)

/-- Translate check coordinates by the same cyclic station amount. -/
def checkShift (t : ZMod 101) : Check ≃ Check := Equiv.prodCongr (Equiv.refl _) (cellShift t)

/-- Station translation carries every routed row neighbourhood to its translated row. -/
theorem neighbors_shift (groups : Fin 3 → Fin 12) (r : Check) (t : ZMod 101) :
    neighbors groups (checkShift t r) = (neighbors groups r).map (dataShift t).toEmbedding := by
  ext v
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨visit (groups r.1) r.2 b, ⟨b, rfl⟩, ?_⟩
    exact (visit_translate (groups r.1) b r.2 t).symm.trans hb
  · rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨b, (visit_translate (groups r.1) b r.2 t).trans hb⟩

/-- Translation preserves every row parity and hence zero syndrome. -/
theorem zero_shift (groups : Fin 3 → Fin 12) (s : Finset Coord) (t : ZMod 101)
    (hz : ZeroSyndrome (neighbors groups) s) :
    ZeroSyndrome (neighbors groups) (s.map (dataShift t).toEmbedding) := by
  intro r
  obtain ⟨r, rfl⟩ := (checkShift t).surjective r
  unfold OddRow
  rw [neighbors_shift]
  have hfilter : ((neighbors groups r).map (dataShift t).toEmbedding).filter
      (fun c => c ∈ s.map (dataShift t).toEmbedding) =
      ((neighbors groups r).filter fun c => c ∈ s).map (dataShift t).toEmbedding := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_map_equiv]
  rw [hfilter, Finset.card_map]
  exact hz r

/-- The station-zero anchors suffice to exclude all nonempty small supports. -/
theorem all_anchors (groups : Fin 3 → Fin 12)
    (hex : ∀ (b : Fin 12) (j : Fin 3) (s : Finset Coord),
      (b, (0, j)) ∈ s → ZeroSyndrome (neighbors groups) s → s.card ≤ 10 → False)
    (s : Finset Coord) (hz : ZeroSyndrome (neighbors groups) s) (hw : s.card ≤ 11) : s = ∅ := by
  by_contra hne
  obtain ⟨⟨b, i, j⟩, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hm := Finset.mem_map_of_mem (dataShift (-i)).toEmbedding hc
  have ha : (b, (0, j)) ∈ s.map (dataShift (-i)).toEmbedding := by
    simpa [dataShift, cellShift] using hm
  have hcard := card_even groups s hz
  apply hex b j _ ha (zero_shift groups s (-i) hz)
  rw [Finset.card_map]
  omega

/-- The lexicographic block and channel rank, independent of station. -/
def anchorRank (v : Coord) : Nat := 3 * v.1.val + v.2.2.val

/-- It suffices to check anchors of minimum block and channel rank in their support. -/
theorem all_min_anchors (groups : Fin 3 → Fin 12)
    (hex : ∀ (b : Fin 12) (j : Fin 3) (s : Finset Coord),
      (b, (0, j)) ∈ s → (∀ v ∈ s, anchorRank (b, (0, j)) ≤ anchorRank v) →
      ZeroSyndrome (neighbors groups) s → s.card ≤ 10 → False)
    (s : Finset Coord) (hz : ZeroSyndrome (neighbors groups) s) (hw : s.card ≤ 11) : s = ∅ := by
  by_contra hne
  obtain ⟨⟨b, i, j⟩, hc, hmin⟩ := Finset.exists_min_image s anchorRank
    (Finset.nonempty_iff_ne_empty.mpr hne)
  have hm := Finset.mem_map_of_mem (dataShift (-i)).toEmbedding hc
  have ha : (b, (0, j)) ∈ s.map (dataShift (-i)).toEmbedding := by
    simpa [dataShift, cellShift] using hm
  have hcard := card_even groups s hz
  refine hex b j _ ha ?_ (zero_shift groups s (-i) hz) ?_
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact hmin u hu
  · rw [Finset.card_map]
    omega

/-- A nonempty support contained in one block meets some routed check exactly once. -/
theorem single_block_excluded (groups : Fin 3 → Fin 12) (v : Coord) (s : Finset Coord)
    (hv : v ∈ s) (hb : ∀ w ∈ s, w.1 = v.1) (hz : ZeroSyndrome (neighbors groups) s) : False := by
  let r : Check := (0, (Qatlib.Papers.Armillary26.Instances.armEff params (groups 0) v.1).symm v.2)
  have hvisit : visit (groups r.1) r.2 v.1 = v := by
    let e := Qatlib.Papers.Armillary26.Instances.armEff params (groups 0) v.1
    change (v.1, e (e.symm v.2)) = v
    rw [Equiv.apply_symm_apply]
  have hfilter : ((neighbors groups r).filter fun c => c ∈ s) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_neighbors, check_iff]
    constructor
    · intro ⟨hcheck, hw⟩
      rw [hb w hw] at hcheck
      exact hcheck.symm.trans hvisit
    · rintro rfl
      exact ⟨hvisit, hv⟩
  apply hz r
  simp [OddRow, hfilter]

end ArmillaryLean.Code8749

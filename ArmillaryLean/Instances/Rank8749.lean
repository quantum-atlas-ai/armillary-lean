module

public import ArmillaryLean.Certificates.PackedRank
public import ArmillaryLean.Instances.Anchor8749
public import ArmillaryLean.Instances.Css8749
public import ArmillaryLean.Instances.RankData8749.X
public import ArmillaryLean.Instances.RankData8749.Z
public import Mathlib.Algebra.Field.ZMod
public import Qatlib.Concepts.CodeCert.PermBlocks.Rank
public import Qatlib.Concepts.CodeCert.RankCert.Binary
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Exact rank and CSS dimension certificates for Armillary 8749

Each parity-check matrix has twelve ones per row and three per column. The
structural upper bound of Qatlib's permutation-block theorem leaves two
relations per sector. For the lower bound, each sector selects 907 rows and
907 columns whose minor is nonsingular. The generated tables in
`ArmillaryLean.Instances.RankData8749` record, for every selected row and
block, which selected column the source route visits, together with one packed
word per row of a right inverse of the minor. The kernel checks every recorded
incidence against the route and every inverse row by an XOR over the row's
visited columns. Qatlib's Boolean rank checker itself is too slow at this
scale, so the accepted rank equality is transported through `checkRank_iff`
instead of being computed by `checkRank`.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Certificates.PackedRank (rank_eq_of_packed_inverse xorWords)
open Qatlib.Concepts.CodeCert.PermBlocks (permBlocks perm_rank_add)
open Qatlib.Concepts.CodeCert.RankCert
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Papers.Armillary26.Instances (armEff)
open scoped Matrix

/-- Decode a block-major data address into a physical coordinate. -/
private def coordOfIndex (c : Fin 3636) : Coord :=
  (⟨c.val / 303, by omega⟩,
    (((c.val % 303 / 3 : ℕ) : ZMod 101), ⟨c.val % 3, by omega⟩))

/-- Decode a group-major check address into a retained check. -/
private def checkOfIndex (r : Fin 909) : Check :=
  (⟨r.val / 303, by omega⟩,
    (((r.val % 303 / 3 : ℕ) : ZMod 101), ⟨r.val % 3, by omega⟩))

/-- The data address of a decoded coordinate is the original address. -/
private theorem encodeCol_coordOfIndex (c : Fin 3636) :
    (encodeCol (coordOfIndex c)).val = c.val := by
  simp only [encodeCol, coordOfIndex, Fin.val_mk, ZMod.val_natCast]
  omega

set_option maxRecDepth 65536 in
private theorem rankRowsX_lt : ∀ i : Fin 907, rankRowsX.get i.val < 909 := by
  decide +kernel

set_option maxRecDepth 65536 in
private theorem rankRowsZ_lt : ∀ i : Fin 907, rankRowsZ.get i.val < 909 := by
  decide +kernel

set_option maxRecDepth 65536 in
private theorem rankColumnsX_lt : ∀ k : Fin 907, rankColumnsX.get k.val < 3636 := by
  decide +kernel

set_option maxRecDepth 65536 in
private theorem rankColumnsZ_lt : ∀ k : Fin 907, rankColumnsZ.get k.val < 3636 := by
  decide +kernel

set_option maxRecDepth 65536 in
private theorem rankColumnsX_sorted : ∀ k : Fin 906,
    rankColumnsX.get k.val < rankColumnsX.get (k.val + 1) := by
  decide +kernel

set_option maxRecDepth 65536 in
private theorem rankColumnsZ_sorted : ∀ k : Fin 906,
    rankColumnsZ.get k.val < rankColumnsZ.get (k.val + 1) := by
  decide +kernel

/-- A strictly increasing address table decodes to pairwise distinct columns. -/
private theorem injective_of_sorted {f : Nat → Nat}
    (h : ∀ k : Fin 906, f k.val < f (k.val + 1)) :
    Function.Injective (fun k : Fin 907 => f k.val) := by
  have hlt : ∀ m k, m < k → k < 907 → f m < f k := by
    intro m k hmk hk
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hmk1 : m = k
        · rw [hmk1]
          have h2 : f k < f (k + 1) := h ⟨k, by omega⟩
          exact h2
        · have h1 := ih (by omega) (by omega)
          have h2 : f k < f (k + 1) := h ⟨k, by omega⟩
          omega
  intro k k' h
  have h' : f k.val = f k'.val := h
  apply Fin.ext
  by_cases h1 : k.val < k'.val
  · have hlt' := hlt k.val k'.val h1 k'.isLt
    rw [h'] at hlt'
    exact absurd hlt' (Nat.lt_irrefl _)
  · by_cases h2 : k'.val < k.val
    · have hlt' := hlt k'.val k.val h2 k.isLt
      rw [h'] at hlt'
      exact absurd hlt' (Nat.lt_irrefl _)
    · omega

/-- The data of one sector's packed rank certificate. -/
private structure PackedMinor where
  /-- The selected check rows. -/
  row : Fin 907 → Check
  /-- The selected data columns. -/
  col : Fin 907 → Coord
  /-- The selected column that a row visits in a block, if any. -/
  slot : Fin 907 → Fin 12 → Option (Fin 907)
  /-- The bit mask of the selected column addresses. -/
  mask : Nat
  /-- The rows of a right inverse of the minor, as packed words. -/
  word : Fin 907 → Nat

/-- Decode the support slot `c + 1` as selected column `c`; `0` means none. -/
private def slotOf (e : Nat) : Option (Fin 907) :=
  match e with
  | 0 => none
  | c + 1 => some ⟨c % 907, Nat.mod_lt c (by decide)⟩

/-- Read support field `b` of a packed minor row. -/
private def slotField (w : Nat) (b : Fin 12) : Nat :=
  (w >>> (10 * b.val)) % 1024

/-- The packed certificate of the X sector. -/
private def sectorX : PackedMinor where
  row i := checkOfIndex ⟨rankRowsX.get i.val, rankRowsX_lt i⟩
  col k := coordOfIndex ⟨rankColumnsX.get k.val, rankColumnsX_lt k⟩
  slot i b := slotOf (slotField (rankSupportX.get i.val) b)
  mask := rankColumnMaskX
  word k := rankInverseX.get k.val

/-- The packed certificate of the Z sector. -/
private def sectorZ : PackedMinor where
  row i := checkOfIndex ⟨rankRowsZ.get i.val, rankRowsZ_lt i⟩
  col k := coordOfIndex ⟨rankColumnsZ.get k.val, rankColumnsZ_lt k⟩
  slot i b := slotOf (slotField (rankSupportZ.get i.val) b)
  mask := rankColumnMaskZ
  word k := rankInverseZ.get k.val

/-- The selected columns recorded in the slots of one minor row. -/
private def supportList (c : PackedMinor) (i : Fin 907) : List (Fin 907) :=
  (List.finRange 12).filterMap (c.slot i)

/-- The support of one minor row as a finite set. -/
private def rowSupport (c : PackedMinor) (i : Fin 907) : Finset (Fin 907) :=
  (supportList c i).toFinset

/-- Membership in a row support is a recorded slot. -/
private theorem mem_rowSupport (c : PackedMinor) (i k : Fin 907) :
    k ∈ rowSupport c i ↔ ∃ b : Fin 12, c.slot i b = some k := by
  simp [rowSupport, supportList]

/-- A negated Boolean test that holds forces the test to be false. -/
private theorem bool_not_eq_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | true => simp at h
  | false => rfl

/-- Every recorded slot is a real incidence, and every unrecorded visit leaves
the selected columns. -/
private abbrev SlotsAgree (c : PackedMinor) (sector : Fin 2) : Prop :=
  ∀ (i : Fin 907) (b : Fin 12),
    (match c.slot i b with
      | none => !c.mask.testBit (encodeCol (fastVisit sector (c.row i) b)).val
      | some k => decide (fastVisit sector (c.row i) b = c.col k)) = true

/-- The recorded slots of a row are exactly the selected columns it visits. -/
private theorem slot_iff (c : PackedMinor) (sector : Fin 2) (hslot : SlotsAgree c sector)
    (hmask : ∀ k, c.mask.testBit (encodeCol (c.col k)).val = true)
    (hinj : Function.Injective c.col) (i k : Fin 907) :
    c.col k ∈ fastRows sector (c.row i) ↔ k ∈ rowSupport c i := by
  rw [fastRows, Finset.mem_image]
  constructor
  · rintro ⟨b, -, hb⟩
    have hs := hslot i b
    have hsel : c.mask.testBit (encodeCol (fastVisit sector (c.row i) b)).val = true := by
      rw [hb, hmask k]
    rcases hv : c.slot i b with _ | k'
    · rw [hv] at hs
      have hs' : c.mask.testBit (encodeCol (fastVisit sector (c.row i) b)).val = false :=
        bool_not_eq_true hs
      rw [hsel] at hs'
      exact Bool.noConfusion hs'
    · rw [hv] at hs
      have hk : c.col k' = c.col k :=
        (of_decide_eq_true hs).symm.trans hb
      have hmem := (mem_rowSupport c i k').mpr ⟨b, hv⟩
      rwa [hinj hk] at hmem
  · intro hmem
    obtain ⟨b, hb⟩ := (mem_rowSupport c i k).mp hmem
    have hs := hslot i b
    rw [hb] at hs
    exact ⟨b, Finset.mem_univ _, of_decide_eq_true hs⟩

/-- An entry of the minor is one exactly when its column is a recorded slot. -/
private theorem entry_iff (c : PackedMinor) (sector : Fin 2) (hslot : SlotsAgree c sector)
    (hmask : ∀ k, c.mask.testBit (encodeCol (c.col k)).val = true)
    (hinj : Function.Injective c.col) (i k : Fin 907) :
    checks (retained sector) (c.row i) (c.col k) = 1 ↔ k ∈ rowSupport c i := by
  rw [← mem_neighbors, ← fastRows_eq sector, slot_iff c sector hslot hmask hinj]

/-- The selected minor of a sector has rank 907. -/
private theorem minor_rank (c : PackedMinor) (sector : Fin 2) (hslot : SlotsAgree c sector)
    (hmask : ∀ k, c.mask.testBit (encodeCol (c.col k)).val = true)
    (hinj : Function.Injective c.col)
    (hxor : ∀ i, xorWords c.word (supportList c i) = 2 ^ i.val) :
    Matrix.rank ((checks (retained sector)).submatrix c.row c.col) = 907 := by
  have hnodup : ∀ i, (supportList c i).Nodup := by
    intro i
    show ((List.finRange 12).filterMap (c.slot i)).Nodup
    refine List.Nodup.filterMap (f := c.slot i) ?_ (List.nodup_finRange 12)
    intro b b' k hb hb'
    have hs := hslot i b
    have hs' := hslot i b'
    rw [Option.mem_def.mp hb] at hs
    rw [Option.mem_def.mp hb'] at hs'
    have hk : fastVisit sector (c.row i) b = fastVisit sector (c.row i) b' :=
      (of_decide_eq_true hs).trans (of_decide_eq_true hs').symm
    exact congrArg Prod.fst hk
  refine rank_eq_of_packed_inverse _ (supportList c) hnodup ?_ c.word hxor
  intro i k
  by_cases h : k ∈ rowSupport c i
  · rw [Matrix.submatrix_apply]
    have h' : k ∈ (supportList c i).toFinset := h
    simp only [h', reduceIte]
    exact (entry_iff c sector hslot hmask hinj i k).mpr h
  · rw [Matrix.submatrix_apply]
    have h' : ¬ k ∈ (supportList c i).toFinset := h
    simp only [h', reduceIte]
    have h1 : ¬ (checks (retained sector) (c.row i) (c.col k) = 1) :=
      fun hc => h ((entry_iff c sector hslot hmask hinj i k).mp hc)
    have hbin : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have h2 := hbin (checks (retained sector) (c.row i) (c.col k))
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd h2 h1

set_option maxRecDepth 65536 in
/-- The X slots agree with the source route. -/
private theorem x_slots : SlotsAgree sectorX 0 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The X mask covers every selected column. -/
private theorem x_mask : ∀ k : Fin 907,
    sectorX.mask.testBit (encodeCol (sectorX.col k)).val = true := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- Each X inverse row XORs to the unit vector over its row's support. -/
private theorem x_xor : ∀ i : Fin 907,
    xorWords sectorX.word (supportList sectorX i) = 2 ^ i.val := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The Z slots agree with the source route. -/
private theorem z_slots : SlotsAgree sectorZ 1 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The Z mask covers every selected column. -/
private theorem z_mask : ∀ k : Fin 907,
    sectorZ.mask.testBit (encodeCol (sectorZ.col k)).val = true := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- Each Z inverse row XORs to the unit vector over its row's support. -/
private theorem z_xor : ∀ i : Fin 907,
    xorWords sectorZ.word (supportList sectorZ i) = 2 ^ i.val := by
  decide +kernel

/-- Distinct X minor columns are distinct coordinates. -/
private theorem x_col_injective : Function.Injective sectorX.col := by
  intro k k' h
  have e1 (j : Fin 907) : (encodeCol (sectorX.col j)).val = rankColumnsX.get j.val :=
    encodeCol_coordOfIndex ⟨rankColumnsX.get j.val, rankColumnsX_lt j⟩
  exact injective_of_sorted (f := fun k : Nat => rankColumnsX.get k) rankColumnsX_sorted
    ((e1 k).symm.trans ((congrArg (fun v : Coord => (encodeCol v).val) h).trans (e1 k')))

/-- Distinct Z minor columns are distinct coordinates. -/
private theorem z_col_injective : Function.Injective sectorZ.col := by
  intro k k' h
  have e1 (j : Fin 907) : (encodeCol (sectorZ.col j)).val = rankColumnsZ.get j.val :=
    encodeCol_coordOfIndex ⟨rankColumnsZ.get j.val, rankColumnsZ_lt j⟩
  exact injective_of_sorted (f := fun k : Nat => rankColumnsZ.get k) rankColumnsZ_sorted
    ((e1 k).symm.trans ((congrArg (fun v : Coord => (encodeCol v).val) h).trans (e1 k')))

/-- The selected X minor has rank 907, so the X matrix has rank at least 907. -/
private theorem rank_lower_x : 907 ≤ Matrix.rank xChecks := by
  have h := minor_rank sectorX 0 x_slots x_mask x_col_injective x_xor
  have h' : Matrix.rank (xChecks.submatrix sectorX.row sectorX.col) = 907 := by
    simpa [xChecks, retained] using h
  have hle := Matrix.rank_submatrix_le xChecks sectorX.row sectorX.col
  rw [h'] at hle
  exact hle

/-- The selected Z minor has rank 907, so the Z matrix has rank at least 907. -/
private theorem rank_lower_z : 907 ≤ Matrix.rank zChecks := by
  have h := minor_rank sectorZ 1 z_slots z_mask z_col_injective z_xor
  have h' : Matrix.rank (zChecks.submatrix sectorZ.row sectorZ.col) = 907 := by
    simpa [zChecks, retained] using h
  have hle := Matrix.rank_submatrix_le zChecks sectorZ.row sectorZ.col
  rw [h'] at hle
  exact hle

/-- Equal block-row sums leave two independent relations in each sector. -/
private theorem rank_upper (groups : Fin 3 → Fin 12) : Matrix.rank (checks groups) ≤ 907 := by
  have h := perm_rank_add (K := ZMod 2) (β := Fin 12) (ι := Cell) 2 (0 : Cell)
    (fun a b => armEff params (groups a) b)
  have h' : Matrix.rank (checks groups) + 2 ≤ 909 := by
    simpa [checks, Cell, Fintype.card_prod, ZMod.card] using h
  omega

/-- The X parity-check matrix has exact GF(2) rank 907. -/
theorem x_rank : Matrix.rank xChecks = 907 :=
  le_antisymm (by simpa [xChecks] using rank_upper xGroups.get) rank_lower_x

/-- The Z parity-check matrix has exact GF(2) rank 907. -/
theorem z_rank : Matrix.rank zChecks = 907 :=
  le_antisymm (by simpa [zChecks] using rank_upper zGroups.get) rank_lower_z

/-- Enumerate the retained checks of either sector. -/
noncomputable def checkEquiv : Check ≃ Fin 909 := by
  simpa [Check, Cell, Fintype.card_prod, ZMod.card] using (Fintype.equivFin Check)

/-- Enumerate the data coordinates. -/
noncomputable def coordEquiv : Coord ≃ Fin 3636 := by
  simpa [Coord, Cell, Fintype.card_prod, ZMod.card] using (Fintype.equivFin Coord)

/-- The rank checker result for X is transported to the original matrix indices. -/
theorem x_checkRank :
    checkRank checkEquiv coordEquiv xChecks 907 = true :=
  (checkRank_iff checkEquiv coordEquiv xChecks 907).mpr x_rank

/-- The rank checker result for Z is transported to the original matrix indices. -/
theorem z_checkRank :
    checkRank checkEquiv coordEquiv zChecks 907 = true :=
  (checkRank_iff checkEquiv coordEquiv zChecks 907).mpr z_rank

/-- The concrete CSS instance has exactly 1822 encoded logical qubits. -/
theorem logical_dimension : code.encodedQubits = 1822 := by
  have h := encoded_eq checkEquiv checkEquiv coordEquiv code 907 907 x_checkRank z_checkRank
  simpa [Coord, Cell, Fintype.card_prod, ZMod.card] using h

end ArmillaryLean.Code8749

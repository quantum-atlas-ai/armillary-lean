module

public import ArmillaryLean.Instances.Anchor8749
public import ArmillaryLean.Certificates.Numeric
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Numeric incidence for the Armillary 8749 certificate

The source matrix is reindexed by the certificate's numeric addresses. A row
word is admitted when it agrees with the word constructed from the routed
neighbourhood; its validity is independent of the search generator.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion

/-- Embed physical coordinates in their numeric certificate addresses. -/
def colAddress : Coord ↪ Nat where
  toFun c := (encodeCol c).val
  inj' _ _ h := encodeCol_inj (Fin.ext h)

/-- The routed row neighbourhood in numeric coordinates. -/
def numericRows (sector : Fin 2) (address : Nat) : Finset Nat :=
  match decodeRow address with
  | none => ∅
  | some r => (fastRows sector r).map colAddress

/-- The address word built directly from the source row's routed neighbours. -/
def referenceWord (sector : Fin 2) (address : Nat) : Nat :=
  match decodeRow address with
  | none => 0
  | some r => Numeric.ofList ((List.finRange 12).map fun b => colAddress (fastVisit sector r b))

/-- The reference word represents the numeric neighbours in both directions. -/
theorem referenceWord_rep (sector : Fin 2) (address : Nat) :
    Numeric.Represents (referenceWord sector address) (numericRows sector address) := by
  cases he : decodeRow address with
  | none => simpa only [referenceWord, numericRows, he] using Numeric.represents_zero
  | some r =>
    simp only [referenceWord, numericRows, he]
    have hs : ((List.finRange 12).map fun b => colAddress (fastVisit sector r b)).toFinset =
        (fastRows sector r).map colAddress := by
      ext c
      simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and,
        Finset.mem_map, fastRows, Finset.mem_image, Finset.mem_univ]
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨fastVisit sector r b, ⟨b, rfl⟩, hb⟩
      · rintro ⟨_, ⟨b, rfl⟩, hb⟩
        exact ⟨b, hb⟩
    rw [← hs]
    exact Numeric.ofList_represents _

/-- Reindexing a physical zero-syndrome support preserves its syndrome. -/
theorem numericZero (sector : Fin 2) (s : Finset Coord)
    (hz : ZeroSyndrome (neighbors (retained sector)) s) :
    ZeroSyndrome (numericRows sector) (s.map colAddress) := by
  intro r
  cases he : decodeRow r with
  | none => simp [numericRows, he, OddRow]
  | some row =>
    simp only [numericRows, he]
    have hm : ((fastRows sector row).map colAddress).filter
        (fun c => c ∈ s.map colAddress) =
        ((fastRows sector row).filter fun v => v ∈ s).map colAddress := by
      ext c
      constructor
      · intro hc
        obtain ⟨hr, hs⟩ := Finset.mem_filter.mp hc
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hr
        exact Finset.mem_map.mpr ⟨v,
          Finset.mem_filter.mpr ⟨hv, (Finset.mem_map' colAddress).mp hs⟩, rfl⟩
      · intro hc
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hc
        obtain ⟨hrow, hv⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_map_of_mem colAddress hrow, Finset.mem_map_of_mem colAddress hv⟩
    unfold OddRow
    rw [hm, Finset.card_map, fastRows_eq]
    exact hz row

/-- Equality to the routed reference word suffices for numeric certificate soundness. -/
def CorrectWords (sector : Fin 2) (word : Nat → Nat) : Prop :=
  ∀ address : Nat, word address = referenceWord sector address

/-- A checked numeric anchor program excludes supports in the original source matrix. -/
theorem checkedNumeric {sector : Fin 2} {word : Nat → Nat} (hwords : CorrectWords sector word)
    {budget : Nat} {b : Fin 12} {j : Fin 3} {program : Program}
    (hc : Numeric.run word 909 3636 budget [colAddress (b, (0, j))]
      (Numeric.put 0 (colAddress (b, (0, j)))) program = true)
    {s : Finset Coord} (ha : (b, (0, j)) ∈ s)
    (hz : ZeroSyndrome (neighbors (retained sector)) s) (hw : s.card ≤ budget) : False := by
  let a := colAddress (b, (0, j))
  have hrows (r : Nat) : Numeric.Represents (word r) (numericRows sector r) := by
    rw [hwords r]
    exact referenceWord_rep sector r
  have hmark := Numeric.represents_put Numeric.represents_zero a
  have hs : ([a] : List Nat).toFinset ⊆ (insert a ∅ : Finset Nat) := by simp
  have hex := Numeric.run_excludes hrows (chosen := [a]) (decided := insert a ∅)
    (by simp) hs hmark hc
  have hmem : a ∈ s.map colAddress := Finset.mem_map_of_mem _ ha
  exact hex (by simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
    (show Extends {a} {a} (s.map colAddress) from
      ⟨Finset.singleton_subset_iff.mpr hmem, fun {_} _ hm => hm⟩))
    (numericZero sector s hz) (by simpa only [Finset.card_map] using hw)

/-- Rank of a valid numeric column address, ignoring its station. -/
def addressRank (c : Nat) : Nat := 3 * (c / 303) + c % 3

/-- The numeric rank agrees with the rank of the corresponding physical coordinate. -/
theorem addressRank_eq (v : Coord) : addressRank (colAddress v) = anchorRank v := by
  have hi := v.2.1.val_lt
  have hj := v.2.2.isLt
  change 3 * ((v.1.val * 303 + v.2.1.val * 3 + v.2.2.val) / 303) +
      (v.1.val * 303 + v.2.1.val * 3 + v.2.2.val) % 3 = 3 * v.1.val + v.2.2.val
  omega

/-- The mask for channels strictly earlier than `j`, across all 101 stations of a block. -/
def earlierChannels (j : Fin 3) : Nat := ((2 ^ 303 - 1) / 7) * (2 ^ j.val - 1)

set_option maxRecDepth 4096 in
/-- The earlier-channel mask has exactly the required bits in one block. -/
private theorem earlier_inside : ∀ (j : Fin 3) (i : Fin 303),
    (earlierChannels j).testBit i.val = decide (i.val % 3 < j.val) := by
  decide +kernel

set_option exponentiation.threshold 4096 in
/-- The earlier-channel mask is zero outside the block. -/
theorem earlier_test (j : Fin 3) (i : Nat) :
    (earlierChannels j).testBit i = decide (i < 303 ∧ i % 3 < j.val) := by
  by_cases hi : i < 303
  · simpa only [hi, true_and] using earlier_inside j ⟨i, hi⟩
  · have hs : ∀ j : Fin 3, earlierChannels j < 2 ^ 303 := by decide
    have hpow : 2 ^ 303 ≤ (2 : Nat) ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hs j) hpow)]
    simp [hi]

/-- Pre-mark the earlier block-channel ranks before starting a canonical anchor. -/
def earlierWord (b : Fin 12) (j : Fin 3) : Nat :=
  (2 ^ (303 * b.val) - 1) ||| (earlierChannels j <<< (303 * b.val))

/-- The semantic set of already forbidden columns in a minimum-rank branch. -/
def earlierSet (b : Fin 12) (j : Fin 3) : Finset Nat :=
  (Finset.range 3636).filter (fun c => addressRank c < 3 * b.val + j.val)

/-- The initial numeric mask represents exactly the earlier ranks. -/
theorem earlier_rep (b : Fin 12) (j : Fin 3) : Numeric.Represents (earlierWord b j) (earlierSet b j) := by
  intro n
  change (earlierWord b j).testBit n = true ↔
    n ∈ (Finset.range 3636).filter (fun c => addressRank c < 3 * b.val + j.val)
  rw [Finset.mem_filter, Finset.mem_range]
  simp only [earlierWord, Nat.testBit_or, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft,
    earlier_test, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, addressRank]
  have hb := b.isLt
  have hj := j.isLt
  omega

/-- A checked numeric program excludes a minimum-rank anchor in the original source rows. -/
theorem checkedMinNumeric {sector : Fin 2} {word : Nat → Nat} (hwords : CorrectWords sector word)
    {budget : Nat} {b : Fin 12} {j : Fin 3} {program : Program}
    (hc : Numeric.run word 909 3636 budget [colAddress (b, (0, j))]
      (Numeric.put (earlierWord b j) (colAddress (b, (0, j)))) program = true)
    {s : Finset Coord} (ha : (b, (0, j)) ∈ s)
    (hmin : ∀ v ∈ s, anchorRank (b, (0, j)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained sector)) s) (hw : s.card ≤ budget) : False := by
  let a := colAddress (b, (0, j))
  have hrows (r : Nat) : Numeric.Represents (word r) (numericRows sector r) := by
    rw [hwords r]
    exact referenceWord_rep sector r
  have hm := Numeric.represents_put (earlier_rep b j) a
  have hchosen : ([a] : List Nat).toFinset ⊆ insert a (earlierSet b j) := by simp
  have hex := Numeric.run_excludes hrows (chosen := [a]) (decided := insert a (earlierSet b j))
    (by simp) hchosen hm hc
  apply hex _ (numericZero sector s hz) (by simpa only [Finset.card_map] using hw)
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_map_of_mem _ ha), ?_⟩
  intro c hsupport hm
  rcases Finset.mem_insert.mp hm with rfl | hprior
  · exact Finset.mem_singleton_self _
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hsupport
    have hlt := (Finset.mem_filter.mp hprior).2
    rw [addressRank_eq] at hlt
    exact ((not_lt_of_ge (hmin v hv)) hlt).elim

end ArmillaryLean.Code8749

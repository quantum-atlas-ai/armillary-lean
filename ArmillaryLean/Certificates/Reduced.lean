module

public import ArmillaryLean.Certificates.XorPacking

@[expose] public section

/-!
# Numeric exclusion certificates with stabilizer overlap

A reduced support meets every stabilizer row in at most six columns.
The additional leaf checks that the already selected columns exceed this
limit. Packing leaves may also use pairwise XORs of the parity checks.
All addresses are checked before use, including stabilizer rows.
-/

namespace ArmillaryLean.Exclusion.Reduced

/-- Each stabilizer row meets the support in at most six places. -/
def OverlapSix (stabilizers : Rows Nat Nat) (s : Finset Nat) : Prop :=
  ∀ r, (s ∩ stabilizers r).card ≤ 6

/-- A checked state rules out all reduced zero-syndrome extensions. -/
def Excludes (rows stabilizers : Rows Nat Nat) (budget : Nat)
    (chosen marked : Finset Nat) : Prop :=
  ∀ ⦃s⦄, Extends chosen marked s → ZeroSyndrome rows s → s.card ≤ budget →
    OverlapSix stabilizers s → False

/-- The parity, stabilizer overlap, and XOR packing leaves with binary splits. -/
inductive Tree where
  | closed (row : Nat)
  | packing (rows : List Nat)
  | split (column : Nat) (yes no : Tree)
  | overlap (row : Nat)
  | xorPacking (pairs : List (Nat × Nat))

/-- Parse checked row pairs, with zero denoting an uncombined row. -/
def parsePairs (nr : Nat) : Nat → List Nat → Option (List (Nat × Nat) × List Nat)
  | 0, rest => some ([], rest)
  | n + 1, r :: s :: rest => do
      if nr ≤ r || nr < s then none else
        let (pairs, suffix) ← parsePairs nr n rest
        return ((r, s) :: pairs, suffix)
  | _, _ => none

/-- Unpack fourteen-bit addresses in little-endian order. -/
def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, payload => (payload &&& 16383) :: unpack n (payload >>> 14)

/-- A balanced stream of packed instructions. -/
def words : Program → List Nat
  | .chunk n p => unpack n p
  | .append left right => words left ++ words right

/-- Parse one reduced tree and return the unread suffix. -/
def parse (nr nc : Nat) : Nat → List Nat → Option (Tree × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: r :: rest =>
      if r < nr then some (.closed r, rest) else none
  | _ + 1, 1 :: count :: rest => do
      let (packed, suffix) ← parseRows (Numeric.bounded nr) count rest
      return (.packing packed, suffix)
  | fuel + 1, 2 :: c :: rest => do
      if nc ≤ c then none else
        let (yes, suffix) ← parse nr nc fuel rest
        let (no, suffix) ← parse nr nc fuel suffix
        return (.split c yes no, suffix)
  | _ + 1, 3 :: r :: rest =>
      if r < nr then some (.overlap r, rest) else none
  | _ + 1, 4 :: count :: rest => do
      let (pairs, suffix) ← parsePairs nr count rest
      return (.xorPacking pairs, suffix)
  | _ + 1, _ => none

/-- Evaluate a reduced certificate, maintaining the chosen columns and their marked bitmap. -/
def check (checks stabilizers : Nat → Nat) (budget : Nat)
    (chosen : List Nat) (marked : Nat) : Tree → Bool
  | .closed r => Numeric.check checks budget chosen marked (.closed r)
  | .packing rs => Numeric.check checks budget chosen marked (.packing rs)
  | .split c yes no =>
      let marked' := Numeric.put marked c
      !marked.testBit c && check checks stabilizers budget (c :: chosen) marked' yes &&
        check checks stabilizers budget chosen marked' no
  | .overlap r => 6 < chosen.countP (stabilizers r).testBit
  | .xorPacking pairs => XorPacking.check checks budget chosen marked pairs

/-- Reusing the two child exclusions proves the reduced exclusion at a split. -/
theorem split_excludes {rows stabilizers : Rows Nat Nat} {budget : Nat}
    {chosen marked : Finset Nat} (c : Nat)
    (yes : Excludes rows stabilizers budget (insert c chosen) (insert c marked))
    (no : Excludes rows stabilizers budget chosen (insert c marked)) :
    Excludes rows stabilizers budget chosen marked := by
  intro s he hz hw ho
  exact (split_extends c he).elim (fun h => yes h hz hw ho) (fun h => no h hz hw ho)

/-- A checked reduced tree excludes every consistent reduced support. -/
theorem check_sound {rows stabilizers : Rows Nat Nat} {checkWord stabWord : Nat → Nat}
    (hr : ∀ r, Numeric.Represents (checkWord r) (rows r))
    (hst : ∀ r, Numeric.Represents (stabWord r) (stabilizers r))
    {budget : Nat} (tree : Tree) {chosen : List Nat} {marked : Nat} {decided : Finset Nat}
    (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ decided)
    (hm : Numeric.Represents marked decided)
    (hc : check checkWord stabWord budget chosen marked tree = true) :
    Excludes rows stabilizers budget chosen.toFinset decided := by
  induction tree generalizing chosen marked decided with
  | closed r =>
      intro s he hz hw _
      exact sound (.closed r) (Numeric.check_refines hr (.closed r) hn hs hm hc) he hz hw
  | packing rs =>
      intro s he hz hw _
      exact sound (.packing rs) (Numeric.check_refines hr (.packing rs) hn hs hm hc) he hz hw
  | xorPacking pairs =>
      intro s he hz hw _
      exact XorPacking.sound hr hn hs hm pairs hc he hz hw
  | split c yes no ih₁ ih₂ =>
      obtain ⟨hleft, hno⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨hfresh, hyes⟩ := Bool.and_eq_true_iff.mp hleft
      have hnot : c ∉ chosen := by
        intro h
        have hb := (hm c).mpr (hs (List.mem_toFinset.mpr h))
        simp [hb] at hfresh
      have hm' := Numeric.represents_put hm c
      have hsub : (c :: chosen).toFinset ⊆ insert c decided := by
        simpa only [List.toFinset_cons] using Finset.insert_subset_insert c hs
      apply split_excludes c
      · simpa only [List.toFinset_cons] using
          ih₁ (List.nodup_cons.mpr ⟨hnot, hn⟩) hsub hm' hyes
      · exact ih₂ hn (hs.trans (Finset.subset_insert _ _)) hm' hno
  | overlap r =>
      intro s he _ _ ho
      have hi : (chosen.filter (stabWord r).testBit).toFinset = chosen.toFinset ∩ stabilizers r := by
        ext c
        simp only [List.mem_toFinset, List.mem_filter, hst r c, Finset.mem_inter]
      have hcard := congrArg Finset.card hi
      rw [List.toFinset_card_of_nodup (hn.filter _), ← List.countP_eq_length_filter] at hcard
      have hle := Finset.card_le_card
        (Finset.inter_subset_inter he.1 (subset_refl (stabilizers r)))
      change decide (6 < chosen.countP (stabWord r).testBit) = true at hc
      rw [← hcard] at hle
      exact (not_lt_of_ge (hle.trans (ho r))) (of_decide_eq_true hc)

/-- Run a complete reduced program from a given checkpoint. -/
def run (checks stabilizers : Nat → Nat) (nr nc budget : Nat)
    (chosen : List Nat) (marked : Nat) (program : Program) : Bool :=
  match parse nr nc 256 (words program) with
  | some (tree, []) => check checks stabilizers budget chosen marked tree
  | _ => false

/-- A complete accepted program proves the reduced exclusion at its checkpoint. -/
theorem run_excludes {rows stabilizers : Rows Nat Nat} {checkWord stabWord : Nat → Nat}
    (hr : ∀ r, Numeric.Represents (checkWord r) (rows r))
    (hst : ∀ r, Numeric.Represents (stabWord r) (stabilizers r))
    {nr nc budget : Nat} {chosen : List Nat} {marked : Nat} {decided : Finset Nat}
    {program : Program} (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ decided)
    (hm : Numeric.Represents marked decided)
    (hc : run checkWord stabWord nr nc budget chosen marked program = true) :
    Excludes rows stabilizers budget chosen.toFinset decided := by
  unfold run at hc
  split at hc
  · exact check_sound hr hst _ hn hs hm hc
  · contradiction

end ArmillaryLean.Exclusion.Reduced

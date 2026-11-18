module

public import ArmillaryLean.Certificates.Program
import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# An arithmetic checker for indexed exclusion trees

One natural number holds the marked columns. A packing leaf scans the rows
once, testing each neighbourhood against the union of the preceding rows.
All bits use the numeric row and column addresses from the program.
-/

namespace ArmillaryLean.Exclusion.Numeric

/-- A balanced lookup tree, indexed first by the low bit of the address. -/
inductive WordTree where
  | leaf (word : Nat)
  | fork (even odd : WordTree)

/-- Read a literal word without rebuilding the neighbourhood at every check. -/
def WordTree.get : WordTree → Nat → Nat
  | .leaf w, _ => w
  | .fork a b, n => if n % 2 == 0 then a.get (n / 2) else b.get (n / 2)

/-- A word represents a set through its test bits. -/
def Represents (word : Nat) (s : Finset Nat) : Prop :=
  ∀ i : Nat, word.testBit i = true ↔ i ∈ s

/-- Set the bit at one address. -/
def put (word i : Nat) : Nat := word ||| (1 <<< i)

/-- A single set bit represents insertion into a set. -/
theorem represents_put {word : Nat} {s : Finset Nat} (h : Represents word s) (i : Nat) :
    Represents (put word i) (insert i s) := by
  intro j
  simp only [put, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq, h j, Finset.mem_insert]
  exact ⟨fun h => h.elim Or.inr (fun he => Or.inl he.symm),
    fun h => h.elim (fun he => Or.inr he.symm) Or.inl⟩

/-- Zero has an empty bit support. -/
theorem represents_zero : Represents 0 ∅ := by intro i; simp

/-- Form a word from a list of bit addresses. -/
def ofList (xs : List Nat) : Nat := xs.foldr (fun c w => put w c) 0

/-- The word formed from a list represents its finite set of addresses. -/
theorem ofList_represents (xs : List Nat) : Represents (ofList xs) xs.toFinset := by
  induction xs with
  | nil => exact represents_zero
  | cons x xs ih =>
    rw [List.toFinset_cons]
    exact represents_put ih x

/-- Check that the first word's set bits are covered by the second. -/
def covered (required marked : Nat) : Bool := (required &&& marked) == required

/-- A successful coverage check implies bit containment. -/
theorem covered_bit {required marked i : Nat} (hc : covered required marked = true)
    (hr : required.testBit i = true) : marked.testBit i = true := by
  have he : required &&& marked = required := beq_iff_eq.mp hc
  have hb := congrArg (fun n : Nat => n.testBit i) he
  simpa only [Nat.testBit_and, hr, Bool.true_and] using hb

/-- Count the odd parity of the selected addresses in a row. -/
def parity (word : Nat) (chosen : List Nat) : Bool := (chosen.countP word.testBit % 2) == 1

/-- Accepted numeric parity gives an odd neighbourhood intersection. -/
theorem parity_sound {word : Nat} {row : Finset Nat} {chosen : List Nat}
    (h : Represents word row) (hn : chosen.Nodup) (hp : parity word chosen = true) :
    OddRow row chosen.toFinset := by
  have hset : (chosen.filter word.testBit).toFinset = row.filter (fun c => c ∈ chosen.toFinset) := by
    ext c
    simp only [List.mem_toFinset, List.mem_filter, h c, Finset.mem_filter]
    exact and_comm
  have hc := congrArg Finset.card hset
  rw [List.toFinset_card_of_nodup (hn.filter _)] at hc
  unfold OddRow
  rw [← hc, ← List.countP_eq_length_filter]
  exact beq_iff_eq.mp hp

/-- A packing scan checks distinct odd rows and coverage of all earlier overlaps. -/
def packValid (rowWord : Nat → Nat) (chosen : List Nat) (marked : Nat) :
    List Nat → Nat → Nat → Bool
  | [], _, _ => true
  | r :: rest, used, seen =>
      let word := rowWord r
      !seen.testBit r && parity word chosen && covered (word &&& used) marked &&
        packValid rowWord chosen marked rest (used ||| word) (put seen r)

/-- Facts recorded by an accepted packing scan against the preceding rows. -/
private def PackFacts (rows : Rows Nat Nat) (chosen marked : Finset Nat) (packed : List Nat)
    (used seen : Nat) : Prop :=
  packed.Nodup ∧ (∀ r ∈ packed, OddRow (rows r) chosen) ∧
    (∀ r ∈ packed, seen.testBit r = false) ∧
    (∀ r ∈ packed, ∀ c ∈ rows r \ marked, used.testBit c = false) ∧
    (∀ r ∈ packed, ∀ t ∈ packed, r ≠ t → Disjoint (rows r \ marked) (rows t \ marked))

/-- A packing scan checks both mutual disjointness and disjointness from the previous union. -/
private theorem packFacts {rowWord : Nat → Nat} {rows : Rows Nat Nat}
    (hrows : ∀ r, Represents (rowWord r) (rows r))
    {chosen : List Nat} (hn : chosen.Nodup) {marked : Nat} {decided : Finset Nat}
    (hm : Represents marked decided) {packed : List Nat} {used seen : Nat}
    (hc : packValid rowWord chosen marked packed used seen = true) :
    PackFacts rows chosen.toFinset decided packed used seen := by
  induction packed generalizing used seen with
  | nil => simp [PackFacts]
  | cons r rest ih =>
    obtain ⟨hp, ht⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨ho, hcov⟩ := Bool.and_eq_true_iff.mp hp
    obtain ⟨hfresh, hodd⟩ := Bool.and_eq_true_iff.mp ho
    obtain ⟨hd, hpo, hseen, hused, hdisj⟩ := ih ht
    have hnseen : r ∉ rest := by
      intro hr
      have hh := hseen r hr
      simp [put, Nat.one_shiftLeft] at hh
    have hrest_seen (t : Nat) (ht : t ∈ rest) : seen.testBit t = false := by
      have hh := hseen t ht
      unfold put at hh
      rw [Nat.testBit_or] at hh
      exact (Bool.or_eq_false_iff.mp hh).1
    have hrest_used (t c : Nat) (ht : t ∈ rest) (hc : c ∈ rows t \ decided) :
        used.testBit c = false ∧ (rowWord r).testBit c = false := by
      have hh := hused t ht c hc
      rw [Nat.testBit_or] at hh
      exact Bool.or_eq_false_iff.mp hh
    have hfirst (c : Nat) (hcr : c ∈ rows r \ decided) : used.testBit c = false := by
      have hbit := (hrows r c).mpr (Finset.mem_sdiff.mp hcr).1
      cases hu : used.testBit c with
      | false => rfl
      | true =>
        have hi : (rowWord r &&& used).testBit c = true := by
          rw [Nat.testBit_and, hbit, hu]; rfl
        exact ((Finset.mem_sdiff.mp hcr).2 ((hm c).mp (covered_bit hcov hi))).elim
    have hcross (t : Nat) (ht : t ∈ rest) : Disjoint (rows r \ decided) (rows t \ decided) := by
      apply Finset.disjoint_left.mpr
      intro c hr hc
      exact Bool.noConfusion (((hrows r c).mpr (Finset.mem_sdiff.mp hr).1).symm.trans
        (hrest_used t c ht hc).2)
    refine ⟨List.nodup_cons.mpr ⟨hnseen, hd⟩, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact parity_sound (hrows t) hn hodd
      · exact hpo t ht
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · cases Hb : seen.testBit t <;> simp_all
      · exact hrest_seen t ht
    · intro t ht c hmem
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hfirst c hmem
      · exact (hrest_used t c ht hmem).1
    · intro t ht u hu hne
      rcases List.mem_cons.mp ht with he | htr
      · subst t
        rcases List.mem_cons.mp hu with he | hur
        · exact (hne he.symm).elim
        · exact hcross u hur
      · rcases List.mem_cons.mp hu with he | hur
        · subst u
          exact (hcross t htr).symm
        · exact hdisj t htr u hur hne

/-- Evaluate the binary tree with arithmetic bitmaps. -/
def check (rowWord : Nat → Nat) (budget : Nat) (chosen : List Nat) (marked : Nat) :
    Tree Nat Nat → Bool
  | .closed r => parity (rowWord r) chosen && covered (rowWord r) marked
  | .packing rs => decide (budget < chosen.length + rs.length) && packValid rowWord chosen marked rs 0 0
  | .split c yes no =>
      let decided := put marked c
      !marked.testBit c && check rowWord budget (c :: chosen) decided yes &&
        check rowWord budget chosen decided no

/-- The arithmetic checker refines the finite-set checker. -/
theorem check_refines {rowWord : Nat → Nat} {rows : Rows Nat Nat}
    (hrows : ∀ r, Represents (rowWord r) (rows r)) {budget : Nat}
    (tree : Tree Nat Nat) {chosen : List Nat} {marked : Nat} {decided : Finset Nat}
    (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ decided) (hm : Represents marked decided)
    (hc : check rowWord budget chosen marked tree = true) :
    Exclusion.check rows budget chosen.toFinset decided tree = true := by
  induction tree generalizing chosen marked decided with
  | closed r =>
    obtain ⟨ho, hcov⟩ := Bool.and_eq_true_iff.mp hc
    apply decide_eq_true
    exact ⟨parity_sound (hrows r) hn ho, fun c hc => (hm c).mp (covered_bit hcov ((hrows r c).mpr hc))⟩
  | packing rs =>
    obtain ⟨hcount, hp⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hd, hodd, _, _, hdisj⟩ := packFacts hrows hn hm hp
    apply decide_eq_true
    refine ⟨?_, fun r hr => hodd r (List.mem_toFinset.mp hr), ?_⟩
    · rw [List.toFinset_card_of_nodup hn, List.toFinset_card_of_nodup hd]
      exact of_decide_eq_true hcount
    · intro r hr t ht hne
      exact hdisj r (List.mem_toFinset.mp hr) t (List.mem_toFinset.mp ht) hne
  | split c yes no ihy ihn =>
    obtain ⟨hleft, hr⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hfresh, hl⟩ := Bool.and_eq_true_iff.mp hleft
    have hnot : c ∉ chosen := by
      intro hh
      have hb := (hm c).mpr (hs (List.mem_toFinset.mpr hh))
      simp [hb] at hfresh
    have hm' := represents_put hm c
    have hs' : (c :: chosen).toFinset ⊆ insert c decided := by
      simpa only [List.toFinset_cons] using Finset.insert_subset_insert c hs
    have h₁ := ihy (List.nodup_cons.mpr ⟨hnot, hn⟩) hs' hm' hl
    have h₂ := ihn hn (hs.trans (Finset.subset_insert _ _)) hm' hr
    simp only [Exclusion.check, ← List.toFinset_cons, h₁, h₂, Bool.and_self]

/-- Decode a numeric address with an explicit upper bound. -/
def bounded (bound i : Nat) : Option Nat := if i < bound then some i else none

/-- Run a complete numeric program from a given branch state. -/
def run (rowWord : Nat → Nat) (nr nc budget : Nat) (chosen : List Nat) (marked : Nat)
    (program : Program) : Bool :=
  match parseTree (bounded nr) (bounded nc) 128 program.words with
  | some (tree, []) => check rowWord budget chosen marked tree
  | _ => false

/-- An accepted numeric program yields a reusable branch exclusion. -/
theorem run_excludes {rowWord : Nat → Nat} {rows : Rows Nat Nat}
    (hrows : ∀ r, Represents (rowWord r) (rows r)) {nr nc budget : Nat}
    {chosen : List Nat} {marked : Nat} {decided : Finset Nat} {program : Program}
    (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ decided) (hm : Represents marked decided)
    (hc : run rowWord nr nc budget chosen marked program = true) :
    Excluded rows budget chosen.toFinset decided := by
  intro support hext hz hw
  unfold run at hc
  split at hc
  · exact sound _ (check_refines hrows _ hn hs hm hc) hext hz hw
  · contradiction

end ArmillaryLean.Exclusion.Numeric

module

public import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Finite exclusion trees for binary checks

A state records selected columns and all columns already decided. An odd
row in the selected columns needs a further column in that row. A closed
leaf has no available such column. A packing leaf exhibits more odd rows
with disjoint available neighbourhoods than the budget permits.
-/

namespace ArmillaryLean.Exclusion

/-- Sparse row neighbourhoods of a binary check matrix. -/
abbrev Rows (Row Col : Type) := Row → Finset Col

/-- A row contains an odd number of selected columns. -/
def OddRow {Col : Type} [DecidableEq Col] (neighbors selected : Finset Col) : Prop :=
  (neighbors.filter fun c => c ∈ selected).card % 2 = 1

instance {Col : Type} [DecidableEq Col] (neighbors selected : Finset Col) :
    Decidable (OddRow neighbors selected) :=
  inferInstanceAs (Decidable (_ % 2 = 1))

/-- A support satisfies all homogeneous checks when every row has even parity. -/
def ZeroSyndrome {Row Col : Type} [DecidableEq Col]
    (rows : Rows Row Col) (support : Finset Col) : Prop :=
  ∀ r, ¬ OddRow (rows r) support

/-- A certificate either splits on a column or closes with one or more odd rows. -/
inductive Tree (Row Col : Type) where
  | split (column : Col) (selected forbidden : Tree Row Col)
  | closed (row : Row)
  | packing (rows : List Row)

/-- An admitted full support extends the selected columns and respects the decided columns. -/
def Extends {Col : Type} [DecidableEq Col] (selected marked support : Finset Col) : Prop :=
  selected ⊆ support ∧ ∀ ⦃c⦄, c ∈ support → c ∈ marked → c ∈ selected

/-- A branch state admits no satisfying extension within the weight budget. -/
def Excluded {Row Col : Type} [DecidableEq Col]
    (rows : Rows Row Col) (budget : Nat) (selected marked : Finset Col) : Prop :=
  ∀ ⦃support⦄, Extends selected marked support → ZeroSyndrome rows support →
    support.card ≤ budget → False

/-- Every consistent support extends at least one child of a binary split. -/
theorem split_extends {Col : Type} [DecidableEq Col] {selected marked support : Finset Col}
    (column : Col) (hext : Extends selected marked support) :
    Extends (insert column selected) (insert column marked) support ∨
      Extends selected (insert column marked) support := by
  by_cases hm : column ∈ support
  · refine Or.inl ⟨Finset.insert_subset hm hext.1, ?_⟩
    intro d hd hmark
    rcases Finset.mem_insert.mp hmark with rfl | hmark
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hext.2 hd hmark)
  · refine Or.inr ⟨hext.1, ?_⟩
    intro d hd hmark
    rcases Finset.mem_insert.mp hmark with rfl | hmark
    · exact (hm hd).elim
    · exact hext.2 hd hmark

/-- Excluding both children of a split excludes the parent branch state. -/
theorem split_excluded {Row Col : Type} [DecidableEq Col]
    {rows : Rows Row Col} {budget : Nat} {selected marked : Finset Col} (column : Col)
    (yes : Excluded rows budget (insert column selected) (insert column marked))
    (no : Excluded rows budget selected (insert column marked)) :
    Excluded rows budget selected marked := by
  intro support hext hz hw
  exact (split_extends column hext).elim (fun h => yes h hz hw) (fun h => no h hz hw)

/-- There are too many odd rows with pairwise disjoint available neighbourhoods. -/
def Packing {Row Col : Type} [DecidableEq Col]
    (rows : Rows Row Col) (budget : Nat) (selected marked : Finset Col)
    (packed : Finset Row) : Prop :=
  budget < selected.card + packed.card ∧
    (∀ r ∈ packed, OddRow (rows r) selected) ∧
    (∀ r ∈ packed, ∀ s ∈ packed, r ≠ s → Disjoint (rows r \ marked) (rows s \ marked))

instance {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    (rows : Rows Row Col) (budget : Nat) (selected marked : Finset Col) (packed : Finset Row) :
    Decidable (Packing rows budget selected marked packed) := by
  unfold Packing
  infer_instance

/-- Check all leaves and both children of each split. -/
def check {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    (rows : Rows Row Col) (budget : Nat) (selected marked : Finset Col) : Tree Row Col → Bool
  | .closed r => decide (OddRow (rows r) selected ∧ rows r ⊆ marked)
  | .packing packed => decide (Packing rows budget selected marked packed.toFinset)
  | .split c yes no =>
      check rows budget (insert c selected) (insert c marked) yes &&
      check rows budget selected (insert c marked) no

/-- Every currently odd row needs an available column in any satisfying extension. -/
theorem needs_extra {Col : Type} [DecidableEq Col] {neighbors selected marked support : Finset Col}
    (h : Extends selected marked support) (hodd : OddRow neighbors selected)
    (heven : ¬ OddRow neighbors support) :
    ∃ c ∈ neighbors \ marked, c ∈ support \ selected := by
  by_contra hn
  have hh : (neighbors.filter fun c => c ∈ selected) =
      (neighbors.filter fun c => c ∈ support) := by
    ext c
    simp only [Finset.mem_filter]
    refine ⟨fun hc => ⟨hc.1, h.1 hc.2⟩, fun hc => ⟨hc.1, ?_⟩⟩
    by_contra hmiss
    have hfree : c ∉ marked := fun hm => hmiss (h.2 hc.2 hm)
    exact hn ⟨c, Finset.mem_sdiff.mpr ⟨hc.1, hfree⟩, Finset.mem_sdiff.mpr ⟨hc.2, hmiss⟩⟩
  exact heven (by simpa only [OddRow, ← hh] using hodd)

/-- A certified packing contradicts the weight budget of any satisfying extension. -/
theorem packing_excludes {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {rows : Rows Row Col} {budget : Nat} {selected marked support : Finset Col}
    {packed : Finset Row} (hp : Packing rows budget selected marked packed)
    (h : Extends selected marked support) (hz : ZeroSyndrome rows support)
    (hw : support.card ≤ budget) : False := by
  classical
  have hex (r : {r // r ∈ packed}) := needs_extra h (hp.2.1 r.1 r.2) (hz r.1)
  let f (r : {r // r ∈ packed}) : Col := Classical.choose (hex r)
  have hf (r : {r // r ∈ packed}) :
      f r ∈ rows r.1 \ marked ∧ f r ∈ support \ selected := Classical.choose_spec (hex r)
  have hi : Function.Injective f := by
    intro r s heq
    by_contra hne
    have hd := hp.2.2 r.1 r.2 s.1 s.2 (fun he => hne (Subtype.ext he))
    exact (Finset.disjoint_left.mp hd (hf r).1) (heq ▸ (hf s).1)
  have hcard : packed.card ≤ (support \ selected).card := by
    rw [← Finset.card_attach (s := packed)]
    exact Finset.card_le_card_of_injOn f (fun r _ => (hf r).2) hi.injOn
  rw [Finset.card_sdiff_of_subset h.1] at hcard
  have hsub := Finset.card_le_card h.1
  have hbudget := hp.1
  omega

/-- An accepted tree excludes every support consistent with the initial branch state. -/
theorem sound {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {rows : Rows Row Col} {budget : Nat} {support : Finset Col}
    (tree : Tree Row Col) {selected marked : Finset Col}
    (hcheck : check rows budget selected marked tree = true)
    (hext : Extends selected marked support) (hz : ZeroSyndrome rows support)
    (hw : support.card ≤ budget) : False := by
  induction tree generalizing selected marked with
  | closed r =>
    have hp : OddRow (rows r) selected ∧ rows r ⊆ marked := of_decide_eq_true hcheck
    obtain ⟨c, hc, _⟩ := needs_extra hext hp.1 (hz r)
    exact (Finset.mem_sdiff.mp hc).2 (hp.2 (Finset.mem_sdiff.mp hc).1)
  | packing packed =>
    exact packing_excludes (of_decide_eq_true hcheck) hext hz hw
  | split c yes no hyes hno =>
    have hc := Bool.and_eq_true_iff.mp hcheck
    exact (split_extends c hext).elim (hyes hc.1) (hno hc.2)

/-- An accepted tree starting with one selected column excludes supports containing that anchor. -/
theorem anchor_excludes {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {rows : Rows Row Col} {budget : Nat} {support : Finset Col} {anchor : Col}
    {tree : Tree Row Col} (hcheck : check rows budget {anchor} {anchor} tree = true)
    (ha : anchor ∈ support) (hz : ZeroSyndrome rows support) (hw : support.card ≤ budget) : False :=
  sound tree hcheck ⟨Finset.singleton_subset_iff.mpr ha, fun {_} _ hm => hm⟩ hz hw

end ArmillaryLean.Exclusion

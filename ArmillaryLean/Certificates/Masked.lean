module

public import ArmillaryLean.Certificates.Mask
public import ArmillaryLean.Certificates.Program
import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# A masked checker for exclusion trees

The evaluator only keeps a short list of selected columns and the mask of
all decided columns. Its acceptance implies acceptance by the finite-set
checker, whose soundness accounts for the forbidden columns.
-/

namespace ArmillaryLean.Exclusion

/-- Bit membership represents membership in a finite set of physical columns. -/
def Represents {Col : Type} (encode : Col → Fin 4096) (m : Mask) (s : Finset Col) : Prop :=
  ∀ c, m.has (encode c) = true ↔ c ∈ s

/-- Setting an address models inserting the uniquely encoded column. -/
theorem represents_put {Col : Type} [DecidableEq Col] {encode : Col → Fin 4096}
    (hinj : Function.Injective encode) {m : Mask} {s : Finset Col}
    (hm : Represents encode m s) (c : Col) : Represents encode (m.put (encode c)) (insert c s) := by
  intro d
  simp only [Mask.has_put, Bool.or_eq_true, decide_eq_true_eq, hm d, Finset.mem_insert]
  exact ⟨fun h => h.elim Or.inr (fun hcd => Or.inl (hinj hcd).symm),
    fun h => h.elim (fun hdc => Or.inr (congrArg encode hdc.symm)) Or.inl⟩

/-- Count selected bits of a row mask modulo two. -/
def oddBits {Col : Type} (encode : Col → Fin 4096) (row : Mask) (selected : List Col) : Bool :=
  selected.countP (fun c => row.has (encode c)) % 2 == 1

/-- Bit parity is the parity of the corresponding neighbourhood intersection. -/
theorem oddBits_sound {Col : Type} [DecidableEq Col] {encode : Col → Fin 4096}
    {row : Mask} {neighbors : Finset Col} {selected : List Col}
    (hm : Represents encode row neighbors) (hn : selected.Nodup)
    (ho : oddBits encode row selected = true) : OddRow neighbors selected.toFinset := by
  have hset : (selected.filter fun c => row.has (encode c)).toFinset =
      neighbors.filter (fun c => c ∈ selected.toFinset) := by
    ext c
    simp only [List.mem_toFinset, List.mem_filter, hm c, Finset.mem_filter]
    exact and_comm
  have hc := congrArg Finset.card hset
  rw [List.toFinset_card_of_nodup (hn.filter _)] at hc
  unfold OddRow
  rw [← hc, ← List.countP_eq_length_filter]
  exact beq_iff_eq.mp ho

/-- Verify exclusion leaves using sparse parity and chunkwise mask coverage. -/
def maskCheck {Row Col : Type} [DecidableEq Row]
    (encode : Col → Fin 4096) (rowMask : Row → Mask) (budget : Nat)
    (selected : List Col) (marked : Mask) : Tree Row Col → Bool
  | .closed r => oddBits encode (rowMask r) selected && (rowMask r).covered marked
  | .packing rs =>
      decide (budget < selected.length + rs.length) && decide rs.Nodup &&
      rs.all (fun r => oddBits encode (rowMask r) selected) &&
      rs.all (fun r => rs.all (fun t =>
        decide (r = t) || ((rowMask r).inter (rowMask t)).covered marked))
  | .split c yes no =>
      !(marked.has (encode c)) &&
      maskCheck encode rowMask budget (c :: selected) (marked.put (encode c)) yes &&
      maskCheck encode rowMask budget selected (marked.put (encode c)) no

/-- A successful mask check implies acceptance by the finite-set checker. -/
theorem maskCheck_refines {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {encode : Col → Fin 4096} {rowMask : Row → Mask} {rows : Rows Row Col}
    (hinj : Function.Injective encode) (hrows : ∀ r, Represents encode (rowMask r) (rows r))
    {budget : Nat} (tree : Tree Row Col) {selected : List Col} {marked : Mask} {decided : Finset Col}
    (hn : selected.Nodup) (hs : selected.toFinset ⊆ decided) (hm : Represents encode marked decided)
    (hc : maskCheck encode rowMask budget selected marked tree = true) :
    check rows budget selected.toFinset decided tree = true := by
  induction tree generalizing selected marked decided with
  | closed r =>
    obtain ⟨ho, hcov⟩ := Bool.and_eq_true_iff.mp hc
    apply decide_eq_true
    refine ⟨oddBits_sound (hrows r) hn ho, fun c hmem => ?_⟩
    exact (hm c).mp (Mask.covered_has hcov ((hrows r c).mpr hmem))
  | packing rs =>
    obtain ⟨hpartial, hcov⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hsize, hodd⟩ := Bool.and_eq_true_iff.mp hpartial
    obtain ⟨hcount, hrn⟩ := Bool.and_eq_true_iff.mp hsize
    have hnodup : rs.Nodup := of_decide_eq_true hrn
    apply decide_eq_true
    refine ⟨?_, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup hn, List.toFinset_card_of_nodup hnodup]
      exact of_decide_eq_true hcount
    · intro r hr
      have ho := List.all_eq_true.mp hodd r (List.mem_toFinset.mp hr)
      exact oddBits_sound (hrows r) hn ho
    · intro r hr q hq hne
      have hall := List.all_eq_true.mp hcov r (List.mem_toFinset.mp hr)
      have hpair := List.all_eq_true.mp hall q (List.mem_toFinset.mp hq)
      have hcovered : ((rowMask r).inter (rowMask q)).covered marked = true := by
        simpa only [decide_eq_false hne, Bool.false_or] using hpair
      apply Finset.disjoint_left.mpr
      intro c hc1 hc2
      obtain ⟨hrc, hfree⟩ := Finset.mem_sdiff.mp hc1
      have hqc := (Finset.mem_sdiff.mp hc2).1
      have hbit : ((rowMask r).inter (rowMask q)).has (encode c) = true := by
        rw [Mask.has_inter, (hrows r c).mpr hrc, (hrows q c).mpr hqc]
        rfl
      exact hfree ((hm c).mp (Mask.covered_has hcovered hbit))
  | split c yes no ihy ihn =>
    obtain ⟨hleft, hno⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hfresh, hy⟩ := Bool.and_eq_true_iff.mp hleft
    have hnot : c ∉ selected := by
      intro hmem
      have hb := (hm c).mpr (hs (List.mem_toFinset.mpr hmem))
      simp [hb] at hfresh
    have hm' := represents_put hinj hm c
    have hs' : (c :: selected).toFinset ⊆ insert c decided := by
      simpa only [List.toFinset_cons] using Finset.insert_subset_insert c hs
    have hyes := ihy (List.nodup_cons.mpr ⟨hnot, hn⟩) hs' hm' hy
    have hno' := ihn hn (hs.trans (Finset.subset_insert _ _)) hm' hno
    simp only [check, ← List.toFinset_cons, hyes, hno', Bool.and_self]

/-- Run a complete packed subtree from a specified checkpoint state. -/
def maskProgramFrom {Row Col : Type} [DecidableEq Row]
    (encode : Col → Fin 4096) (rowMask : Row → Mask) (row : Nat → Option Row)
    (col : Nat → Option Col) (budget depth : Nat) (selected : List Col) (marked : Mask)
    (program : Program) : Bool :=
  match parseTree row col depth program.words with
  | some (tree, []) => maskCheck encode rowMask budget selected marked tree
  | _ => false

/-- Run the masked checker from a single initial anchor. -/
def maskProgram {Row Col : Type} [DecidableEq Row]
    (encode : Col → Fin 4096) (rowMask : Row → Mask) (row : Nat → Option Row)
    (col : Nat → Option Col) (budget depth : Nat) (anchor : Col) (program : Program) : Bool :=
  maskProgramFrom encode rowMask row col budget depth [anchor] (Mask.empty.put (encode anchor)) program

/-- Accepted subtrees prove reusable exclusions at their starting checkpoints. -/
theorem maskProgramFrom_excludes {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {encode : Col → Fin 4096} {rowMask : Row → Mask} {rows : Rows Row Col}
    (hinj : Function.Injective encode) (hrows : ∀ r, Represents encode (rowMask r) (rows r))
    {row : Nat → Option Row} {col : Nat → Option Col} {budget depth : Nat}
    {selected : List Col} {marked : Mask} {decided : Finset Col} {program : Program}
    (hn : selected.Nodup) (hs : selected.toFinset ⊆ decided) (hm : Represents encode marked decided)
    (hcheck : maskProgramFrom encode rowMask row col budget depth selected marked program = true) :
    Excluded rows budget selected.toFinset decided := by
  intro support hext hz hw
  unfold maskProgramFrom at hcheck
  split at hcheck
  · exact sound _ (maskCheck_refines hinj hrows _ hn hs hm hcheck) hext hz hw
  · contradiction

/-- The masked checker certifies the same anchored exclusion as the finite-set checker. -/
theorem maskProgram_excludes {Row Col : Type} [DecidableEq Row] [DecidableEq Col]
    {encode : Col → Fin 4096} {rowMask : Row → Mask} {rows : Rows Row Col}
    (hinj : Function.Injective encode) (hrows : ∀ r, Represents encode (rowMask r) (rows r))
    {row : Nat → Option Row} {col : Nat → Option Col} {budget depth : Nat} {anchor : Col}
    {program : Program} {support : Finset Col}
    (hcheck : maskProgram encode rowMask row col budget depth anchor program = true)
    (ha : anchor ∈ support) (hz : ZeroSyndrome rows support) (hw : support.card ≤ budget) : False := by
  have h0 : Represents encode Mask.empty (∅ : Finset Col) := by
    intro c
    simp [Mask.has, Mask.empty]
  have hsingle := represents_put hinj h0 anchor
  have hex := maskProgramFrom_excludes hinj hrows (selected := [anchor]) (decided := {anchor})
    (by simp) (by simp) hsingle hcheck
  apply hex _ hz hw
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
    (show Extends {anchor} {anchor} support from
      ⟨Finset.singleton_subset_iff.mpr ha, fun {_} _ hm => hm⟩)

end ArmillaryLean.Exclusion

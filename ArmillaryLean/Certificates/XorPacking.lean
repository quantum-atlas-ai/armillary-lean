module

public import ArmillaryLean.Certificates.Numeric
public import Mathlib.Data.Finset.SymmDiff
import Lean.Elab.Tactic.Omega

@[expose] public section

open scoped symmDiff

namespace ArmillaryLean.Exclusion.XorPacking

/-- Restricting to a support commutes with symmetric difference. -/
private theorem filter_xor (u v s : Finset Nat) :
    (u ∆ v).filter (· ∈ s) = u.filter (· ∈ s) ∆ v.filter (· ∈ s) := by
  ext c
  by_cases h : c ∈ s <;> simp [Finset.mem_symmDiff, h]

/-- The parity of an intersection is additive under symmetric difference. -/
private theorem even_xor {u v s : Finset Nat}
    (hu : ¬ OddRow u s) (hv : ¬ OddRow v s) : ¬ OddRow (u ∆ v) s := by
  unfold OddRow at *
  rw [filter_xor]
  let a := u.filter (· ∈ s)
  let b := v.filter (· ∈ s)
  change ¬ (a ∆ b).card % 2 = 1
  change ¬ a.card % 2 = 1 at hu
  change ¬ b.card % 2 = 1 at hv
  have hd : Disjoint (a \ b) (b \ a) := by
    apply Finset.disjoint_left.mpr
    intro c hc₁ hc₂
    exact (Finset.mem_sdiff.mp hc₁).2 (Finset.mem_sdiff.mp hc₂).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have ha := Finset.card_sdiff_add_card_inter a b
  have hb := Finset.card_sdiff_add_card_inter b a
  rw [Finset.inter_comm b a] at hb
  omega

/-- Numeric XOR represents symmetric difference of the row sets. -/
private theorem represents_xor {x y : Nat} {u v : Finset Nat}
    (hx : Numeric.Represents x u) (hy : Numeric.Represents y v) :
    Numeric.Represents (x ^^^ y) (u ∆ v) := by
  intro i
  rw [Nat.testBit_xor, Finset.mem_symmDiff]
  simp only [← hx i, ← hy i]
  cases x.testBit i <;> cases y.testBit i <;> decide

/-- A pair `(r, 0)` takes the original row; a pair `(r, s+1)` combines two rows. -/
def derivedRows (rows : Rows Nat Nat) (pairs : List (Nat × Nat)) (i : Nat) : Finset Nat :=
  match pairs[i]? with
  | some (r, 0) => rows r
  | some (r, s + 1) => rows r ∆ rows s
  | none => ∅

/-- The same row combination on the cached numeric row words. -/
def derivedWords (rowWord : Nat → Nat) (pairs : List (Nat × Nat)) (i : Nat) : Nat :=
  match pairs[i]? with
  | some (r, 0) => rowWord r
  | some (r, s + 1) => rowWord r ^^^ rowWord s
  | none => 0

/-- The derived numeric rows represent the derived sets. -/
private theorem derived_rep {rowWord : Nat → Nat} {rows : Rows Nat Nat}
    (hr : ∀ r, Numeric.Represents (rowWord r) (rows r))
    (pairs : List (Nat × Nat)) (i : Nat) :
    Numeric.Represents (derivedWords rowWord pairs i) (derivedRows rows pairs i) := by
  rcases h : pairs[i]? with - | ⟨r, s⟩
  · simpa [derivedWords, derivedRows, h] using Numeric.represents_zero
  · cases s with
    | zero => simpa [derivedWords, derivedRows, h] using hr r
    | succ s =>
      simpa [derivedWords, derivedRows, h] using represents_xor (hr r) (hr s)

/-- A zero syndrome for the source rows implies a zero syndrome for the derived rows. -/
private theorem derived_zero {rows : Rows Nat Nat} {s : Finset Nat}
    (hz : ZeroSyndrome rows s) (pairs : List (Nat × Nat)) :
    ZeroSyndrome (derivedRows rows pairs) s := by
  intro i
  rcases h : pairs[i]? with - | ⟨r, t⟩
  · simp [derivedRows, h, OddRow]
  · cases t with
    | zero => simpa [derivedRows, h] using hz r
    | succ t => simpa [derivedRows, h] using even_xor (hz r) (hz t)

/-- Reuse the existing numeric packing checker on virtual XOR row addresses. -/
def check (rowWord : Nat → Nat) (budget : Nat) (chosen : List Nat)
    (marked : Nat) (pairs : List (Nat × Nat)) : Bool :=
  Numeric.check (derivedWords rowWord pairs) budget chosen marked (.packing (List.range pairs.length))

/-- A verified XOR packing excludes the original kernel's small extensions. -/
theorem sound {rowWord : Nat → Nat} {rows : Rows Nat Nat}
    (hr : ∀ r, Numeric.Represents (rowWord r) (rows r)) {budget : Nat}
    {chosen : List Nat} {marked : Nat} {decided : Finset Nat}
    (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ decided)
    (hm : Numeric.Represents marked decided) (pairs : List (Nat × Nat))
    (hc : check rowWord budget chosen marked pairs = true) :
    Excluded rows budget chosen.toFinset decided := by
  intro s he hz hw
  exact Exclusion.sound (.packing (List.range pairs.length))
    (Numeric.check_refines (derived_rep hr pairs) _ hn hs hm hc)
    he (derived_zero hz pairs) hw

end ArmillaryLean.Exclusion.XorPacking

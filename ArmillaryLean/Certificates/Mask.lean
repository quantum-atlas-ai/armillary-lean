module

public import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Finite masks in 512-bit words

Eight words suffice for the 3636 physical columns. The correctness results use
bit membership and hold for any words, including untrusted input.
-/

namespace ArmillaryLean.Exclusion

/-- A mask indexed by a chunk number. -/
abbrev Mask := Fin 8 → Nat

namespace Mask

/-- The 512-bit word containing an address. -/
def word (i : Fin 4096) : Fin 8 := ⟨i.val / 512, by have := i.isLt; omega⟩

/-- Membership of an address in a mask. -/
def has (m : Mask) (i : Fin 4096) : Bool := (m (word i)).testBit (i.val % 512)

/-- The mask with no represented columns. -/
def empty : Mask := fun _ => 0

/-- Set one address bit inside its own chunk. -/
def put (m : Mask) (i : Fin 4096) : Mask :=
  fun k => if k = word i then m k ||| (1 <<< (i.val % 512)) else m k

/-- Intersect two masks word by word. -/
def inter (a b : Mask) : Mask := fun k => a k &&& b k

/-- Check that all set bits of the first mask are covered by the second. -/
def covered (a b : Mask) : Bool := (List.finRange 8).all fun k => (a k &&& b k) == a k

/-- A single set bit tests true exactly at its offset. -/
private theorem single_bit (i j : Nat) : (1 <<< i).testBit j = decide (i = j) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : i = j
  · subst j
    simp
  · cases hb : (decide (i ≤ j) && Nat.testBit 1 (j - i)) with
    | false => exact (decide_eq_false h).symm
    | true =>
      obtain ⟨hle, hbit⟩ := Bool.and_eq_true_iff.mp hb
      have hi := of_decide_eq_true hle
      have hj := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hbit
      omega

/-- Setting one bit adds exactly that address to the represented set. -/
theorem has_put (m : Mask) (i j : Fin 4096) :
    (put m i).has j = (m.has j || decide (i = j)) := by
  unfold has put
  by_cases h : word j = word i
  · have hiff : i.val % 512 = j.val % 512 ↔ i = j := by
      constructor
      · intro hrem
        have hquot := congrArg Fin.val h
        change j.val / 512 = i.val / 512 at hquot
        apply Fin.ext
        omega
      · rintro rfl
        rfl
    simp only [ite_eq_left h, Nat.testBit_or, single_bit, hiff]
  · have hn : i ≠ j := fun he => h (congrArg word he.symm)
    simp only [ite_eq_right h, decide_eq_false hn, Bool.or_false]

/-- Intersection agrees with conjunction of bit membership. -/
theorem has_inter (a b : Mask) (i : Fin 4096) :
    (inter a b).has i = (a.has i && b.has i) := Nat.testBit_and ..

/-- A successful coverage check implies containment at each address. -/
theorem covered_has {a b : Mask} (h : covered a b = true) {i : Fin 4096}
    (ha : a.has i = true) : b.has i = true := by
  have hk := List.all_eq_true.mp h (word i) (List.mem_finRange _)
  have hv : (a (word i) &&& b (word i)) = a (word i) := by simpa using hk
  have hbit := congrArg (fun n : Nat => n.testBit (i.val % 512)) hv
  rw [Nat.testBit_and] at hbit
  change (a.has i && b.has i) = a.has i at hbit
  simpa only [ha, Bool.true_and] using hbit

/-- Store the bits of the addresses in a list. -/
def ofList (indices : List (Fin 4096)) : Mask := indices.foldr (fun i m => m.put i) empty

/-- A list-generated mask contains precisely the listed addresses. -/
theorem has_ofList (indices : List (Fin 4096)) (i : Fin 4096) :
    (ofList indices).has i = true ↔ i ∈ indices := by
  induction indices with
  | nil => simp [ofList, has, empty]
  | cons j rest ih =>
    change ((ofList rest).put j).has i = true ↔ i ∈ j :: rest
    simp only [has_put, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun he => Or.inl he.symm),
      fun h => h.elim (fun he => Or.inr he.symm) Or.inl⟩

end Mask
end ArmillaryLean.Exclusion

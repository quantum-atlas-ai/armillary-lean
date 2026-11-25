module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Packed right inverses certify full rank over `ZMod 2`

Qatlib's verified Boolean elimination decides small ranks, but its register
model is too slow for a `907 x 907` minor. A sparse matrix admits a cheaper
certificate: one packed word per row of a right inverse. XOR-ing the words over
the support of each sparse row must give the unit vector of that row. The
argument below turns such a check into full rank, and the caller replays the
XORs with natural-number bit operations inside the kernel.
-/

namespace ArmillaryLean.Certificates.PackedRank

open scoped Matrix

/-- The binary matrix whose row `k` lists the set bits of the word `words k`. -/
def matrixOfWords {n : ℕ} (words : Fin n → Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun k j => if (words k).testBit j.val then 1 else 0

/-- The exclusive or of the words along a list of indices. -/
def xorWords {n : ℕ} (words : Fin n → Nat) (l : List (Fin n)) : Nat :=
  l.foldr (fun k acc => words k ^^^ acc) 0

/-- A leading index contributes its word to the exclusive or. -/
theorem xorWords_cons {n : ℕ} (words : Fin n → Nat) (a : Fin n) (l : List (Fin n)) :
    xorWords words (a :: l) = words a ^^^ xorWords words l :=
  rfl

/-- Summing bit rows over the set of a list of indices XORs the packed words. -/
theorem sum_matrixOfWords {n : ℕ} (words : Fin n → Nat) (j : Fin n) :
    ∀ {l : List (Fin n)}, l.Nodup →
    (∑ k ∈ l.toFinset, matrixOfWords words k j) =
      (if (xorWords words l).testBit j.val then 1 else 0) := by
  intro l hnodup
  induction hnodup with
  | nil => simp [matrixOfWords, xorWords]
  | @cons a l ha hnodup ih =>
      have ha' : a ∉ l := fun hmem => ha a hmem rfl
      rw [xorWords_cons, List.toFinset_cons,
        Finset.sum_insert (List.mem_toFinset.not.mpr ha'), ih, Nat.testBit_xor]
      simp only [matrixOfWords, Matrix.of_apply]
      cases (words a).testBit j.val <;> cases (xorWords words l).testBit j.val <;> decide

/-- A binary matrix is the indicator of a row support. -/
def IsSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (support : Fin n → Finset (Fin n)) :
    Prop :=
  ∀ i k, M i k = if k ∈ support i then 1 else 0

/-- A sparse binary matrix whose rows XOR the packed words to unit vectors has
full rank: the packed words form a right inverse. -/
theorem rank_eq_of_packed_inverse {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (support : Fin n → List (Fin n)) (hnodup : ∀ i, (support i).Nodup)
    (hsupport : IsSupport M (fun i => (support i).toFinset))
    (words : Fin n → Nat)
    (hxor : ∀ i, xorWords words (support i) = 2 ^ i.val) :
    M.rank = n := by
  have hmul : M * matrixOfWords words = 1 := by
    ext i j
    have hrow : (∑ k ∈ Finset.univ, M i k * matrixOfWords words k j) =
        ∑ k ∈ (support i).toFinset, matrixOfWords words k j := by
      have hzero : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ∉ (support i).toFinset →
          M i k * matrixOfWords words k j = 0 := by
        intro k _ hk
        rw [hsupport i k]
        simp [hk]
      rw [← Finset.sum_subset (Finset.subset_univ (support i).toFinset) hzero]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hsupport i k]
      simp [hk]
    rw [Matrix.mul_apply, hrow, sum_matrixOfWords _ _ (hnodup i), hxor i, Nat.testBit_two_pow,
      Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have hv : ¬ (i.val = j.val) := Fin.val_injective.ne hij
      simp [hv, hij]
  have hsurj : Function.Surjective M.mulVec :=
    fun w => ⟨matrixOfWords words *ᵥ w, by rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]⟩
  have hr : M.rank = Fintype.card (Fin n) := Matrix.mulVec_surjective_iff_rank_eq_card.mp hsurj
  rwa [Fintype.card_fin] at hr

end ArmillaryLean.Certificates.PackedRank

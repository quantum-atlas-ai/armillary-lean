module

public import Qatlib.Papers.Armillary26.Instances.Routed

@[expose] public section

/-!
# Concrete routed check matrices

For each retained pair of groups, equality of relative routes at station zero
certifies equality of the full routes. This reduces CSS compatibility to
finite checks on block pairings and the source channel tables.
-/

namespace ArmillaryLean.Routed

open Qatlib.Concepts.CodeCert.PermBlocks (matColWt pairCancel permBlocks permBlocks_cwt)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff armEff_eq_intAct)
open Qatlib.Papers.Armillary26.Pairing (Kchi chi intAct intAct_apply intAct_symm pairK static_zero)
open scoped Matrix

variable {p q : ℕ} [NeZero p]

/-- The station and channel coordinates of a routed cell. -/
abbrev Cell (p q : ℕ) := ZMod p × Fin q

/-- A physical data coordinate on the twelve routed blocks. -/
abbrev Coord (p q : ℕ) := Fin 12 × Cell p q

/-- A check coordinate for one of the three retained groups. -/
abbrev Check (p q : ℕ) := Fin 3 × Cell p q

/-- Interpret a finite channel table with a checked inverse. -/
def channelPerm (f inv : Vector (Fin q) q)
    (h : ∀ i, inv.get (f.get i) = i ∧ f.get (inv.get i) = i) : Equiv.Perm (Fin q) where
  toFun := f.get
  invFun := inv.get
  left_inv i := (h i).1
  right_inv i := (h i).2

/-- Build the binary check matrix for the retained groups from the source routes. -/
def checks (a : ArmParam p q) (groups : Fin 3 → Fin 12) :
    Matrix (Check p q) (Coord p q) (ZMod 2) :=
  permBlocks fun r => armEff a (groups r)

/-- Every row reads exactly one coordinate in each data block. -/
theorem check_read (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (r : Check p q) (v : Coord p q → ZMod 2) :
    (checks a groups *ᵥ v) r = ∑ b : Fin 12, v (b, armEff a (groups r.1) b r.2) := by
  change (∑ c : Coord p q, checks a groups r c * v c) = _
  rw [Fintype.sum_prod_type]
  simp [checks, permBlocks, ite_mul]

/-- Every data coordinate lies in one row per retained group. -/
theorem column_weight (a : ArmParam p q) (groups : Fin 3 → Fin 12) (v : Coord p q) :
    matColWt (checks a groups) v = 3 := by
  simpa [checks] using
    (permBlocks_cwt (K := ZMod 2) (fun r => armEff a (groups r)) v.1 v.2)

omit [NeZero p] in
/-- A data route translates its output station by the input station shift. -/
theorem visit_translate (a : ArmParam p q) (g b : Fin 12) (s t : ZMod p) (j : Fin q) :
    armEff a g b (s + t, j) =
      ((armEff a g b (s, j)).1 + t, (armEff a g b (s, j)).2) := by
  simp [armEff_eq_intAct, intAct, add_right_comm]

/-- Follow an X route and then the inverse Z route within a block. -/
def relative (a : ArmParam p q) (x z b : Fin 12) (u : Cell p q) : Cell p q :=
  (armEff a z b).symm (armEff a x b u)

omit [NeZero p] in
/-- A relative route is determined by its values at station zero. -/
theorem relative_at (a : ArmParam p q) (x z b : Fin 12) (s : ZMod p) (j : Fin q) :
    relative a x z b (s, j) =
      (s + (relative a x z b (0, j)).1, (relative a x z b (0, j)).2) := by
  simp [relative, armEff_eq_intAct, intAct_apply, intAct_symm, sub_eq_add_neg, add_assoc]

/-- Finite source checks certify the involution, cancellation and ordering of the pairing. -/
theorem paired (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (pair : Fin 3 → Fin 3 → Fin 12 → Fin 12)
    (inv : ∀ i j, Function.Involutive (pair i j))
    (fixed : ∀ i j b, pair i j b ≠ b)
    (stationZero : ∀ i j b k,
      relative a (x i) (z j) (pair i j b) (0, k) = relative a (x i) (z j) b (0, k))
    (order : ∀ i j b, chi (x i) (z j) (pair i j b) = chi (x i) (z j) b) :
    Kchi x z (fun i => armEff a (x i)) (fun j => armEff a (z j)) pair := by
  refine ⟨inv, fixed, ?_, order⟩
  intro i j b
  unfold pairK
  apply (pairCancel _ _ _ _).2
  apply Equiv.ext
  rintro ⟨s, k⟩
  change relative a (x i) (z j) (pair i j b) (s, k) = relative a (x i) (z j) b (s, k)
  rw [relative_at, relative_at a (x i) (z j) b, stationZero]

/-- Assemble a CSS code on the physical coordinates certified by a routed pairing. -/
def code (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (pair : Fin 3 → Fin 3 → Fin 12 → Fin 12)
    (h : Kchi x z (fun i => armEff a (x i)) (fun j => armEff a (z j)) pair) :
    CssData (Coord p q) (Check p q) (Check p q) where
  hX := checks a x
  hZ := checks a z
  hcompat := static_zero x z _ _ pair h

end ArmillaryLean.Routed

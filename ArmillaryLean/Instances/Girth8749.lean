module

public import ArmillaryLean.Instances.Anchor8749
public import ArmillaryLean.Instances.Css8749
public import Qatlib.Concepts.CodeCert.DistCert.Tanner

@[expose] public section

/-!
# Exact Tanner girth of Armillary 8749

Every retained check visits one data coordinate per block. Two distinct checks
of one sector close a Tanner four-cycle exactly when two distinct blocks carry
the same relative route value. A relative route shifts the station by a
constant, so the channel at station zero decides every station. Qatlib's
generic girth theorem turns the resulting rectangle exclusion and one explicit
closed walk of length six into extended girth six on both sides.
-/

namespace ArmillaryLean.Code8749

open Qatlib.Concepts.CodeCert.DistCert (NoRect tanner girth_six)
open Qatlib.Concepts.CodeCert.PermBlocks (permBlocks)
open Qatlib.Papers.Armillary26.Instances (armEff armEff_eq_intAct)
open Qatlib.Papers.Armillary26.Pairing (intAct intAct_apply intAct_symm)
open scoped Matrix

private theorem entry_ne_zero {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : α → β → Equiv.Perm ι) (a : α) (p : ι) (b : β) (q : ι) :
    permBlocks (K := ZMod 2) σ (a, p) (b, q) ≠ 0 ↔ σ a b p = q := by
  simp only [permBlocks]
  by_cases hc : σ a b p = q
  · simp [hc]
  · simp [hc]

/-- A permutation-block matrix over `ZMod 2` has no rectangle exactly when two
distinct row groups never route one internal cell to the same pair of
distinct blocks. -/
theorem permBlocks_noRect {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : α → β → Equiv.Perm ι) :
    NoRect (permBlocks (K := ZMod 2) σ) ↔
      ∀ (a a' : α), a ≠ a' → ∀ (b b' : β), b ≠ b' → ∀ p p' : ι,
        ¬ (σ a b p = σ a' b p' ∧ σ a b' p = σ a' b' p') := by
  constructor
  · intro hrect a a' haa b b' hbb p p' hboth
    obtain ⟨hone, htwo⟩ := hboth
    refine hrect (a, p) (a', p') (b, σ a b p) (b', σ a b' p) ?_ ?_ ⟨?_, ?_, ?_, ?_⟩
    · exact fun h => haa (congrArg Prod.fst h)
    · exact fun h => hbb (congrArg Prod.fst h)
    · exact (entry_ne_zero σ a p b _).mpr rfl
    · exact (entry_ne_zero σ a p b' _).mpr rfl
    · exact (entry_ne_zero σ a' p' b _).mpr hone.symm
    · exact (entry_ne_zero σ a' p' b' _).mpr htwo.symm
  · intro h r s i j hrs hij hboth
    obtain ⟨hone, htwo, hthree, hfour⟩ := hboth
    obtain ⟨a, p⟩ := r
    obtain ⟨a', p'⟩ := s
    obtain ⟨b, q⟩ := i
    obtain ⟨b', q'⟩ := j
    have e1 : σ a b p = q := (entry_ne_zero σ a p b q).mp hone
    have e2 : σ a b' p = q' := (entry_ne_zero σ a p b' q').mp htwo
    have e3 : σ a' b p' = q := (entry_ne_zero σ a' p' b q).mp hthree
    have e4 : σ a' b' p' = q' := (entry_ne_zero σ a' p' b' q').mp hfour
    have haa : a ≠ a' := by
      intro e
      subst e
      exact hrs (Prod.ext rfl ((σ a b).injective (e1.trans e3.symm)))
    have hbb : b ≠ b' := by
      intro e
      subst e
      exact hij (Prod.ext rfl (e1.symm.trans e2))
    exact h a a' haa b b' hbb p p' ⟨e1.trans e3.symm, e2.trans e4.symm⟩

/-- The relative route from one group to another inside one block. -/
private def relativeRoute (g g' b : Fin 12) (u : Cell) : Cell :=
  (armEff params g' b).symm (armEff params g b u)

/-- The station of a relative route shifts with the input station. -/
private theorem relativeRoute_at (g g' b : Fin 12) (s : ZMod 101) (j : Fin 3) :
    relativeRoute g g' b (s, j) =
      (s + (relativeRoute g g' b (0, j)).1, (relativeRoute g g' b (0, j)).2) := by
  simp [relativeRoute, armEff_eq_intAct, intAct_apply, intAct_symm, sub_eq_add_neg, add_assoc]

/-- In either sector, two distinct retained groups route every channel to
different cells in two distinct blocks. -/
private theorem relative_disjoint : ∀ (sector : Fin 2) (x z : Fin 3), x ≠ z →
    ∀ (b b' : Fin 12), b ≠ b' → ∀ j : Fin 3,
      relativeRoute (retained sector x) (retained sector z) b (0, j) ≠
        relativeRoute (retained sector x) (retained sector z) b' (0, j) := by
  decide +kernel

/-- Neither retained sector of the 8749 instance contains a Tanner four-cycle. -/
private theorem sector_noRect (sector : Fin 2) : NoRect (checks (retained sector)) := by
  rw [checks, permBlocks_noRect]
  intro a a' hne b b' hbd u u' hboth
  obtain ⟨s, j⟩ := u
  have h1 : relativeRoute (retained sector a) (retained sector a') b (s, j) = u' := by
    rw [relativeRoute, hboth.1, Equiv.symm_apply_apply]
  have h2 : relativeRoute (retained sector a) (retained sector a') b' (s, j) = u' := by
    rw [relativeRoute, hboth.2, Equiv.symm_apply_apply]
  have hrw1 := relativeRoute_at (retained sector a) (retained sector a') b s j
  have hrw2 := relativeRoute_at (retained sector a) (retained sector a') b' s j
  rw [h1] at hrw1
  rw [h2] at hrw2
  have hp : relativeRoute (retained sector a) (retained sector a') b (0, j) =
      relativeRoute (retained sector a) (retained sector a') b' (0, j) := by
    have heq := hrw1.symm.trans hrw2
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg (fun w : Cell => w.2) heq
    exact Prod.ext (add_left_cancel h1) h2
  exact relative_disjoint sector a a' hne b b' hbd j hp

/-- The X-check matrix has no Tanner four-cycle. -/
theorem x_noRect : NoRect xChecks :=
  sector_noRect 0

/-- The Z-check matrix has no Tanner four-cycle. -/
theorem z_noRect : NoRect zChecks :=
  sector_noRect 1

/-- An incidence is an edge from a check to a data coordinate. -/
private theorem tanner_inl_inr (A : Matrix Check Coord (ZMod 2)) (r : Check) (i : Coord) :
    (tanner A).Adj (Sum.inl r) (Sum.inr i) ↔ A r i ≠ 0 :=
  Iff.rfl

/-- An incidence is an edge from a data coordinate to a check. -/
private theorem tanner_inr_inl (A : Matrix Check Coord (ZMod 2)) (r : Check) (i : Coord) :
    (tanner A).Adj (Sum.inr i) (Sum.inl r) ↔ A r i ≠ 0 :=
  Iff.rfl

/-- The closed walk `r 0 → c 0 → r 1 → c 1 → r 2 → c 2 → r 0` of a Tanner graph. -/
private def sixWalk (A : Matrix Check Coord (ZMod 2)) (r : Fin 3 → Check) (c : Fin 3 → Coord)
    (e₀ : ∀ k, A (r k) (c k) ≠ 0) (e₁ : ∀ k, A (r (k + 1)) (c k) ≠ 0) :
    (tanner A).Walk (Sum.inl (r 0)) (Sum.inl (r 0)) :=
  .cons ((tanner_inl_inr A _ _).mpr (e₀ 0))
  (.cons ((tanner_inr_inl A _ _).mpr (e₁ 0))
  (.cons ((tanner_inl_inr A _ _).mpr (e₀ 1))
  (.cons ((tanner_inr_inl A _ _).mpr (e₁ 1))
  (.cons ((tanner_inl_inr A _ _).mpr (e₀ 2))
  (.cons ((tanner_inr_inl A _ _).mpr (e₁ 2)) .nil)))))

/-- The three X checks of the explicit six-cycle, as `(group, (station, channel))`. -/
private def xCycleChecks : Vector Check 3 :=
  #v[(1, ((0 : ZMod 101), (0 : Fin 3))), (0, ((89 : ZMod 101), (2 : Fin 3))),
     (2, ((92 : ZMod 101), (0 : Fin 3)))]

/-- The three data coordinates of the explicit X six-cycle. -/
private def xCycleCols : Vector Coord 3 :=
  #v[(0, ((0 : ZMod 101), (0 : Fin 3))), (9, ((94 : ZMod 101), (1 : Fin 3))),
     (6, ((3 : ZMod 101), (1 : Fin 3)))]

/-- The three Z checks of the explicit six-cycle, as `(group, (station, channel))`. -/
private def zCycleChecks : Vector Check 3 :=
  #v[(2, ((0 : ZMod 101), (0 : Fin 3))), (0, ((91 : ZMod 101), (1 : Fin 3))),
     (1, ((2 : ZMod 101), (2 : Fin 3)))]

/-- The three data coordinates of the explicit Z six-cycle. -/
private def zCycleCols : Vector Coord 3 :=
  #v[(0, ((1 : ZMod 101), (0 : Fin 3))), (4, ((5 : ZMod 101), (0 : Fin 3))),
     (9, ((11 : ZMod 101), (1 : Fin 3)))]

/-- Each X cycle check visits its data coordinate. -/
private theorem xCycle_first : ∀ k : Fin 3,
    xChecks (xCycleChecks.get k) (xCycleCols.get k) = 1 := by
  decide +kernel

/-- Each X cycle coordinate is visited by the next X cycle check. -/
private theorem xCycle_second : ∀ k : Fin 3,
    xChecks (xCycleChecks.get (k + 1)) (xCycleCols.get k) = 1 := by
  decide +kernel

/-- Each Z cycle check visits its data coordinate. -/
private theorem zCycle_first : ∀ k : Fin 3,
    zChecks (zCycleChecks.get k) (zCycleCols.get k) = 1 := by
  decide +kernel

/-- Each Z cycle coordinate is visited by the next Z cycle check. -/
private theorem zCycle_second : ∀ k : Fin 3,
    zChecks (zCycleChecks.get (k + 1)) (zCycleCols.get k) = 1 := by
  decide +kernel

/-- The explicit six-cycle of the X Tanner graph. -/
private def xCycle : (tanner xChecks).Walk (Sum.inl (xCycleChecks.get 0))
    (Sum.inl (xCycleChecks.get 0)) :=
  sixWalk xChecks xCycleChecks.get xCycleCols.get
    (fun k => by rw [xCycle_first k]; exact one_ne_zero)
    (fun k => by rw [xCycle_second k]; exact one_ne_zero)

/-- The explicit six-cycle of the Z Tanner graph. -/
private def zCycle : (tanner zChecks).Walk (Sum.inl (zCycleChecks.get 0))
    (Sum.inl (zCycleChecks.get 0)) :=
  sixWalk zChecks zCycleChecks.get zCycleCols.get
    (fun k => by rw [zCycle_first k]; exact one_ne_zero)
    (fun k => by rw [zCycle_second k]; exact one_ne_zero)

/-- The X witness is a cycle: its six edges and six interior vertices differ. -/
private theorem xCycle_isCycle : xCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨⟨by decide⟩, by decide, by decide⟩

/-- The Z witness is a cycle: its six edges and six interior vertices differ. -/
private theorem zCycle_isCycle : zCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨⟨by decide⟩, by decide, by decide⟩

/-- The Tanner graph of the X-check matrix has extended girth exactly six. -/
theorem x_girth : (tanner xChecks).egirth = 6 :=
  girth_six xChecks x_noRect xCycle_isCycle rfl

/-- The Tanner graph of the Z-check matrix has extended girth exactly six. -/
theorem z_girth : (tanner zChecks).egirth = 6 :=
  girth_six zChecks z_noRect zCycle_isCycle rfl

end ArmillaryLean.Code8749

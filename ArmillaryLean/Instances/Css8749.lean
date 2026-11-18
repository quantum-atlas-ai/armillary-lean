module

public import ArmillaryLean.Instances.Code8749

@[expose] public section

/-!
# CSS compatibility of Armillary instance 8749

For each retained X/Z group pair, the block pairing is checked against the
actual routed relative permutations. Station-zero checks suffice because
every relative permutation commutes with station translation.
-/

namespace ArmillaryLean.Code8749

open Qatlib.Concepts.CodeCert.PermBlocks (pairCancel)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData)
open Qatlib.Papers.Armillary26.Instances (armEff armEff_eq_intAct)
open Qatlib.Papers.Armillary26.Pairing (Kchi chi intAct_apply intAct_symm pairK static_zero)
open scoped Matrix

/-- Pair equal relative permutations within each retained X/Z group pair. -/
def blockPair (x z : Fin 3) (b : Fin 12) : Fin 12 :=
  let p46 := #v[7, 11, 8, 6, 5, 4, 3, 0, 2, 10, 9, 1]
  let p42 := #v[5, 4, 3, 2, 1, 0, 10, 9, 11, 7, 6, 8]
  let p02 := #v[1, 0, 10, 11, 8, 9, 7, 6, 4, 5, 2, 3]
  let p82 := #v[8, 9, 7, 4, 3, 6, 5, 2, 0, 1, 11, 10]
  let p810 := #v[3, 6, 5, 0, 10, 2, 1, 11, 9, 8, 4, 7]
  (((#v[#v[p46, p42, p02], #v[p42, p02, p82], #v[p02, p82, p810]] :
    Vector (Vector (Vector (Fin 12) 12) 3) 3).get x).get z).get b

/-- Follow an X route and then the inverse Z route within one block. -/
def relative (x z : Fin 3) (b : Fin 12) (u : Cell) : Cell :=
  (armEff params (zGroups.get z) b).symm (armEff params (xGroups.get x) b u)

/-- A relative route is determined by its values at station zero. -/
theorem relative_at (x z : Fin 3) (b : Fin 12) (s : ZMod 101) (j : Fin 3) :
    relative x z b (s, j) =
      (s + (relative x z b (0, j)).1, (relative x z b (0, j)).2) := by
  simp [relative, armEff_eq_intAct, intAct_apply, intAct_symm, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 0 in
/-- The block pairing preserves all three station-zero entries of the relative route. -/
private theorem relative_zero : ∀ (x z : Fin 3) (b : Fin 12) (j : Fin 3),
    relative x z (blockPair x z b) (0, j) = relative x z b (0, j) := by
  decide +kernel

/-- The concrete block pairing cancels the static product and preserves visit order. -/
theorem paired : Kchi xGroups.get zGroups.get
    (fun x => armEff params (xGroups.get x)) (fun z => armEff params (zGroups.get z))
    blockPair := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · change ∀ (x z : Fin 3) (b : Fin 12), blockPair x z (blockPair x z b) = b
    decide
  · intro x z b
    unfold pairK
    apply (pairCancel _ _ _ _).2
    apply Equiv.ext
    rintro ⟨s, j⟩
    change relative x z (blockPair x z b) (s, j) = relative x z b (s, j)
    rw [relative_at x z (blockPair x z b) s j, relative_at x z b s j, relative_zero]

/-- The two Table S2 matrices satisfy CSS orthogonality. -/
theorem compatible : xChecks * zChecksᵀ = 0 :=
  static_zero xGroups.get zGroups.get
    (fun x => armEff params (xGroups.get x)) (fun z => armEff params (zGroups.get z))
    blockPair paired

/-- The CSS code whose check matrices are the concrete Table S2 routed matrices. -/
def code : CssData Coord Check Check where
  hX := xChecks
  hZ := zChecks
  hcompat := compatible

end ArmillaryLean.Code8749

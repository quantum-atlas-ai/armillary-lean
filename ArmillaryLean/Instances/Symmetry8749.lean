module

public import ArmillaryLean.Instances.Rows8749
import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Isomorphism of the two Armillary 8749 check graphs

The X-to-Z isomorphism reverses the station coordinate and permutes the
blocks, check groups and channels. A finite station-zero check against the
routed tables verifies the data, and affine dependence gives the diagram at
all stations.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion (OddRow ZeroSyndrome)
open ChannelPerm

/-- The block correspondence between the two check graphs. -/
def blockImage (b : Fin 12) : Fin 12 :=
  (#v[1, 0, 10, 11, 8, 9, 7, 6, 4, 5, 2, 3] : Vector (Fin 12) 12).get b

/-- The checked block correspondence is an involution. -/
theorem block_invol : ∀ b, blockImage (blockImage b) = b := by decide

/-- The block bijection of the X-to-Z graph isomorphism. -/
def blockIso : Fin 12 ≃ Fin 12 where
  toFun := blockImage
  invFun := blockImage
  left_inv := block_invol
  right_inv := block_invol

/-- The station offset for each source data block. -/
def blockShift (b : Fin 12) : ZMod 101 :=
  (#v[10, 10, 5, 3, 9, 10, 7, 7, 9, 10, 5, 3] : Vector (ZMod 101) 12).get b

/-- The channel permutation for each source data block. -/
def dataChannel (b : Fin 12) : Equiv.Perm (Fin 3) :=
  ((#v[p021, p021, p102, p120, p201, p201, p012, p012, p120, p120, p102, p201] :
    Vector ChannelPerm 12).get b).toEquiv

/-- The coordinate bijection from the X-check graph to the Z-check graph. -/
def coordIso : Coord ≃ Coord where
  toFun c := (blockIso c.1, (blockShift c.1 - c.2.1, dataChannel c.1 c.2.2))
  invFun c := let b := blockIso.symm c.1
              (b, (blockShift b - c.2.1, (dataChannel b).symm c.2.2))
  left_inv c := by simp
  right_inv c := by simp

/-- The check-group permutation reverses the three retained groups. -/
def checkGroup : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

/-- The station offset for a source check group. -/
def checkOffset (g : Fin 3) : ZMod 101 :=
  (#v[0, 99, 95] : Vector (ZMod 101) 3).get g

/-- The check-channel action in each source group. -/
def checkChannel (g : Fin 3) : Equiv.Perm (Fin 3) :=
  ((#v[p120, p012, p021] : Vector ChannelPerm 3).get g).toEquiv

/-- The row bijection from the X-check graph to the Z-check graph. -/
def rowIso : Check ≃ Check where
  toFun r := (checkGroup r.1, (checkOffset r.1 - r.2.1, checkChannel r.1 r.2.2))
  invFun r := let g := checkGroup.symm r.1
              (g, (checkOffset g - r.2.1, (checkChannel g).symm r.2.2))
  left_inv r := by simp
  right_inv r := by simp

set_option maxHeartbeats 0 in
/-- The routed graph-isomorphism diagram at every station-zero check coordinate. -/
private theorem iso_zero : ∀ (g : Fin 3) (j : Fin 3) (b : Fin 12),
    coordIso (fastVisit 0 (g, (0, j)) b) = fastVisit 1 (rowIso (g, (0, j))) (blockIso b) := by
  decide +kernel

/-- Mapping a routed X neighbour gives the corresponding routed Z neighbour. -/
theorem visit_iso (r : Check) (b : Fin 12) :
    coordIso (fastVisit 0 r b) = fastVisit 1 (rowIso r) (blockIso b) := by
  obtain ⟨g, i, j⟩ := r
  let x := routeZero 0 g b j
  let z := routeZero 1 (checkGroup g) (blockIso b) (checkChannel g j)
  have h := iso_zero g j b
  have hs := congrArg (fun c : Coord => c.2.1) h
  change blockShift b - (x.1 + 0) = z.1 + (checkOffset g - 0) at hs
  simp only [add_zero, sub_zero] at hs
  have hc := congrArg (fun c : Coord => c.2.2) h
  change dataChannel b x.2 = z.2 at hc
  have hs' : blockShift b - (x.1 + i) = z.1 + (checkOffset g - i) := by
    calc
      _ = (blockShift b - x.1) - i := by abel
      _ = (z.1 + checkOffset g) - i := by rw [hs]
      _ = _ := by abel
  change (blockIso b, (blockShift b - (x.1 + i), dataChannel b x.2)) =
    (blockIso b, (z.1 + (checkOffset g - i), z.2))
  rw [hs', hc]

/-- The graph isomorphism maps every X row neighbourhood onto its Z counterpart. -/
theorem neighbors_iso (r : Check) :
    neighbors (retained 1) (rowIso r) = (neighbors (retained 0) r).map coordIso.toEmbedding := by
  rw [← fastRows_eq 1, ← fastRows_eq 0]
  ext c
  simp only [fastRows, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨b, hb⟩
    let a := blockIso.symm b
    refine ⟨fastVisit 0 r a, ⟨a, rfl⟩, ?_⟩
    have h := visit_iso r a
    change coordIso (fastVisit 0 r a) = c
    rw [h, show blockIso a = b from Equiv.apply_symm_apply _ _]
    exact hb
  · rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨blockIso b, (visit_iso r b).symm.trans hb⟩

/-- Reindexing by the graph isomorphism preserves all syndrome equations. -/
theorem zero_iso (s : Finset Coord) : ZeroSyndrome (neighbors (retained 0)) s ↔
    ZeroSyndrome (neighbors (retained 1)) (s.map coordIso.toEmbedding) := by
  have hi (r : Check) : OddRow (neighbors (retained 1) (rowIso r))
      (s.map coordIso.toEmbedding) ↔ OddRow (neighbors (retained 0) r) s := by
    unfold OddRow
    rw [neighbors_iso]
    have hfilter : ((neighbors (retained 0) r).map coordIso.toEmbedding).filter
        (fun c => c ∈ s.map coordIso.toEmbedding) =
        ((neighbors (retained 0) r).filter fun c => c ∈ s).map coordIso.toEmbedding := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_map_equiv]
    rw [hfilter, Finset.card_map]
  constructor
  · intro h row
    obtain ⟨r, rfl⟩ := rowIso.surjective row
    exact fun ho => h r ((hi r).mp ho)
  · intro h r ho
    exact h (rowIso r) ((hi r).mpr ho)

/-- Pull back a Z zero-syndrome support to an X zero-syndrome support. -/
theorem zero_pullback (s : Finset Coord) (hz : ZeroSyndrome (neighbors (retained 1)) s) :
    ZeroSyndrome (neighbors (retained 0)) (s.map coordIso.symm.toEmbedding) := by
  apply (zero_iso _).mpr
  have hm : (s.map coordIso.symm.toEmbedding).map coordIso.toEmbedding = s := by
    ext c
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
  rwa [hm]

end ArmillaryLean.Code8749

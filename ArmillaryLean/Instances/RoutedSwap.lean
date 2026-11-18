module

public import ArmillaryLean.Instances.RoutedAnchors

@[expose] public section

/-!
# Transport of reduced certificates along a sector swap

A common column permutation must intertwine both row families. This preserves
both the opposite check syndrome and the overlaps with the stabilizer rows.
-/

namespace ArmillaryLean.Routed

open ArmillaryLean.Exclusion (OddRow ZeroSyndrome)
open ArmillaryLean.Stabilizer (support)
open Qatlib.Concepts.CodingDecoding.CssTesters (bitWeight)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)
open scoped Matrix

variable {p q : ℕ} [NeZero p]

/-- A common column equivalence interchanges the routed X and Z row families. -/
structure SectorSwap (a : ArmParam p q) (x z : Fin 3 → Fin 12) where
  dataMap : Coord p q ≃ Coord p q
  xToZ : Check p q ≃ Check p q
  zToX : Check p q ≃ Check p q
  mapX : ∀ r, neighbors a z (xToZ r) = (neighbors a x r).map dataMap.toEmbedding
  mapZ : ∀ r, neighbors a x (zToX r) = (neighbors a z r).map dataMap.toEmbedding

omit [NeZero p] in
/-- Pairwise neighborhood correspondence gives correspondence of the whole rows. -/
theorem neighbors_of_visits (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (e : Coord p q ≃ Coord p q) (f : Check p q ≃ Check p q) (bmap : Fin 12 ≃ Fin 12)
    (h : ∀ (r : Check p q) (b : Fin 12), e (b, armEff a (x r.1) b r.2) =
      (bmap b, armEff a (z (f r).1) (bmap b) (f r).2)) (r : Check p q) :
    neighbors a z (f r) = (neighbors a x r).map e.toEmbedding := by
  ext c
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := bmap.surjective b
    exact ⟨_, ⟨b, rfl⟩, (h r b).trans hb⟩
  · rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨bmap b, (h r b).symm.trans hb⟩

omit [NeZero p] in
/-- Mapping two supports by the same equivalence preserves their intersection weight. -/
private theorem count_map (e : Coord p q ≃ Coord p q) (s t : Finset (Coord p q)) :
    ((s.map e.toEmbedding).filter (fun c => c ∈ t.map e.toEmbedding)).card =
      (s.filter fun c => c ∈ t).card := by
  have he : (s.map e.toEmbedding).filter (fun c => c ∈ t.map e.toEmbedding) =
      (s.filter fun c => c ∈ t).map e.toEmbedding := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_map_equiv]
  rw [he, Finset.card_map]

/-- One family of checked reduced anchors suffices in the presence of a sector swap. -/
theorem distance_ge_of_swap (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (c : CssData (Coord p q) (Check p q) (Check p q))
    (hx : c.hX = checks a x) (hz : c.hZ = checks a z)
    (sym : SectorSwap a x z) (d : ℕ) (he : d % 2 = 0)
    (cert : ReducedAnchors a z x (d - 2)) : (d : ℕ∞) ≤ cssDistance c := by
  apply distance_ge_of_six a x z c hx hz d
  · intro v hv hw ho
    have hs := (zero_support_iff a z v).mpr hv
    let s := (support v).map sym.dataMap.symm.toEmbedding
    have hmap : s.map sym.dataMap.toEmbedding = support v := by
      ext i
      simp only [s, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
    have hwt : s.card < d := by
      rw [← Finset.card_map (f := sym.dataMap.toEmbedding), hmap]
      exact hw
    have hs' : ZeroSyndrome (neighbors a x) s := by
      intro r
      have hr := hs (sym.xToZ r)
      unfold OddRow at hr ⊢
      rw [sym.mapX r, ← hmap, count_map] at hr
      exact hr
    have ho' : ∀ r, (s ∩ neighbors a z r).card ≤ 6 := by
      intro r
      have hr := ho (sym.zToX r)
      rw [sym.mapZ r, ← hmap, ← Finset.filter_mem_eq_inter, count_map,
        Finset.filter_mem_eq_inter] at hr
      exact hr
    have empty := reduced_empty a z x d he cert s hs' hwt ho'
    have hv0 : support v = ∅ := by rw [← hmap, empty, Finset.map_empty]
    funext i
    have hm : i ∉ support v := by simp [hv0]
    simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Pi.zero_apply] using hm
  · intro v hv hw ho
    have empty := reduced_empty a z x d he cert (support v) ((zero_support_iff a x v).mpr hv) hw ho
    funext i
    have hm : i ∉ support v := by simp [empty]
    simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Pi.zero_apply] using hm

end ArmillaryLean.Routed

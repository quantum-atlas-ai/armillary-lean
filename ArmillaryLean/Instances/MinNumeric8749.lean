module

public import ArmillaryLean.Instances.Numeric8749

@[expose] public section

/-!
# Composable numeric checkpoints for minimum-rank anchors

A checkpoint may use a literal word for its marked addresses. A separate
equality ties that literal to the earlier-rank mask and to its branch path.
-/

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion

/-- The semantic marked addresses at a minimum-rank checkpoint. -/
def checkpointSet (b : Fin 12) (j : Fin 3) (path : List Nat) : Finset Nat :=
  path.toFinset ∪ earlierSet b j

/-- Form the numeric marked word from a verified earlier mask and the branch path. -/
def checkpointWord (b : Fin 12) (j : Fin 3) (path : List Nat) : Nat :=
  path.foldr (fun c word => Numeric.put word c) (earlierWord b j)

/-- The checkpoint word represents the branch's finite marked set. -/
theorem checkpointWords (b : Fin 12) (j : Fin 3) (path : List Nat) :
    Numeric.Represents (checkpointWord b j path) (checkpointSet b j path) := by
  induction path with
  | nil => simpa only [checkpointWord, List.foldr_nil, checkpointSet, List.toFinset_nil,
      Finset.empty_union] using earlier_rep b j
  | cons c rest ih =>
    simp only [checkpointWord, List.foldr_cons, checkpointSet, List.toFinset_cons, Finset.insert_union]
    exact Numeric.represents_put ih c

/-- A checked fragment yields a numeric exclusion at its checkpoint. -/
theorem checkedNumericPart {sector : Fin 2} {rowWord : Nat → Nat} (hrows : CorrectWords sector rowWord)
    {budget : Nat} {b : Fin 12} {j : Fin 3} {chosen path : List Nat} {marked : Nat} {program : Program}
    (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ path.toFinset)
    (hm : marked = checkpointWord b j path)
    (hc : Numeric.run rowWord 909 3636 budget chosen marked program = true) :
    Excluded (numericRows sector) budget chosen.toFinset (checkpointSet b j path) := by
  have hw (r : Nat) : Numeric.Represents (rowWord r) (numericRows sector r) := by
    rw [hrows r]
    exact referenceWord_rep sector r
  have hrep := hm ▸ checkpointWords b j path
  exact Numeric.run_excludes hw hn (hs.trans Finset.subset_union_left) hrep hc

/-- A combined numeric root exclusion proves the physical minimum-rank anchor obligation. -/
theorem min_from_root {sector : Fin 2} {budget : Nat} {b : Fin 12} {j : Fin 3}
    (hex : Excluded (numericRows sector) budget {colAddress (b, (0, j))}
      (checkpointSet b j [colAddress (b, (0, j))]))
    {s : Finset Coord} (ha : (b, (0, j)) ∈ s)
    (hmin : ∀ v ∈ s, anchorRank (b, (0, j)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained sector)) s) (hw : s.card ≤ budget) : False := by
  let a := colAddress (b, (0, j))
  apply hex _ (numericZero sector s hz) (by simpa only [Finset.card_map] using hw)
  refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_map_of_mem _ ha), ?_⟩
  intro c hsupport hm
  simp only [checkpointSet, List.toFinset_cons, List.toFinset_nil, Finset.insert_union,
    Finset.empty_union, Finset.mem_insert] at hm
  rcases hm with hEq | hprior
  · exact Finset.mem_singleton.mpr hEq
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hsupport
    have hlt := (Finset.mem_filter.mp hprior).2
    rw [addressRank_eq] at hlt
    exact ((not_lt_of_ge (hmin v hv)) hlt).elim

end ArmillaryLean.Code8749

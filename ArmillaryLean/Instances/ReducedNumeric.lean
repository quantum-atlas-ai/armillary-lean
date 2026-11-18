module

public import ArmillaryLean.Certificates.Reduced
public import ArmillaryLean.Instances.RoutedAnchors
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Physical indices for reduced Armillary certificates

Row and column addresses are ordered by group or block, station, then channel.
The word table represents the physical rows through the same address map as
the search coordinates. The initial marked set excludes earlier anchor ranks.
-/

namespace ArmillaryLean.Routed

open ArmillaryLean.Exclusion
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)

variable {p q k : ℕ} [NeZero p]

/-- The mixed-radix address equivalence in group, station, channel order. -/
def addressEquiv : (Fin k × Cell p q) ≃ Fin (k * (p * q)) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (ZMod.finEquiv p).symm (Equiv.refl _)).trans
    finProdFinEquiv)).trans finProdFinEquiv

/-- Encode a physical coordinate as an injective natural address. -/
def address : (Fin k × Cell p q) ↪ Nat where
  toFun x := (addressEquiv x).val
  inj' _ _ h := addressEquiv.injective (Fin.ext h)

/-- A physical address lies in the finite table range. -/
theorem address_lt (x : Fin k × Cell p q) : address x < k * (p * q) :=
  (addressEquiv x).isLt

/-- The numeric address spells out the finite mixed-radix address. -/
theorem address_eq (x : Fin k × Cell p q) :
    address x = x.2.2.val + q * x.2.1.val + (p * q) * x.1.val := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => rfl

/-- Rank forgets the station component of a numeric column address. -/
def numericRank (p q i : Nat) : Nat := q * (i / (p * q)) + i % q

/-- The numeric and physical anchor ranks coincide. -/
theorem numericRank_eq (a : ArmParam p q) (v : Coord p q) :
    numericRank p q (address v) = anchorRank v := by
  have hpq := Nat.mul_pos a.hp a.hq
  have hc := (finProdFinEquiv (⟨v.2.1.val, v.2.1.val_lt⟩, v.2.2)).isLt
  change v.2.2.val + q * v.2.1.val < p * q at hc
  rw [numericRank, address_eq, Nat.add_mul_div_left _ _ hpq, Nat.div_eq_of_lt hc, Nat.zero_add,
    show (p * q) * v.1.val = q * (p * v.1.val) by ac_rfl, Nat.add_mul_mod_self_left,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt v.2.2.isLt]
  rfl

/-- The numeric row is the image of the physical row, or empty out of bounds. -/
def certRows (a : ArmParam p q) (groups : Fin 3 → Fin 12) (r : Nat) : Finset Nat :=
  if h : r < 3 * (p * q) then (neighbors a groups (addressEquiv.symm ⟨r, h⟩)).map address
  else ∅

/-- A table word computed from the physical row's twelve routed entries. -/
def certWord (a : ArmParam p q) (groups : Fin 3 → Fin 12) (r : Nat) : Nat :=
  if h : r < 3 * (p * q) then
    let row : Check p q := addressEquiv.symm ⟨r, h⟩
    Numeric.ofList ((List.finRange 12).map (fun b => address (b, armEff a (groups row.1) b row.2)))
  else 0

/-- A direct table word has exactly the bits of the corresponding numeric row. -/
theorem certWord_rep (a : ArmParam p q) (groups : Fin 3 → Fin 12) (r : Nat) :
    Numeric.Represents (certWord a groups r) (certRows a groups r) := by
  by_cases h : r < 3 * (p * q)
  · simp only [certRows, certWord, dite_eq_left h]
    let row : Check p q := addressEquiv.symm ⟨r, h⟩
    have he : ((List.finRange 12).map
        (fun b => address (b, armEff a (groups row.1) b row.2))).toFinset =
        (neighbors a groups row).map address := by
      ext c
      simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and, neighbors,
        Finset.mem_map, Finset.mem_image, Finset.mem_univ]
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨_, ⟨b, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨b, rfl⟩, h⟩
        exact ⟨b, h⟩
    rw [← he]
    exact Numeric.ofList_represents _
  · simpa only [certRows, certWord, dite_eq_right h] using Numeric.represents_zero

/-- A common injective address map preserves a filtered neighborhood cardinality. -/
private theorem mapped_filter (s t : Finset (Coord p q)) :
    ((s.map address).filter fun c => c ∈ t.map address).card =
      (s.filter fun c => c ∈ t).card := by
  have he : ((s.map address).filter fun c => c ∈ t.map address) =
      (s.filter fun c => c ∈ t).map address := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, ⟨w, hw, he⟩⟩
      exact ⟨v, ⟨hv, address.injective he ▸ hw⟩, rfl⟩
    · rintro ⟨v, ⟨hv, ht⟩, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, ⟨v, ht, rfl⟩⟩
  rw [he, Finset.card_map]

/-- Physical zero syndrome gives numeric zero syndrome. -/
theorem cert_zero (a : ArmParam p q) (groups : Fin 3 → Fin 12) (s : Finset (Coord p q))
    (hz : ZeroSyndrome (neighbors a groups) s) :
    ZeroSyndrome (certRows a groups) (s.map address) := by
  intro r
  by_cases h : r < 3 * (p * q)
  · unfold OddRow
    rw [certRows, dite_eq_left h, mapped_filter]
    exact hz _
  · simp [certRows, h, OddRow]

/-- Physical row-overlap bounds give the numeric overlap bounds. -/
theorem cert_overlap (a : ArmParam p q) (groups : Fin 3 → Fin 12) (s : Finset (Coord p q))
    (ho : ∀ r, (s ∩ neighbors a groups r).card ≤ 6) :
    Reduced.OverlapSix (certRows a groups) (s.map address) := by
  intro r
  by_cases h : r < 3 * (p * q)
  · rw [certRows, dite_eq_left h, ← Finset.filter_mem_eq_inter, mapped_filter,
      Finset.filter_mem_eq_inter]
    exact ho _
  · simp [certRows, h]

/-- The earlier numeric ranks must be forbidden when a minimum-rank anchor is selected. -/
def priorList (p q : Nat) (b : Fin 12) (j : Fin q) : List Nat :=
  (List.range (12 * (p * q))).filter (fun i => numericRank p q i < q * b.val + j.val)

/-- The initial canonical mask is constructed independently of any proof program. -/
def priorWord (p q : Nat) (b : Fin 12) (j : Fin q) : Nat :=
  Numeric.ofList (priorList p q b j)

/-- A checkpoint carries the initial canonical mask and all previous split columns. -/
def branchWord (base : Nat) (path : List Nat) : Nat :=
  path.foldr (fun i w => Numeric.put w i) base

/-- The checkpoint word represents the finite marked set. -/
theorem branchWord_rep {base : Nat} {prior : Finset Nat}
    (hb : Numeric.Represents base prior) (path : List Nat) :
    Numeric.Represents (branchWord base path) (path.toFinset ∪ prior) := by
  induction path with
  | nil => simpa [branchWord] using hb
  | cons c cs ih =>
    simpa only [branchWord, List.foldr_cons, List.toFinset_cons, Finset.insert_union] using
      Numeric.represents_put ih c

/-- A checked fragment yields the reduced exclusion at the stated numeric checkpoint. -/
theorem reduced_part {p q : Nat} [NeZero p] {a : ArmParam p q}
    {opposite stabilizers : Fin 3 → Fin 12} {ow sw : Nat → Nat}
    (hOpp : ∀ r, Numeric.Represents (ow r) (certRows a opposite r))
    (hStab : ∀ r, Numeric.Represents (sw r) (certRows a stabilizers r))
    {b : Fin 12} {j : Fin q} {base budget : Nat} {chosen path : List Nat} {marked : Nat}
    {program : Program}
    (hb : base = priorWord p q b j) (hn : chosen.Nodup) (hs : chosen.toFinset ⊆ path.toFinset)
    (hm : marked = branchWord base path)
    (hc : Reduced.run ow sw (3 * (p * q)) (12 * (p * q)) budget chosen marked program = true) :
    Reduced.Excludes (certRows a opposite) (certRows a stabilizers) budget
      chosen.toFinset (path.toFinset ∪ (priorList p q b j).toFinset) := by
  exact Reduced.run_excludes hOpp hStab hn (hs.trans Finset.subset_union_left)
    (hm ▸ branchWord_rep (hb ▸ Numeric.ofList_represents (priorList p q b j)) path) hc

/-- The numeric root exclusion rules out its physical reduced anchor. -/
theorem reduced_root (a : ArmParam p q) (opposite stabilizers : Fin 3 → Fin 12)
    (b : Fin 12) (j : Fin q) (budget : Nat)
    (hex : Reduced.Excludes (certRows a opposite) (certRows a stabilizers) budget
      {address (b, ((0 : ZMod p), j))}
      ({address (b, ((0 : ZMod p), j))} ∪ (priorList p q b j).toFinset))
    (s : Finset (Coord p q)) (ha : (b, (0, j)) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (p := p) (b, (0, j)) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors a opposite) s) (hw : s.card ≤ budget)
    (ho : ∀ r, (s ∩ neighbors a stabilizers r).card ≤ 6) : False := by
  apply hex _ (cert_zero a opposite s hz) ((Finset.card_map _).trans_le hw)
    (cert_overlap a stabilizers s ho)
  refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_map_of_mem _ ha), ?_⟩
  intro c hsup hd
  rcases Finset.mem_union.mp hd with hd | hd
  · exact hd
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hsup
    simp only [priorList, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hd
    rw [numericRank_eq a v] at hd
    exact ((not_lt_of_ge (hm v hv)) hd.2).elim

end ArmillaryLean.Routed

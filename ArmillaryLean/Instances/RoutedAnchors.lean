module

public import ArmillaryLean.Certificates.Exclusion
public import ArmillaryLean.Instances.RoutedLower

@[expose] public section

/-!
# Anchored lower certificates for routed Armillary codes

Station translation preserves both the parity of the opposite checks and
the overlaps with the stabilizer rows. An even target distance reduces
the support budget by two. The resulting obligations are stated on the
actual neighborhoods of both routed check matrices.
-/

namespace ArmillaryLean.Routed

open ArmillaryLean.Exclusion (OddRow ZeroSyndrome)
open ArmillaryLean.Stabilizer (support)
open Qatlib.Concepts.CodingDecoding.CssTesters (bitWeight)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Concepts.CodeCert.PermBlocks (block_col_sum)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)
open scoped Matrix

variable {p q : ℕ} [NeZero p]

/-- The indicator of a routed data support. -/
private def bits (s : Finset (Coord p q)) (v : Coord p q) : ZMod 2 :=
  if v ∈ s then 1 else 0

/-- The binary indicator recovers a vector from its nonzero support. -/
private theorem bits_support (v : Coord p q → ZMod 2) : bits (support v) = v := by
  funext i
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hb (v i) with h | h <;> simp [bits, support, h]

/-- The support of the binary indicator is the original finite set. -/
private theorem support_bits (s : Finset (Coord p q)) : support (bits s) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [support, bits, hi]

omit [NeZero p] in
/-- Summing a binary indicator counts the intersection modulo two. -/
private theorem sum_bits (s t : Finset (Coord p q)) :
    ∑ v ∈ s, bits t v = ((s.filter fun v => v ∈ t).card : ZMod 2) := by
  simp only [bits, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Each routed matrix row reads the parity of its neighborhood. -/
private theorem row_parity (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (r : Check p q) (s : Finset (Coord p q)) :
    (checks a groups *ᵥ bits s) r =
      (((neighbors a groups r).filter fun c => c ∈ s).card : ZMod 2) := by
  rw [check_read]
  have hinj : Function.Injective (fun b => (b, armEff a (groups r.1) b r.2)) :=
    fun _ _ h => congrArg Prod.fst h
  rw [← Finset.sum_image hinj.injOn, sum_bits]
  rfl

/-- A support indicator has zero syndrome exactly when all row intersections are even. -/
private theorem zero_bits_iff (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (s : Finset (Coord p q)) :
    ZeroSyndrome (neighbors a groups) s ↔ checks a groups *ᵥ bits s = 0 := by
  simp only [ZeroSyndrome, OddRow, funext_iff, Pi.zero_apply, row_parity,
    ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  constructor <;> intro h r <;> have hr := h r <;> omega

/-- The matrix syndrome agrees with the parities of the routed neighborhoods. -/
theorem zero_support_iff (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (v : Coord p q → ZMod 2) : ZeroSyndrome (neighbors a groups) (support v) ↔
      checks a groups *ᵥ v = 0 := by
  rw [zero_bits_iff, bits_support]

/-- A zero-syndrome vector has even weight because each column has odd weight. -/
theorem weight_even (a : ArmParam p q) (groups : Fin 3 → Fin 12) (v : Coord p q → ZMod 2)
    (hz : checks a groups *ᵥ v = 0) : bitWeight v % 2 = 0 := by
  have col_sum (c : Coord p q) : (∑ r : Check p q, checks a groups r c) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [checks, block_col_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    decide
  have htotal : (∑ r : Check p q, (checks a groups *ᵥ v) r) = (bitWeight v : ZMod 2) := by
    change (∑ r : Check p q, ∑ c : Coord p q, checks a groups r c * v c) = _
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, col_sum, one_mul]
    conv_lhs => rw [← bits_support v]
    simpa [bitWeight, support] using sum_bits (Finset.univ : Finset (Coord p q)) (support v)
  have hzero : (bitWeight v : ZMod 2) = 0 := by simpa [hz] using htotal.symm
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hzero)

/-- Translate the station of a data or check coordinate while fixing its other indices. -/
private def translate {k : ℕ} (t : ZMod p) : (Fin k × Cell p q) ≃ (Fin k × Cell p q) :=
  Equiv.prodCongr (Equiv.refl _) {
    toFun u := (u.1 + t, u.2)
    invFun u := (u.1 - t, u.2)
    left_inv u := by simp
    right_inv u := by simp
  }

omit [NeZero p] in
/-- A translated check visits precisely the translated data neighbors. -/
private theorem neighbors_shift (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (r : Check p q) (t : ZMod p) :
    neighbors a groups (translate t r) = (neighbors a groups r).map (translate t).toEmbedding := by
  ext v
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map]
  have at_block (b : Fin 12) :
      (b, armEff a (groups (translate t r).1) b (translate t r).2) =
        translate t (b, armEff a (groups r.1) b r.2) :=
    congrArg (fun u => (b, u)) (visit_translate a (groups r.1) b r.2.1 t r.2.2)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨_, ⟨b, rfl⟩, (at_block b).symm.trans hb⟩
  · rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨b, (at_block b).trans hb⟩

omit [NeZero p] in
/-- A common translation on two supports preserves their intersection count. -/
private theorem shifted_inter (s u : Finset (Coord p q)) (t : ZMod p) :
    ((s.map (translate t).toEmbedding).filter
        (fun c => c ∈ u.map (translate t).toEmbedding)).card =
      (s.filter fun c => c ∈ u).card := by
  have he : (s.map (translate t).toEmbedding).filter
      (fun c => c ∈ u.map (translate t).toEmbedding) =
      (s.filter fun c => c ∈ u).map (translate t).toEmbedding := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_map_equiv]
  rw [he, Finset.card_map]

/-- The rank of a candidate anchor depends only on its block and channel. -/
def anchorRank (v : Coord p q) : ℕ := q * v.1.val + v.2.2.val

/-- A reduced anchored support obligation for one check sector. -/
def ReducedAnchors (a : ArmParam p q) (stabilizers opposite : Fin 3 → Fin 12)
    (budget : ℕ) : Prop :=
  ∀ (b : Fin 12) (j : Fin q) (s : Finset (Coord p q)),
    (b, (0, j)) ∈ s → (∀ v ∈ s, anchorRank (p := p) (b, (0, j)) ≤ anchorRank v) →
    ZeroSyndrome (neighbors a opposite) s → s.card ≤ budget →
    (∀ r, (s ∩ neighbors a stabilizers r).card ≤ 6) → False

/-- Anchor exclusions imply vanishing of all sufficiently small reduced kernel vectors. -/
private theorem reduced_zero (a : ArmParam p q) (stabilizers opposite : Fin 3 → Fin 12)
    (d : ℕ) (even : d % 2 = 0) (cert : ReducedAnchors a stabilizers opposite (d - 2))
    (v : Coord p q → ZMod 2) (hz : checks a opposite *ᵥ v = 0) (hw : bitWeight v < d)
    (ho : ∀ r, ((support v) ∩ neighbors a stabilizers r).card ≤ 6) : v = 0 := by
  by_contra hne
  have hnon : (support v).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    apply hne
    rw [← bits_support v, he]
    funext i
    simp [bits]
  obtain ⟨⟨b, i, j⟩, ha, hmin⟩ := Finset.exists_min_image (support v) anchorRank hnon
  let t := -i
  let s := (support v).map (translate t).toEmbedding
  apply cert b j s
  · have hm := Finset.mem_map_of_mem (translate t).toEmbedding ha
    simpa [s, translate, t] using hm
  · intro u hu
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hu
    exact hmin c hc
  · intro r
    obtain ⟨r, rfl⟩ := (translate t).surjective r
    unfold OddRow
    rw [neighbors_shift]
    rw [shifted_inter]
    exact (zero_support_iff a opposite v).mpr hz r
  · have hEven := weight_even a opposite v hz
    change s.card ≤ d - 2
    rw [show s.card = bitWeight v from Finset.card_map _]
    omega
  · intro r
    obtain ⟨r, rfl⟩ := (translate t).surjective r
    rw [neighbors_shift, ← Finset.filter_mem_eq_inter]
    change ((support v).map (translate t).toEmbedding |>.filter
      (fun c => c ∈ (neighbors a stabilizers r).map (translate t).toEmbedding)).card ≤ 6
    rw [shifted_inter, Finset.filter_mem_eq_inter]
    exact ho r

/-- The two anchored reduced certificate families give the even CSS distance lower bound. -/
theorem distance_ge_of_anchors (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (c : CssData (Coord p q) (Check p q) (Check p q))
    (hx : c.hX = checks a x) (hz : c.hZ = checks a z)
    (d : ℕ) (even : d % 2 = 0) (xCert : ReducedAnchors a x z (d - 2))
    (zCert : ReducedAnchors a z x (d - 2)) : (d : ℕ∞) ≤ cssDistance c :=
  distance_ge_of_six a x z c hx hz d
    (reduced_zero a x z d even xCert) (reduced_zero a z x d even zCert)

/-- Reduced-anchor exclusions force small reduced support sets to be empty. -/
theorem reduced_empty (a : ArmParam p q) (stabilizers opposite : Fin 3 → Fin 12)
    (d : ℕ) (even : d % 2 = 0) (cert : ReducedAnchors a stabilizers opposite (d - 2))
    (s : Finset (Coord p q)) (hz : ZeroSyndrome (neighbors a opposite) s) (hw : s.card < d)
    (ho : ∀ r, (s ∩ neighbors a stabilizers r).card ≤ 6) : s = ∅ := by
  have h := reduced_zero a stabilizers opposite d even cert (bits s)
    ((zero_bits_iff a opposite s).mp hz)
    (by simpa only [show bitWeight (bits s) = (support (bits s)).card from rfl, support_bits] using hw)
    (by simpa only [support_bits] using ho)
  rw [← support_bits s, h]
  ext i
  simp [support]

end ArmillaryLean.Routed

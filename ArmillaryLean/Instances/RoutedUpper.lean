module

public import ArmillaryLean.Instances.Routed
public import Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance

@[expose] public section

/-!
# A logical upper witness on the routed data coordinates

Each witness entry contributes to exactly one opposite-sector check per
retained group. A fixed-point-free pairing cancels these contributions.
A two-block indicator separates the witness from the stabilizer row space.
-/

namespace ArmillaryLean.Routed

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (CssData cssDistance)
open Qatlib.Concepts.ErrorCorrection.LogicalOps (distance_le)
open Qatlib.Papers.Armillary26.Instances (ArmParam armEff)
open Qatlib.Papers.Armillary26.Pairing (sum_inv_zero)
open scoped Matrix

variable {p q w : ℕ} [NeZero p]

/-- The opposite-sector cell reached from a witness coordinate by reversing its route. -/
def incoming (a : ArmParam p q) (g : Fin 12) (v : Coord p q) : Cell p q :=
  (armEff a g v.1).symm v.2

/-- The binary indicator of an enumerated witness support. -/
def witnessBits (u : Fin w → Coord p q) (v : Coord p q) : ZMod 2 :=
  if v ∈ Finset.univ.image u then 1 else 0

/-- The witness dot product is the sum over its distinct coordinates. -/
private theorem witness_dot (u : Fin w → Coord p q) (hu : Function.Injective u)
    (v : Coord p q → ZMod 2) : dotProduct v (witnessBits u) = ∑ i, v (u i) := by
  have hs : Finset.univ.filter (fun c => c ∈ Finset.univ.image u) = Finset.univ.image u := by
    ext c
    simp
  simp only [dotProduct, witnessBits, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [hs, Finset.sum_image hu.injOn]

omit [NeZero p] in
/-- A routed matrix entry indicates whether the coordinate comes from the row's cell. -/
private theorem witness_entry (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (r : Check p q) (v : Coord p q) :
    checks a groups r v = if r.2 = incoming a (groups r.1) v then 1 else 0 := by
  let perm := armEff a (groups r.1) v.1
  change (if perm r.2 = v.2 then (1 : ZMod 2) else 0) = _
  have h : perm r.2 = v.2 ↔ r.2 = incoming a (groups r.1) v := perm.eq_symm_apply.symm
  by_cases hr : r.2 = incoming a (groups r.1) v
  · rw [ite_eq_left (h.mpr hr), ite_eq_left hr]
  · rw [ite_eq_right (fun hp => hr (h.mp hp)), ite_eq_right hr]

/-- Pairing witnesses that trace to the same incoming row gives zero syndrome. -/
theorem witness_zero (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (u : Fin w → Coord p q) (hu : Function.Injective u)
    (pair : Fin 3 → Fin w → Fin w) (inv : ∀ z, Function.Involutive (pair z))
    (fixed : ∀ z i, pair z i ≠ i)
    (same : ∀ z i, incoming a (groups z) (u (pair z i)) = incoming a (groups z) (u i)) :
    checks a groups *ᵥ witnessBits u = 0 := by
  funext r
  change dotProduct (checks a groups r) (witnessBits u) = 0
  rw [witness_dot u hu]
  refine sum_inv_zero _ (pair r.1) (inv r.1) (fixed r.1) ?_
  intro i
  simp only [witness_entry, same]

/-- The indicator of two distinct data blocks. -/
def separator (b₀ b₁ : Fin 12) (v : Coord p q) : ZMod 2 :=
  if v.1 = b₀ ∨ v.1 = b₁ then 1 else 0

/-- The rowwise sum of the two-block indicator is zero in the binary field. -/
private theorem separator_zero (a : ArmParam p q) (groups : Fin 3 → Fin 12)
    (b₀ b₁ : Fin 12)
    (even : (∑ b : Fin 12, if b = b₀ ∨ b = b₁ then (1 : ZMod 2) else 0) = 0) :
    checks a groups *ᵥ separator b₀ b₁ = 0 := by
  funext r
  rw [check_read]
  exact even

/-- An injectively enumerated support gives the indicated pure Pauli weight. -/
private theorem witness_weight (u : Fin w → Coord p q) (hu : Function.Injective u) :
    pauliWeight (witnessBits u) 0 = w := by
  unfold pauliWeight
  have h : Finset.univ.filter (fun v => witnessBits u v ≠ 0 ∨ (0 : Coord p q → ZMod 2) v ≠ 0) =
      Finset.univ.image u := by
    ext v
    by_cases hv : v ∈ Finset.univ.image u <;> simp [witnessBits, hv]
  rw [h, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]

/-- A paired pure X witness separated by a two-block indicator bounds CSS distance. -/
theorem distance_le_of_witness (a : ArmParam p q) (x z : Fin 3 → Fin 12)
    (c : CssData (Coord p q) (Check p q) (Check p q))
    (hx : c.hX = checks a x) (hz : c.hZ = checks a z)
    (u : Fin w → Coord p q) (hu : Function.Injective u)
    (zero : checks a z *ᵥ witnessBits u = 0)
    (b₀ b₁ : Fin 12)
    (even : (∑ b : Fin 12, if b = b₀ ∨ b = b₁ then (1 : ZMod 2) else 0) = 0)
    (odd : (∑ i, separator b₀ b₁ (u i)) = 1) :
    cssDistance c ≤ (w : ℕ∞) := by
  let e : PauliLabel (Coord p q) := (witnessBits u, 0)
  have hs : pauliSyndrome c e = (0, 0) := by
    change (c.hX *ᵥ 0, c.hZ *ᵥ witnessBits u) = (0, 0)
    rw [hz, Matrix.mulVec_zero, zero]
  have hdot : dotProduct (separator b₀ b₁) (witnessBits u) = 1 :=
    (witness_dot u hu _).trans odd
  have hn : ¬ IsStabilizerLabel c e := by
    intro hs
    obtain ⟨coeffs, hc⟩ := hs.1
    change c.hXᵀ *ᵥ coeffs = witnessBits u at hc
    have hz : dotProduct (separator b₀ b₁) (witnessBits u) = 0 := by
      rw [← hc, hx, Matrix.dotProduct_transpose_mulVec, separator_zero a x b₀ b₁ even,
        dotProduct_zero]
    exact zero_ne_one (hz.symm.trans hdot)
  simpa only [e, witness_weight u hu] using distance_le c e hs hn

end ArmillaryLean.Routed

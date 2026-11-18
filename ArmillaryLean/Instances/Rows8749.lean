module

public import ArmillaryLean.Instances.Lower8749

@[expose] public section

/-!
# Computable sparse rows for the Armillary 8749 checks

The six tables store the routed destinations at station zero. The kernel
checks each entry against the source route. Translation then supplies every
other row without recomputing the route inside a certificate.
-/

namespace ArmillaryLean.Code8749

/-- The retained group indices for the X-check and Z-check matrices, respectively. -/
def retained (sector : Fin 2) : Fin 3 → Fin 12 :=
  if sector = 0 then xGroups.get else zGroups.get

/-- The Table S2 routing table at station zero, indexed by sector, group, block and channel. -/
def routeTable : Vector (Vector (Vector (Vector Cell 3) 12) 3) 2 :=
  #v[#v[#v[#v[(12, 2), (12, 1), (12, 0)], #v[(9, 1), (9, 2), (9, 0)], #v[(5, 0), (5, 2), (5, 1)],
        #v[(4, 1), (4, 0), (4, 2)], #v[(0, 1), (0, 0), (0, 2)], #v[(100, 1), (100, 0), (100, 2)],
        #v[(98, 0), (98, 1), (98, 2)], #v[(2, 2), (2, 1), (2, 0)], #v[(1, 2), (1, 0), (1, 1)],
        #v[(5, 0), (5, 2), (5, 1)], #v[(6, 0), (6, 2), (6, 1)], #v[(3, 2), (3, 1), (3, 0)]],
      #v[#v[(0, 0), (0, 2), (0, 1)], #v[(1, 2), (1, 1), (1, 0)], #v[(1, 2), (1, 0), (1, 1)],
        #v[(1, 0), (1, 2), (1, 1)], #v[(9, 1), (9, 2), (9, 0)], #v[(3, 0), (3, 1), (3, 2)],
        #v[(3, 1), (3, 2), (3, 0)], #v[(12, 1), (12, 2), (12, 0)], #v[(8, 1), (8, 0), (8, 2)],
        #v[(14, 2), (14, 0), (14, 1)], #v[(7, 2), (7, 1), (7, 0)], #v[(6, 1), (6, 2), (6, 0)]],
      #v[#v[(9, 2), (9, 1), (9, 0)], #v[(5, 2), (5, 1), (5, 0)], #v[(7, 2), (7, 1), (7, 0)],
        #v[(8, 1), (8, 0), (8, 2)], #v[(12, 1), (12, 2), (12, 0)], #v[(13, 0), (13, 1), (13, 2)],
        #v[(12, 1), (12, 2), (12, 0)], #v[(13, 1), (13, 0), (13, 2)], #v[(0, 1), (0, 0), (0, 2)],
        #v[(2, 1), (2, 0), (2, 2)], #v[(4, 2), (4, 0), (4, 1)], #v[(2, 1), (2, 2), (2, 0)]]],
    #v[#v[#v[(11, 1), (11, 0), (11, 2)], #v[(7, 1), (7, 0), (7, 2)], #v[(7, 2), (7, 0), (7, 1)],
        #v[(7, 0), (7, 2), (7, 1)], #v[(15, 2), (15, 0), (15, 1)], #v[(14, 2), (14, 0), (14, 1)],
        #v[(0, 1), (0, 2), (0, 0)], #v[(1, 1), (1, 0), (1, 2)], #v[(3, 0), (3, 2), (3, 1)],
        #v[(3, 2), (3, 1), (3, 0)], #v[(4, 2), (4, 1), (4, 0)], #v[(1, 2), (1, 0), (1, 1)]],
      #v[#v[(11, 1), (11, 2), (11, 0)], #v[(12, 0), (12, 1), (12, 2)], #v[(0, 2), (0, 0), (0, 1)],
        #v[(100, 0), (100, 1), (100, 2)], #v[(3, 2), (3, 1), (3, 0)], #v[(99, 0), (99, 1), (99, 2)],
        #v[(98, 1), (98, 2), (98, 0)], #v[(6, 1), (6, 2), (6, 0)], #v[(2, 0), (2, 1), (2, 2)],
        #v[(9, 2), (9, 0), (9, 1)], #v[(6, 2), (6, 1), (6, 0)], #v[(4, 1), (4, 0), (4, 2)]],
      #v[#v[(1, 0), (1, 2), (1, 1)], #v[(99, 0), (99, 1), (99, 2)], #v[(100, 0), (100, 1), (100, 2)],
        #v[(0, 2), (0, 1), (0, 0)], #v[(8, 2), (8, 0), (8, 1)], #v[(5, 2), (5, 1), (5, 0)],
        #v[(5, 0), (5, 2), (5, 1)], #v[(10, 2), (10, 0), (10, 1)], #v[(9, 1), (9, 0), (9, 2)],
        #v[(11, 1), (11, 0), (11, 2)], #v[(0, 0), (0, 1), (0, 2)], #v[(100, 0), (100, 2), (100, 1)]]]]

/-- Read the station-zero entry of the sparse routing table. -/
def routeZero (sector : Fin 2) (r : Fin 3) (b : Fin 12) (j : Fin 3) : Cell :=
  (((routeTable.get sector).get r).get b).get j

set_option maxHeartbeats 0 in
/-- Every entry of the sparse routing table agrees with the actual station-zero visit. -/
theorem routeZero_eq : ∀ (sector : Fin 2) (r : Fin 3) (b : Fin 12) (j : Fin 3),
    (visit (retained sector r) (0, j) b).2 = routeZero sector r b j := by
  decide +kernel

/-- A row's physical neighbour in a specified block, computed by a table lookup. -/
def fastVisit (sector : Fin 2) (r : Check) (b : Fin 12) : Coord :=
  let u := routeZero sector r.1 b r.2.2
  (b, (u.1 + r.2.1, u.2))

/-- The table lookup agrees with the source route at every station. -/
theorem fastVisit_eq (sector : Fin 2) (r : Check) (b : Fin 12) :
    fastVisit sector r b = visit (retained sector r.1) r.2 b := by
  obtain ⟨g, i, j⟩ := r
  unfold fastVisit
  rw [← routeZero_eq]
  simpa using (visit_translate (retained sector g) b (0, j) i).symm

/-- Efficiently enumerate a row's twelve neighbours for use in a certificate checker. -/
def fastRows (sector : Fin 2) (r : Check) : Finset Coord :=
  Finset.univ.image (fastVisit sector r)

/-- The checker row neighbourhoods agree with the reference neighbourhoods. -/
theorem fastRows_eq (sector : Fin 2) : fastRows sector = neighbors (retained sector) := by
  funext r
  unfold fastRows neighbors
  congr 1
  funext b
  exact fastVisit_eq sector r b

end ArmillaryLean.Code8749

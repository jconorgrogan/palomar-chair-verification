module

public import ProductClosure.RegisteredTubeOwners
public import ProductClosure.ProductWorldRealization
public import ProductClosure.ProductWorldRelative
public import ProductClosure.ProductGraphCarrierDisjoint

@[expose] public section

/-! Actual adjacent occupied cells force an exposed full native site contact
and physical carrier nonoverlap in the exact relative pose chart. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}

/-- Distinct actual tile states have physically disjoint relative carriers;
this is derived from occupied-cell disjointness and Euclidean realization. -/
theorem relative_carrierDisjoint_of_tiles
    (W : World.CompleteTiling (World.placedCells S))
    (q r : RegisteredPrime.Pose (m + 1)) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hne : q ≠ r) : ProductGraphCarrierDisjoint.CarrierDisjoint S (poseIsometry (q.relative r)) := by
  let N := W.reframe q
  have hroot : RegisteredPrime.identityPose (m + 1) ∈ N.tiles := by
    change q.comp (RegisteredPrime.identityPose (m + 1)) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_identity] using hq
  have ht : q.relative r ∈ N.tiles := by
    change q.comp (q.relative r) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_relative] using hr
  have hrt : RegisteredPrime.identityPose (m + 1) ≠ q.relative r := by
    intro he
    exact hne ((World.relative_identity_iff q r).mp he.symm)
  have hd := N.realize.disjoint _ hroot _ ht hrt
  have hid : World.placedCarrier S (RegisteredPrime.identityPose (m + 1)) = Polycube.carrier S := by
    unfold World.placedCarrier
    rw [poseIsometry_identity]
    change id '' Polycube.carrier S = Polycube.carrier S
    exact Set.image_id _
  rw [hid] at hd
  exact hd

/-- A literal face-adjacent occupied pair in distinct tiles supplies an exact
full-frame native SiteTransport witness. Both the exposed root facet and
its companion are recovered from cell geometry, not postulated. -/
theorem neighbor_pair_siteTransport
    (W : World.CompleteTiling (World.placedCells S))
    (q r : RegisteredPrime.Pose (m + 1)) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hne : q ≠ r) {x y : LatticeIndex m}
    (hx : x ∈ World.placedCells S q) (hy : y ∈ World.placedCells S r)
    (hxy : World.LatticeAdjacent x y) :
    ∃ u v : Site S, SiteTransport (poseIsometry (q.relative r)) u v := by
  let N := W.reframe q
  have hroot : RegisteredPrime.identityPose (m + 1) ∈ N.tiles := by
    change q.comp (RegisteredPrime.identityPose (m + 1)) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_identity] using hq
  have ht : q.relative r ∈ N.tiles := by
    change q.comp (q.relative r) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_relative] using hr
  have hrt : RegisteredPrime.identityPose (m + 1) ≠ q.relative r := by
    intro he
    exact hne ((World.relative_identity_iff q r).mp he.symm)
  have hd : Disjoint (S : Set (LatticeIndex m)) (World.placedCells S (q.relative r)) := by
    simpa only [placedCells_identity] using N.disjoint _ hroot _ ht hrt
  have hx' : q.inv.cell x ∈ World.placedCells S (RegisteredPrime.identityPose (m + 1)) := by
    apply (World.placedCells_comp_cell_iff S q (RegisteredPrime.identityPose (m + 1)) _).mp
    simpa only [World.poseCellIndex_eq_cell, RegisteredPrime.Pose.cell_inv_cell,
      RegisteredPrime.Pose.comp_identity] using hx
  rw [placedCells_identity] at hx'
  have hy' : q.inv.cell y ∈ World.placedCells S (q.relative r) := by
    apply (World.placedCells_comp_cell_iff S q (q.relative r) _).mp
    simpa only [World.poseCellIndex_eq_cell, RegisteredPrime.Pose.cell_inv_cell,
      RegisteredPrime.Pose.comp_relative] using hy
  let A : Polycube.Cell S := ⟨q.inv.cell x, hx'⟩
  have hadj : RegisteredPrime.Adjacent (cellIndex A) (q.inv.cell y) := by
    exact q.inv.adjacent_cells x y ((World.latticeAdjacent_iff_registered x y).mp hxy)
  have hout : ¬ ∃ B : Polycube.Cell S, cellIndex B = q.inv.cell y := by
    rintro ⟨B, he⟩
    exact Set.disjoint_left.mp hd (he ▸ B.property) hy'
  obtain ⟨f, _, hfo⟩ := native_cell_exposed_neighbor A (q.inv.cell y) hadj hout
  let u : Site S := (f, (Equiv.refl (Fin m), fun _ => true))
  have houtside : facetOutsideIndex u.1 ∈ World.placedCells S (q.relative r) := by
    change facetOutsideIndex f ∈ _
    rwa [hfo]
  obtain ⟨v, hv⟩ := site_mate_of_outside_owner (q.relative r) u hd houtside
  exact ⟨u, v, hv⟩

/-- The main owner-neighbor interface consumed by actual product closure. -/
theorem neighbor_owners_dense_contact
    (W : World.CompleteTiling (World.placedCells S)) {x y : LatticeIndex m}
    (hxy : World.LatticeAdjacent x y) (hne : W.owner x ≠ W.owner y) :
    (∃ u v : Site S, SiteTransport (poseIsometry ((W.owner x).relative (W.owner y))) u v) ∧
      ProductGraphCarrierDisjoint.CarrierDisjoint S
        (poseIsometry ((W.owner x).relative (W.owner y))) :=
  ⟨neighbor_pair_siteTransport W _ _ (W.owner_mem x) (W.owner_mem y) hne
      (W.mem_owner x) (W.mem_owner y) hxy,
    relative_carrierDisjoint_of_tiles W _ _ (W.owner_mem x) (W.owner_mem y) hne⟩

#print axioms neighbor_pair_siteTransport
#print axioms relative_carrierDisjoint_of_tiles
#print axioms neighbor_owners_dense_contact
end
end ProductClosure.NativeCompiler

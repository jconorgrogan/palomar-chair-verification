module

public import PhysicalRegistration.RegisteredCarrierWorld
public import PrimeFacetClosure.NativeContactFacet
public import PhysicalRegistration.MaterialCovariance
public import PrimeFacetClosure.NativePrescribedOrbit
public import PrimeFacetClosure.GeneratedWorldProfiles
public import PhysicalRegistration.CompiledRegisteredWorld
public import PhysicalRegistration.NativeMaterialGluing

@[expose] public section

/-! Actual registered cell owners isolate every native tube to the two
carrier cells adjacent to its exposed facet. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

@[simp] theorem facetInsideCell_tangent_index {m : ℕ} (f : Facet m) (i : Fin (m+1))
    (hi : i ≠ normalIndex f) : cellIndex (facetInsideCell f) i = facetCellCoordinate f i := by
  cases f with
  | inl a => rfl
  | inr j => simp [facetInsideCell, cellIndex, facetCellCoordinate, normalIndex] at hi ⊢; exact hi

@[simp] theorem facetInsideCell_normal_index {m : ℕ} (f : Facet m) :
    cellIndex (facetInsideCell f) (normalIndex f) =
      facetPlane f - if facetPositive f then 1 else 0 := by
  cases f with
  | inl a => cases h : a.1.val a.2 <;> simp [facetInsideCell, cellIndex, normalIndex, facetPlane, facetPositive, h]
  | inr j => simp [facetInsideCell, cellIndex, normalIndex, facetPlane, facetPositive]

@[simp] theorem facetOutsideIndex_normal {m : ℕ} (f : Facet m) :
    facetOutsideIndex f (normalIndex f) =
      facetPlane f - if facetPositive f then 0 else 1 := by
  simp only [facetOutsideIndex, latticeStep, facetInsideCell_normal_index]
  cases facetPositive f <;> simp <;> omega

@[simp] theorem facetOutsideIndex_tangent {m : ℕ} (f : Facet m) (i : Fin (m+1))
    (hi : i ≠ normalIndex f) : facetOutsideIndex f i = facetCellCoordinate f i := by
  simp [facetOutsideIndex, latticeStep, hi, facetInsideCell_tangent_index f i hi]

/-- A native tube meets only the two literal lattice cells adjacent to its
facet. Strict transverse margins include all closed-tube boundary points. -/
theorem closedTube_latticeCell_cases {m J : ℕ} (u : Site m) {x : Space m}
    (hx : x ∈ closedTube J u) (z : LatticeIndex m) (hz : x ∈ latticeCell z) :
    z = cellIndex (facetInsideCell u.1) ∨ z = facetOutsideIndex u.1 := by
  have hn := closedTube_subset_facetNeighborhood u hx
  have ht : ∀ i, i ≠ normalIndex u.1 → z i = facetCellCoordinate u.1 i := by
    intro i hi
    have hxcoord := abs_lt.mp (hn i)
    rw [facetCenter_tangent u.1 i hi] at hxcoord
    have hzcoord := hz i
    have h₁ : (z i : ℝ) < ((facetCellCoordinate u.1 i + 1 : ℤ) : ℝ) := by
      push_cast; linarith [hxcoord.2, hzcoord.1]
    have h₂ : (facetCellCoordinate u.1 i : ℝ) < ((z i + 1 : ℤ) : ℝ) := by
      push_cast; linarith [hxcoord.1, hzcoord.2]
    have h₁' := Int.cast_lt.mp h₁
    have h₂' := Int.cast_lt.mp h₂
    omega
  have hj : z (normalIndex u.1) = facetPlane u.1 - 1 ∨
      z (normalIndex u.1) = facetPlane u.1 := by
    have hxcoord := abs_lt.mp (hn (normalIndex u.1))
    rw [facetCenter_normal] at hxcoord
    have hzcoord := hz (normalIndex u.1)
    have h₁ : (z (normalIndex u.1) : ℝ) < ((facetPlane u.1 + 1 : ℤ) : ℝ) := by
      push_cast; linarith [hxcoord.2, hzcoord.1]
    have h₂ : ((facetPlane u.1 - 2 : ℤ) : ℝ) < (z (normalIndex u.1) : ℝ) := by
      push_cast; linarith [hxcoord.1, hzcoord.2]
    have h₁' := Int.cast_lt.mp h₁
    have h₂' := Int.cast_lt.mp h₂
    omega
  have hin : z (normalIndex u.1) = cellIndex (facetInsideCell u.1) (normalIndex u.1) ∨
      z (normalIndex u.1) = facetOutsideIndex u.1 (normalIndex u.1) := by
    rw [facetInsideCell_normal_index, facetOutsideIndex_normal]
    cases facetPositive u.1 <;> simp_all [or_comm]
  rcases hin with hin | hout
  · left
    funext i
    by_cases hi : i = normalIndex u.1
    · simpa only [hi] using hin
    · rw [ht i hi, facetInsideCell_tangent_index u.1 i hi]
  · right
    funext i
    by_cases hi : i = normalIndex u.1
    · simpa only [hi] using hout
    · rw [ht i hi, facetOutsideIndex_tangent u.1 i hi]

/-- Any carrier meeting a root-native tube owns one of its two adjacent
registered cells. This is genuine cell ownership, not a local cover premise. -/
theorem carrier_meets_native_tube_owner {m J : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (u : Site m)
    (hx : (closedTube J u ∩ (poseIsometry q '' carrier m)).Nonempty) :
    RegisteredPrime.Occupies q (cellIndex (facetInsideCell u.1)) ∨
      RegisteredPrime.Occupies q (facetOutsideIndex u.1) := by
  obtain ⟨x, hxT, hxC⟩ := hx
  obtain ⟨z, hqz, hxz⟩ := (mem_posed_carrier_iff q x).mp hxC
  rcases closedTube_latticeCell_cases u hxT z hxz with rfl | rfl
  · exact Or.inl hqz
  · exact Or.inr hqz

/-- The other side of a native exposed facet is never part of the same chair. -/
theorem facetOutsideIndex_not_unitChairCell {m : ℕ} (f : Facet m) :
    ¬ RegisteredPrime.UnitChairCell (facetOutsideIndex f) := by
  intro h
  cases f with
  | inl a =>
      have hj := h.1 a.2
      rw [facetOutsideIndex_outer] at hj
      cases hb : a.1.val a.2 <;>
        simp [RegisteredPrime.exterior, RegisteredPrime.bit, hb] at hj
  | inr j =>
      obtain ⟨i, hi⟩ := h.2
      rw [facetOutsideIndex_inner] at hi
      norm_num at hi

/-- The actual owner of the cell beyond a facet has an exposed companion
facet with exactly opposite normal and the same literal center. -/
theorem facet_companion_of_outside_owner {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (f : Facet m)
    (hd : RegisteredPrime.Disjoint (RegisteredPrime.identityPose (m+1)) q)
    (hq : RegisteredPrime.Occupies q (facetOutsideIndex f)) :
    ∃ g : Facet m, poseIsometry q (facetCenter g) = facetCenter f ∧
      placedNormal (poseIsometry q) (outward g) = -outward f := by
  obtain ⟨B, hB⟩ := (occupies_iff_native_cell q _).mp hq
  have hba : RegisteredPrime.Adjacent (cellIndex B)
      (q.inv.cell (cellIndex (facetInsideCell f))) := by
    have h := (q.inv.adjacent_cells _ _ (adjacent_facet_inside_outside f)).symm
    rwa [← hB, RegisteredPrime.Pose.inv_cell_cell] at h
  have haout : ¬ ∃ C : Cell m, cellIndex C = q.inv.cell (cellIndex (facetInsideCell f)) := by
    rintro ⟨C, hC⟩
    apply hd (cellIndex (facetInsideCell f))
    refine ⟨⟨_, cellIndex_unitChairCell _, RegisteredPrime.identity_cell _⟩,
      (occupies_iff_native_cell q _).mpr ⟨C, ?_⟩⟩
    rw [hC, RegisteredPrime.Pose.cell_inv_cell]
  obtain ⟨g, hg, hgo⟩ := native_cell_exposed_neighbor B _ hba haout
  refine ⟨g, facet_match_of_crossed_cells q f g ?_ ?_⟩
  · rw [hg, hB]
  · rw [hgo, RegisteredPrime.Pose.cell_inv_cell]

/-- Every prescribed native site has a physical mate on its outside cell's
actual registered owner. -/
theorem site_mate_of_outside_owner {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (u : Site m)
    (hd : RegisteredPrime.Disjoint (RegisteredPrime.identityPose (m+1)) q)
    (hq : RegisteredPrime.Occupies q (facetOutsideIndex u.1)) :
    ∃ v : Site m, SiteTransport (poseIsometry q) u v := by
  obtain ⟨g, hc, hn⟩ := facet_companion_of_outside_owner q u.1 hd hq
  obtain ⟨v, _, hv⟩ := exists_siteTransport_prescribed_root q u g hc hn
  exact ⟨v, hv⟩

/-- Cell coverage supplies a distinct actual mate for every root site. -/
theorem registered_root_site_mate {m : ℕ} (W : RegisteredPrime.RegisteredWorld (m+1))
    (hroot : W.tiles (RegisteredPrime.identityPose (m+1))) (u : Site m) :
    ∃ q, W.tiles q ∧ q ≠ RegisteredPrime.identityPose (m+1) ∧
      ∃ v : Site m, SiteTransport (poseIsometry q) u v := by
  obtain ⟨q, hq, hqo⟩ := W.covers (facetOutsideIndex u.1)
  have hne : q ≠ RegisteredPrime.identityPose (m+1) := by
    intro he
    subst q
    exact facetOutsideIndex_not_unitChairCell u.1
      ((RegisteredPrime.identity_occupies _).mp hqo)
  exact ⟨q, hq, hne, site_mate_of_outside_owner q u
    (registeredWorld_disjoint W hroot hq hne.symm) hqo⟩

/-- A distinct carrier meeting a root tube must be its actual paired owner.
Thus no third carrier can cross any part of the closed tube. -/
theorem registered_root_tube_isolation {m J : ℕ}
    (W : RegisteredPrime.RegisteredWorld (m+1))
    (hroot : W.tiles (RegisteredPrime.identityPose (m+1)))
    (q : RegisteredPrime.Pose (m+1)) (hq : W.tiles q)
    (hne : q ≠ RegisteredPrime.identityPose (m+1)) (u : Site m) :
    Disjoint (closedTube J u) (poseIsometry q '' carrier m) ∨
      ∃ v : Site m, SiteTransport (poseIsometry q) u v := by
  by_cases hd : Disjoint (closedTube J u) (poseIsometry q '' carrier m)
  · exact Or.inl hd
  right
  have hx : (closedTube J u ∩ (poseIsometry q '' carrier m)).Nonempty :=
    Set.not_disjoint_iff.mp hd
  rcases carrier_meets_native_tube_owner q u hx with hin | hout
  · exact False.elim (hne (W.nonoverlap q _ hq hroot _ hin
      ⟨_, cellIndex_unitChairCell _, RegisteredPrime.identity_cell _⟩).eq)
  · exact site_mate_of_outside_owner q u
      (registeredWorld_disjoint W hroot hq hne.symm) hout

/-- Every actual registered-world tube has a distinct world tile carrying
its exact full-orbit mate. -/
theorem registered_world_site_mate {m : ℕ} (W : RegisteredPrime.RegisteredWorld (m+1))
    (q : RegisteredPrime.Pose (m+1)) (hq : W.tiles q) (u : Site m) :
    ∃ r, W.tiles r ∧ r ≠ q ∧ ∃ v : Site m,
      SiteTransport (relativePlacement (poseIsometry q) (poseIsometry r)) u v := by
  obtain ⟨s, hs, hne, v, hv⟩ :=
    registered_root_site_mate (W.reframe q) (W.reframe_root q hq) u
  refine ⟨q.comp s, hs, ?_, v, ?_⟩
  · intro he
    apply hne
    apply RegisteredPrime.Pose.comp_left_cancel q
    simpa only [RegisteredPrime.Pose.comp_identity] using he
  · have he : q.relative (q.comp s) = s := by
      simp only [RegisteredPrime.Pose.relative, ← RegisteredPrime.Pose.comp_assoc,
        RegisteredPrime.Pose.inv_comp, RegisteredPrime.Pose.identity_comp]
    rw [← poseIsometry_relative, he]
    exact hv

/-- The literal world-coordinate carrier isolation property required by
finite tube replacement, derived solely from registered cell ownership. -/
theorem registered_world_tube_isolation {m J : ℕ}
    (W : RegisteredPrime.RegisteredWorld (m+1))
    (q r : RegisteredPrime.Pose (m+1)) (hq : W.tiles q) (hr : W.tiles r)
    (hne : q ≠ r) (u : Site m) :
    Disjoint (poseIsometry q '' closedTube J u) (poseIsometry r '' carrier m) ∨
      ∃ v : Site m, poseIsometry q '' closedTube J u = poseIsometry r '' closedTube J v := by
  have hs : (W.reframe q).tiles (q.relative r) := by
    change W.tiles (q.comp (q.relative r))
    rwa [RegisteredPrime.Pose.comp_relative]
  have hne' : q.relative r ≠ RegisteredPrime.identityPose (m+1) := by
    intro he
    have he' := congrArg (q.comp ·) he
    simp only [RegisteredPrime.Pose.comp_relative, RegisteredPrime.Pose.comp_identity] at he'
    exact hne he'.symm
  rcases registered_root_tube_isolation (J := J) (W.reframe q)
    (W.reframe_root q hq) (q.relative r) hs hne' u with hd | ⟨v, hv⟩
  · left
    have hd' := (Set.disjoint_image_iff (poseIsometry q).injective).mpr hd
    rwa [poseIsometry_relative, placed_relative_image] at hd'
  · right
    rw [poseIsometry_relative] at hv
    exact ⟨v, hv.placed_closedTube J⟩

#print axioms registered_world_site_mate
#print axioms registered_world_tube_isolation
#print axioms registered_root_site_mate
#print axioms registered_root_tube_isolation
#print axioms closedTube_latticeCell_cases
#print axioms carrier_meets_native_tube_owner
end
end PhysicalRegistration.NativeChair

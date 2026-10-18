module

public import ProductClosure.NativeContactFacet
public import ProductClosure.PoseMaterialRealization
public import ProductClosure.NativeMaterialGluing
public import ProductClosure.ProductWorldReindex

@[expose] public section

/-! Actual registered cell ownership isolates every native finite-polycube tube. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}

theorem mem_posed_carrier_iff (S : Finset (LatticeIndex m))
    (q : RegisteredPrime.Pose (m + 1)) (x : Space m) :
    x ∈ poseIsometry q '' Polycube.carrier S ↔
      ∃ z ∈ World.placedCells S q, x ∈ latticeCell z := by
  change x ∈ World.placedCarrier S q ↔ _
  rw [World.placedCarrier_eq_carrier_image, Polycube.mem_carrier_iff]
  simp [World.placedCells]

@[simp] theorem facetInsideCell_tangent_index  (f : Facet S) (i : Fin (m+1))
    (hi : i ≠ normalIndex f) : cellIndex (facetInsideCell f) i = facetCellCoordinate f i := by
  rfl

@[simp] theorem facetInsideCell_normal_index  (f : Facet S) :
    cellIndex (facetInsideCell f) (normalIndex f) =
      facetPlane f - if facetPositive f then 1 else 0 := by
  change f.cell.val f.axis = Polycube.facetPlane f - if f.positive then 1 else 0
  simp only [Polycube.facetPlane]
  omega

@[simp] theorem facetOutsideIndex_normal  (f : Facet S) :
    facetOutsideIndex f (normalIndex f) =
      facetPlane f - if facetPositive f then 0 else 1 := by
  change Polycube.facetOutsideIndex f f.axis = _
  unfold Polycube.facetOutsideIndex Polycube.latticeStep
  change _ = Polycube.facetPlane f - if f.positive then 0 else 1
  simp only [ite_true, Polycube.facetPlane]
  cases f.positive <;> simp <;> omega

@[simp] theorem facetOutsideIndex_tangent  (f : Facet S) (i : Fin (m+1))
    (hi : i ≠ normalIndex f) : facetOutsideIndex f i = facetCellCoordinate f i := by
  simp [facetOutsideIndex, Polycube.facetOutsideIndex, Polycube.latticeStep,
    normalIndex, facetCellCoordinate, show i ≠ f.axis from hi]

/-- A native tube meets only the two literal lattice cells adjacent to its
facet. Strict transverse margins include all closed-tube boundary points. -/
theorem closedTube_latticeCell_cases {J : ℕ} (u : Site S) {x : Space m}
    (hx : x ∈ closedTube J u) (z : LatticeIndex m) (hz : x ∈ latticeCell z) :
    z = cellIndex (facetInsideCell u.1) ∨ z = facetOutsideIndex u.1 := by
  have hn := closedTube_subset_facetNeighborhood u hx
  have ht : ∀ i, i ≠ normalIndex u.1 → z i = facetCellCoordinate u.1 i := by
    intro i hi
    have hxcoord := abs_lt.mp (hn i)
    change -(1 / 2 : ℝ) < x i - facetCenter u.1 i ∧ x i - facetCenter u.1 i < 1 / 2 at hxcoord
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
    change -(1 / 2 : ℝ) < x (normalIndex u.1) - facetCenter u.1 (normalIndex u.1) ∧
      x (normalIndex u.1) - facetCenter u.1 (normalIndex u.1) < 1 / 2 at hxcoord
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
theorem carrier_meets_native_tube_owner {J : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (u : Site S)
    (hx : (closedTube J u ∩ (poseIsometry q '' Polycube.carrier S)).Nonempty) :
    cellIndex (facetInsideCell u.1) ∈ World.placedCells S q ∨
      facetOutsideIndex u.1 ∈ World.placedCells S q := by
  obtain ⟨x, hxT, hxC⟩ := hx
  obtain ⟨z, hqz, hxz⟩ := (mem_posed_carrier_iff S q x).mp hxC
  rcases closedTube_latticeCell_cases u hxT z hxz with rfl | rfl
  · exact Or.inl hqz
  · exact Or.inr hqz


@[simp] theorem placedCells_identity (S : Finset (LatticeIndex m)) :
    World.placedCells S (RegisteredPrime.identityPose (m + 1)) = (S : Set (LatticeIndex m)) := by
  ext z
  simp [World.placedCells, World.poseCellIndex_eq_cell, RegisteredPrime.identity_cell]

theorem occupies_iff_native_cell (q : RegisteredPrime.Pose (m + 1)) (z : LatticeIndex m) :
    z ∈ World.placedCells S q ↔ ∃ c : Polycube.Cell S, q.cell (cellIndex c) = z := by
  simp [World.placedCells, World.poseCellIndex_eq_cell, cellIndex]

theorem adjacent_facet_inside_outside (f : Facet S) :
    RegisteredPrime.Adjacent (cellIndex (facetInsideCell f)) (facetOutsideIndex f) := by
  refine ⟨normalIndex f, ?_, ?_⟩
  · cases h : f.positive <;>
      simp [cellIndex, facetInsideCell, facetOutsideIndex, Polycube.facetOutsideIndex,
        Polycube.latticeStep, normalIndex, h]
  · intro i hi
    simp [cellIndex, facetInsideCell, facetOutsideIndex, Polycube.facetOutsideIndex,
      Polycube.latticeStep, show i ≠ f.axis from hi]

/-- An exposed facet's outside neighbor is literally absent from occupancy. -/
theorem facetOutsideIndex_not_mem (f : Facet S) : facetOutsideIndex f ∉ S := f.outside

/-- The owner beyond an exposed facet has a genuine opposed companion facet. -/
theorem facet_companion_of_outside_owner (q : RegisteredPrime.Pose (m+1))
    (f : Facet S)
    (hd : Disjoint (S : Set (LatticeIndex m)) (World.placedCells S q))
    (hq : facetOutsideIndex f ∈ World.placedCells S q) :
    ∃ g : Facet S, poseIsometry q (facetCenter g) = facetCenter f ∧
      placedNormal (poseIsometry q) (outward g) = -outward f := by
  obtain ⟨B, hB⟩ := (occupies_iff_native_cell q _).mp hq
  have hba : RegisteredPrime.Adjacent (cellIndex B)
      (q.inv.cell (cellIndex (facetInsideCell f))) := by
    have h := (q.inv.adjacent_cells _ _ (adjacent_facet_inside_outside f)).symm
    rwa [← hB, RegisteredPrime.Pose.inv_cell_cell] at h
  have haout : ¬ ∃ C : Polycube.Cell S,
      cellIndex C = q.inv.cell (cellIndex (facetInsideCell f)) := by
    rintro ⟨C, hC⟩
    apply Set.disjoint_left.mp hd f.cell.property
    apply (occupies_iff_native_cell q _).mpr
    refine ⟨C, ?_⟩
    rw [hC, RegisteredPrime.Pose.cell_inv_cell]
    rfl
  obtain ⟨g, hg, hgo⟩ := native_cell_exposed_neighbor B _ hba haout
  refine ⟨g, facet_match_of_crossed_cells q f g ?_ ?_⟩
  · rw [hg, hB]
  · rw [hgo, RegisteredPrime.Pose.cell_inv_cell]

/-- The full tangent-frame orbit completes every prescribed root site. -/
theorem site_mate_of_outside_owner (q : RegisteredPrime.Pose (m+1))
    (u : Site S)
    (hd : Disjoint (S : Set (LatticeIndex m)) (World.placedCells S q))
    (hq : facetOutsideIndex u.1 ∈ World.placedCells S q) :
    ∃ v : Site S, SiteTransport (poseIsometry q) u v := by
  obtain ⟨g, hc, hn⟩ := facet_companion_of_outside_owner q u.1 hd hq
  obtain ⟨v, _, hv⟩ := exists_siteTransport_prescribed_root q u g hc hn
  exact ⟨v, hv⟩

/-- Complete cell coverage supplies a distinct actual mate of every native site. -/
theorem registered_root_site_mate (W : World.CompleteTiling (World.placedCells S))
    (hroot : RegisteredPrime.identityPose (m+1) ∈ W.tiles) (u : Site S) :
    ∃ q, q ∈ W.tiles ∧ q ≠ RegisteredPrime.identityPose (m+1) ∧
      ∃ v : Site S, SiteTransport (poseIsometry q) u v := by
  obtain ⟨q, hq, hqo⟩ := W.cover (facetOutsideIndex u.1)
  have hne : q ≠ RegisteredPrime.identityPose (m+1) := by
    intro he
    subst q
    apply facetOutsideIndex_not_mem u.1
    change facetOutsideIndex u.1 ∈ (S : Set (LatticeIndex m))
    simpa only [placedCells_identity] using hqo
  refine ⟨q, hq, hne, site_mate_of_outside_owner q u ?_ hqo⟩
  simpa only [placedCells_identity] using W.disjoint _ hroot q hq hne.symm

/-- A distinct carrier meeting a root tube owns precisely its outside cell. -/
theorem registered_root_tube_isolation {J : ℕ}
    (W : World.CompleteTiling (World.placedCells S))
    (hroot : RegisteredPrime.identityPose (m+1) ∈ W.tiles)
    (q : RegisteredPrime.Pose (m+1)) (hq : q ∈ W.tiles)
    (hne : q ≠ RegisteredPrime.identityPose (m+1)) (u : Site S) :
    Disjoint (closedTube J u) (poseIsometry q '' Polycube.carrier S) ∨
      ∃ v : Site S, SiteTransport (poseIsometry q) u v := by
  by_cases hd : Disjoint (closedTube J u) (poseIsometry q '' Polycube.carrier S)
  · exact Or.inl hd
  right
  have hx : (closedTube J u ∩ (poseIsometry q '' Polycube.carrier S)).Nonempty :=
    Set.not_disjoint_iff.mp hd
  have hdq : Disjoint (S : Set (LatticeIndex m)) (World.placedCells S q) := by
    simpa only [placedCells_identity] using W.disjoint _ hroot q hq hne.symm
  rcases carrier_meets_native_tube_owner q u hx with hin | hout
  · exact False.elim (Set.disjoint_left.mp hdq u.1.cell.property hin)
  · exact site_mate_of_outside_owner q u hdq hout

/-- Every world-coordinate tube has a distinct placed exact full-orbit mate. -/
theorem registered_world_site_mate (W : World.CompleteTiling (World.placedCells S))
    (q : RegisteredPrime.Pose (m+1)) (hq : q ∈ W.tiles) (u : Site S) :
    ∃ r, r ∈ W.tiles ∧ r ≠ q ∧ ∃ v : Site S,
      SiteTransport (relativePlacement (poseIsometry q) (poseIsometry r)) u v := by
  have hroot : RegisteredPrime.identityPose (m + 1) ∈ (W.reframe q).tiles := by
    change q.comp (RegisteredPrime.identityPose (m + 1)) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_identity] using hq
  obtain ⟨s, hs, hne, v, hv⟩ := registered_root_site_mate (W.reframe q) hroot u
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

/-- Tube isolation follows from actual integer-cell ownership. -/
theorem registered_world_tube_isolation {J : ℕ}
    (W : World.CompleteTiling (World.placedCells S))
    (q r : RegisteredPrime.Pose (m+1)) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hne : q ≠ r) (u : Site S) :
    Disjoint (poseIsometry q '' closedTube J u) (poseIsometry r '' Polycube.carrier S) ∨
      ∃ v : Site S, poseIsometry q '' closedTube J u = poseIsometry r '' closedTube J v := by
  have hs : q.relative r ∈ (W.reframe q).tiles := by
    change q.comp (q.relative r) ∈ W.tiles
    rwa [RegisteredPrime.Pose.comp_relative]
  have hroot : RegisteredPrime.identityPose (m + 1) ∈ (W.reframe q).tiles := by
    change q.comp (RegisteredPrime.identityPose (m + 1)) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_identity] using hq
  have hne' : q.relative r ≠ RegisteredPrime.identityPose (m+1) := by
    intro he
    have he' := congrArg (q.comp ·) he
    simp only [RegisteredPrime.Pose.comp_relative, RegisteredPrime.Pose.comp_identity] at he'
    exact hne he'.symm
  rcases registered_root_tube_isolation (J := J) (W.reframe q)
    hroot (q.relative r) hs hne' u with hd | ⟨v, hv⟩
  · left
    have hd' := (Set.disjoint_image_iff (poseIsometry q).injective).mpr hd
    rwa [poseIsometry_relative, placed_relative_image] at hd'
  · right
    rw [poseIsometry_relative] at hv
    exact ⟨v, hv.placed_closedTube J⟩

#print axioms registered_world_site_mate
#print axioms registered_world_tube_isolation
#print axioms closedTube_latticeCell_cases
end
end ProductClosure.NativeCompiler

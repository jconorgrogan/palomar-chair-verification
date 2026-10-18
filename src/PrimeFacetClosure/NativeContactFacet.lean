module

public import PrimeFacetClosure.NativeFreeOrbit

@[expose] public section

/-! Actual registered carrier contacts supply exposed native facet pairs,
then full free-orbit site pairs. No profile or facet-cover certificate. -/
namespace PhysicalRegistration.NativeChair
noncomputable section

/-- Integer adjacency is exactly one signed coordinate step. -/
theorem adjacent_is_latticeStep {m : ℕ} (a b : LatticeIndex m)
    (h : RegisteredPrime.Adjacent a b) :
    ∃ j side, b = latticeStep a j side := by
  obtain ⟨j, hj, ht⟩ := h
  rcases hj with hj | hj
  · refine ⟨j, false, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i; simp [latticeStep]; omega
    · simp [latticeStep, hij, ht i hij]
  · refine ⟨j, true, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i; simp [latticeStep]; omega
    · simp [latticeStep, hij, ht i hij]

/-- An adjacent cell outside the carrier crosses a literal exposed facet. -/
theorem native_cell_exposed_neighbor {m : ℕ} (A : Cell m) (b : LatticeIndex m)
    (hab : RegisteredPrime.Adjacent (cellIndex A) b)
    (hb : ¬ ∃ B : Cell m, cellIndex B = b) :
    ∃ f : Facet m, facetInsideCell f = A ∧ facetOutsideIndex f = b := by
  obtain ⟨j, side, rfl⟩ := adjacent_is_latticeStep (cellIndex A) b hab
  rcases occupied_cell_neighbor A j side with ⟨B, hB⟩ | ⟨f, hf, hout⟩
  · exact False.elim (hb ⟨B, hB.symm⟩)
  · exact ⟨f, hf, hout.symm⟩

/-- Opposite inside/outside cell transport identifies the actual facet
centers and reverses their actual outward normals. -/
theorem facet_match_of_crossed_cells {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (f g : Facet m)
    (hgo : q.cell (cellIndex (facetInsideCell g)) = facetOutsideIndex f)
    (hgi : q.cell (facetOutsideIndex g) = cellIndex (facetInsideCell f)) :
    poseIsometry q (facetCenter g) = facetCenter f ∧
      placedNormal (poseIsometry q) (outward g) = -outward f := by
  have h₁ := (poseIsometry_realizes q).map_latticeCenter (cellIndex (facetInsideCell g))
  rw [hgo, latticeCenter_cellIndex, facetInsideCell_center, facetOutsideIndex_center] at h₁
  have h₂ := (poseIsometry_realizes q).map_latticeCenter (facetOutsideIndex g)
  rw [hgi, latticeCenter_cellIndex, facetInsideCell_center, facetOutsideIndex_center] at h₂
  constructor
  · ext i
    have h₁i := congrArg (fun x : Space m => x i) h₁
    have h₂i := congrArg (fun x : Space m => x i) h₂
    simp only [poseIsometry_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul] at h₁i h₂i ⊢
    linarith
  · ext i
    rw [placedNormal_poseIsometry_apply]
    have h₁i := congrArg (fun x : Space m => x i) h₁
    have h₂i := congrArg (fun x : Space m => x i) h₂
    simp only [poseIsometry_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      PiLp.neg_apply, smul_eq_mul] at h₁i h₂i ⊢
    linarith

/-- The adjacent occupied cells in any genuine carrier face contact expose
one facet on each tile. Their centers coincide and their normals oppose. -/
theorem faceContact_exists_native_facets {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (hc : RegisteredPrime.FaceContact (RegisteredPrime.identityPose (m+1)) q) :
    ∃ f g : Facet m, poseIsometry q (facetCenter g) = facetCenter f ∧
      placedNormal (poseIsometry q) (outward g) = -outward f := by
  obtain ⟨hd, a, b, ha, hb, hab⟩ := hc
  obtain ⟨A, hA⟩ := (occupies_iff_native_cell (RegisteredPrime.identityPose (m+1)) a).mp ha
  rw [RegisteredPrime.identity_cell] at hA
  obtain ⟨B, hB⟩ := (occupies_iff_native_cell q b).mp hb
  have hbout : ¬ ∃ C : Cell m, cellIndex C = b := by
    rintro ⟨C, hC⟩
    apply hd b
    refine ⟨(occupies_iff_native_cell (RegisteredPrime.identityPose (m+1)) b).mpr ⟨C, ?_⟩, hb⟩
    simpa only [RegisteredPrime.identity_cell] using hC
  obtain ⟨f, hf, hfo⟩ := native_cell_exposed_neighbor A b (hA ▸ hab) hbout
  have hba : RegisteredPrime.Adjacent (cellIndex B) (q.inv.cell a) := by
    have h := (q.inv.adjacent_cells a b hab).symm
    rwa [← hB, RegisteredPrime.Pose.inv_cell_cell] at h
  have haout : ¬ ∃ C : Cell m, cellIndex C = q.inv.cell a := by
    rintro ⟨C, hC⟩
    apply hd a
    refine ⟨ha, (occupies_iff_native_cell q a).mpr ⟨C, ?_⟩⟩
    rw [hC, RegisteredPrime.Pose.cell_inv_cell]
  obtain ⟨g, hg, hgo⟩ := native_cell_exposed_neighbor B (q.inv.cell a) hba haout
  refine ⟨f, g, facet_match_of_crossed_cells q f g ?_ ?_⟩
  · rw [hg, hB, hfo]
  · rw [hgo, RegisteredPrime.Pose.cell_inv_cell, hf, hA]

/-- Every genuine registered carrier face contact has a literal pair of
native full-orbit sites matched by its actual Euclidean pose. This supplies
the initial witness required by the facet-profile classification. -/
theorem faceContact_exists_siteTransport {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (hc : RegisteredPrime.FaceContact (RegisteredPrime.identityPose (m+1)) q) :
    ∃ u v : Site m, SiteTransport (poseIsometry q) u v := by
  obtain ⟨f, g, hfg, hn⟩ := faceContact_exists_native_facets q hc
  obtain ⟨u, v, _, _, huv⟩ := exists_siteTransport_of_facet_match q f g hfg hn
  exact ⟨u, v, huv⟩

#print axioms faceContact_exists_native_facets
#print axioms faceContact_exists_siteTransport
end
end PhysicalRegistration.NativeChair

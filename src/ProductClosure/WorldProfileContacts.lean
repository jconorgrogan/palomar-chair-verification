module

public import ProductClosure.PhysicalProfileLaw
public import ProductClosure.RegisteredTubeOwners

@[expose] public section

/-! Literal site mating witnesses actual adjacent occupied cells. Neighbor
laws therefore apply to every site equation, with no global-contact callback. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}

/-- The exact inward cell of a transported key is the root's outward cell. -/
theorem SiteTransport.relative_cell_neighbor
    (q r : RegisteredPrime.Pose (m+1)) (u v : Site S)
    (ht : SiteTransport (poseIsometry (q.relative r)) u v) :
    r.cell (cellIndex (facetInsideCell v.1)) = q.cell (facetOutsideIndex u.1) := by
  letI : Nonempty (Polycube.Cell S) := ⟨u.1.cell⟩
  rw [poseIsometry_relative] at ht
  obtain ⟨ha,hn,hc⟩ := ht.relative_world_frame (poseIsometry q) (poseIsometry r) u v
  have he := matched_companion_cellCenter u v (poseIsometry q) (poseIsometry r) ha hn hc
  have h₁ := poseIsometry_map_latticeCenter r (cellIndex (facetInsideCell v.1))
  rw [latticeCenter_cellIndex] at h₁
  rw [h₁, poseIsometry_map_latticeCenter] at he
  exact latticeCenter_injective he

/-- No legality is needed: any actual full site match gives genuine occupied
unit cells on the two sides of the same carrier wall. -/
theorem SiteTransport.exists_adjacent_occupied
    (q r : RegisteredPrime.Pose (m+1)) (u v : Site S)
    (ht : SiteTransport (poseIsometry (q.relative r)) u v) :
    ∃ x ∈ World.placedCells S q, ∃ y ∈ World.placedCells S r,
      World.LatticeAdjacent x y := by
  refine ⟨q.cell (cellIndex (facetInsideCell u.1)), ?_,
    r.cell (cellIndex (facetInsideCell v.1)), ?_, ?_⟩
  · exact (occupies_iff_native_cell q _).mpr ⟨facetInsideCell u.1,rfl⟩
  · exact (occupies_iff_native_cell r _).mpr ⟨facetInsideCell v.1,rfl⟩
  · rw [ht.relative_cell_neighbor q r u v, World.latticeAdjacent_iff_registered]
    exact q.adjacent_cells _ _ (adjacent_facet_inside_outside u.1)

/-- Complete-world neighboring-owner legality controls every supplied actual
site match between distinct placed states. -/
theorem legal_of_siteTransport
    (W : World.CompleteTiling (World.placedCells S))
    {M : RegisteredPrime.Pose (m+1) → RegisteredPrime.Pose (m+1) → Prop}
    (hl : W.IsLegal World.LatticeAdjacent M)
    (q r : RegisteredPrime.Pose (m+1)) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hne : q ≠ r) (u v : Site S)
    (ht : SiteTransport (poseIsometry (q.relative r)) u v) : M q r := by
  obtain ⟨x,hx,y,hy,hxy⟩ := ht.exists_adjacent_occupied q r u v
  have hqx := W.owner_eq_of_mem hq hx
  have hry := W.owner_eq_of_mem hr hy
  have h := hl x y hxy (by intro he; exact hne (hqx.symm.trans (he.trans hry)))
  rwa [hqx,hry] at h

/-- Neighboring-owner full profiles extend to all distinct placed pairs,
because every equation to be tested itself supplies a genuine contact. -/
theorem fullProfiles_of_neighbor_profiles {J : ℕ} (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S))
    (hl : W.IsLegal World.LatticeAdjacent (fun q r =>
      FullProfileMating a (poseIsometry (q.relative r)))) :
    ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r →
      FullProfileMating a (poseIsometry (q.relative r)) := by
  intro q hq r hr hne u v ht
  exact legal_of_siteTransport W hl q r hq hr hne u v ht u v ht

end
end ProductClosure.NativeCompiler

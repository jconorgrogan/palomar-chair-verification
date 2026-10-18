module

public import SpectreGeometry.PolygonProductKeyPacking

@[expose] public section


/-! Finite actual boundary-incident neighborhoods at concrete key-graph points.
The tiling interface has only coverage and interior disjointness. Finiteness,
boundary incidence and neighborhood coverage are conclusions, not supplied
cone fans or angular-conservation premises. -/
namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace Topology

private theorem local_graph_mem_closure_interior {S : Set EFour} {x : EFour} {L : ℝ}
    (G : LocalLipschitzGraphAt S x L) : x ∈ closure (interior S) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hr := G.radius_pos
  let t := min ε G.radius / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htε : t < ε := by dsimp [t]; have := min_le_left ε G.radius; linarith
  have htr : t < G.radius := by
    dsimp [t]
    have := min_le_right ε G.radius
    linarith
  refine ⟨x + t • G.inward, ?_, ?_⟩
  · simpa using G.interior_above 0 t (by simp)
      (by simpa using G.radius_pos) (by rwa [abs_of_pos ht])
      (by simpa [G.height_zero] using ht)
  · simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs, G.inward_unit,
      abs_of_pos ht, norm_sub_rev] using htε

theorem placed_product_key_window_subset_frontier (f : EFour ≃ᵢ EFour)
    (u : ProductKeySite) :
    placedProductKeyGraphWindow f u ⊆ frontier (placedPolygonProductKeyBody f) := by
  change f.toHomeomorph '' productKeyGraphWindow u ⊆
    frontier (f.toHomeomorph '' polygonProductKeyBody)
  rw [← f.toHomeomorph.image_frontier]
  exact image_mono (product_key_graph_window_subset_frontier u)

theorem placed_product_key_window_subset_closure_interior (f : EFour ≃ᵢ EFour)
    (u : ProductKeySite) :
    placedProductKeyGraphWindow f u ⊆ closure (interior (placedPolygonProductKeyBody f)) := by
  intro x hx
  exact local_graph_mem_closure_interior (placedProductKeyGraphWindow_local_graph f u x hx)

theorem placed_product_key_window_notMem_any_interior {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (root : ι) (u : ProductKeySite) (x : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u) (i : ι) :
    x ∉ interior (placedPolygonProductKeyBody (f i)) := by
  by_cases hi : root = i
  · subst i
    exact (placed_product_key_window_subset_frontier (f root) u hx).2
  · exact Set.disjoint_left.mp ((hdisjoint hi).closure_left isOpen_interior)
      (placed_product_key_window_subset_closure_interior (f root) u hx)

theorem placed_product_key_incident_mem_frontier {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (root : ι) (u : ProductKeySite) (x : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u) (i : ι)
    (hi : i ∈ polygonProductIncidentTiles f x) :
    x ∈ frontier (placedPolygonProductKeyBody (f i)) :=
  ⟨subset_closure hi, placed_product_key_window_notMem_any_interior f hdisjoint root u x hx i⟩

theorem PolygonProductPhysicalTiling.finite_key_boundary_germ {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (x : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u) :
    (polygonProductIncidentTiles f x).Finite ∧
    (∀ i ∈ polygonProductIncidentTiles f x,
      x ∈ frontier (placedPolygonProductKeyBody (f i))) ∧
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      (∀ i, i ∉ polygonProductIncidentTiles f x →
        Disjoint (placedPolygonProductKeyBody (f i)) U) ∧
      (∀ y ∈ U, ∃ i ∈ polygonProductIncidentTiles f x,
        y ∈ placedPolygonProductKeyBody (f i)) ∧
      Pairwise (fun (i j : polygonProductIncidentTiles f x) =>
        Disjoint (interior (placedPolygonProductKeyBody (f i.val)))
          (interior (placedPolygonProductKeyBody (f j.val)))) :=
  ⟨(T.finite_incident_germ x).1,
    fun i hi => placed_product_key_incident_mem_frontier f T.interiors_disjoint
      root u x hx i hi, (T.finite_incident_germ x).2⟩

end
end SpectreGeometry

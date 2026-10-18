module

public import SpectreGeometry.PolygonProductKeyIncidentConeModels
public import SpectreGeometry.PolygonProductKeyIncidentConservation
public import SpectreGeometry.PolygonProductKeyNormalCharts
public import SpectreGeometry.PolygonProductKeyCompanionPropagation

@[expose] public section


/-! Actual complementary key incidence and whole-crease companions for every
physical tiling by the concrete optimized product body. The physical tiling
has only coverage and pairwise interior disjointness. Finite incidents,
transverse charts, actual strata, angular conservation, and no-switching are
all derived by the checked geometric interfaces. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set

private theorem companion_of_root_model {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (x p q : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hL : LinearMap.range L.toLinearMap = Submodule.span ℝ {p,q})
    (hr : ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
      ∀ k : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane k →
      (f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal k) ∈ Set.range L)
    (Mroot : ActualBoundaryConeModel (f root) x L)
    (hroot : ActualKeyMass (f root) x L Mroot.cone) :
    ∃ j : ι, j ≠ root ∧ ∃ v : ProductKeySite, x ∈ f j '' creaseComplex v := by
  classical
  let I := polygonProductIncidentTiles f x
  let : Fintype I := (T.finite_incident_germ x).1.fintype
  have hex : ∀ i : I, ∃ M : ActualBoundaryConeModel (f i.val) x L,
      ConeSectorClassification (f i.val) x L M.cone ∧
        (i.val = root → ActualKeyMass (f i.val) x L M.cone) := by
    rintro ⟨i,hi⟩
    by_cases hir : i = root
    · subst i
      exact ⟨Mroot,Or.inr hroot,fun _ => hroot⟩
    · have hfront := placed_product_key_incident_mem_frontier f T.interiors_disjoint root u x hx i hi
      obtain ⟨M,hM⟩ := incident_boundary_cone_model (f i) x p q L hL hfront (hr i hi)
      exact ⟨M,hM,fun h => (hir h).elim⟩
  choose M hM using hex
  have hrootmem : root ∈ I := image_mono (product_key_graph_window_subset_body u) hx
  exact classified_actual_incident_companion T root u x hx L M (fun i => (hM i).1)
    ⟨⟨root,hrootmem⟩,(hM ⟨root,hrootmem⟩).2 rfl⟩

/-- Dense complementary incidence on every actual base crease. -/
theorem physical_base_crease_dense_companions {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (b : ProductKeySide) :
    ∃ D : Set EFour, D ⊆ f root '' baseGeneric u b ∧
      closure D = f root '' baseCrease u b ∧
      ∀ x ∈ D, ∃ j : ι, j ≠ root ∧ ∃ v : ProductKeySite, x ∈ f j '' creaseComplex v := by
  obtain ⟨D,hDG,hDC,hplanes⟩ := baseGeneric_incident_boundary_normal_span f T.interiors_disjoint root u b
  obtain ⟨L,hL⟩ := exists_placed_product_key_base_normal_chart u b (f root)
  rw [affine_linear_eq_displacement] at hL
  have hpair := pair_mem_chart_range _ _ L hL
  refine ⟨D,hDG,hDC,?_⟩
  intro x hx
  obtain ⟨z,hz,rfl⟩ := hDG hx
  have hwindow : f root z ∈ placedProductKeyGraphWindow (f root) u :=
    ⟨z,sideFace_subset_graphWindow u b hz.1.1,rfl⟩
  obtain ⟨M,hMass,hCrease⟩ := exists_base_boundary_cone_model (f root) z L u b hz hpair.1 hpair.2
  apply companion_of_root_model T root u (f root z)
    ((f root).toRealLinearIsometryEquiv (productKeyOutwardNormal u))
    ((f root).toRealLinearIsometryEquiv (productKeySideNormal u b)) hwindow L hL _ M
    ⟨u,hCrease,Or.inl ⟨b,hMass⟩⟩
  intro j hj k hk
  have hn := hplanes (f root z) hx j hj k hk
  change _ ∈ LinearMap.range L.toLinearMap
  rwa [hL]

/-- Dense complementary incidence on every actual distinct-axis side crease. -/
theorem physical_side_crease_dense_companions {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (b c : ProductKeySide) (hbc : b.1 ≠ c.1) :
    ∃ D : Set EFour, D ⊆ f root '' sideGeneric u b c ∧
      closure D = f root '' sideCrease u b c ∧
      ∀ x ∈ D, ∃ j : ι, j ≠ root ∧ ∃ v : ProductKeySite, x ∈ f j '' creaseComplex v := by
  obtain ⟨D,hDG,hDC,hplanes⟩ := sideGeneric_incident_boundary_normal_span f T.interiors_disjoint root u b c hbc
  obtain ⟨L,hL⟩ := exists_placed_product_key_side_normal_chart u b c hbc (f root)
  rw [affine_linear_eq_displacement] at hL
  have hpair := pair_mem_chart_range _ _ L hL
  refine ⟨D,hDG,hDC,?_⟩
  intro x hx
  obtain ⟨z,hz,rfl⟩ := hDG hx
  have hwindow : f root z ∈ placedProductKeyGraphWindow (f root) u :=
    ⟨z,sideFace_subset_graphWindow u b hz.1.1,rfl⟩
  obtain ⟨M,hMass,hCrease⟩ := exists_side_boundary_cone_model (f root) z L u b c hbc hz hpair.1 hpair.2
  apply companion_of_root_model T root u (f root z)
    ((f root).toRealLinearIsometryEquiv (productKeySideNormal u b))
    ((f root).toRealLinearIsometryEquiv (productKeySideNormal u c)) hwindow L hL _ M
    ⟨u,hCrease,Or.inr ⟨b,c,hbc,hMass⟩⟩
  intro j hj k hk
  have hn := hplanes (f root z) hx j hj k hk
  change _ ∈ LinearMap.range L.toLinearMap
  rwa [hL]

/-- Every concrete key has exactly one other indexed whole-crease companion
in an arbitrary physical tiling; no local matching premise remains. -/
theorem physical_whole_crease_companion {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) :
    ∃! jv : ι × ProductKeySite, jv.1 ≠ root ∧
      f root '' creaseComplex u ⊆ f jv.1 '' creaseComplex jv.2 := by
  apply whole_crease_companion_of_dense_matches f T.interiors_disjoint root u
  · intro b
    obtain ⟨D,_,hD,hm⟩ := physical_base_crease_dense_companions T root u b
    exact ⟨D,hD,hm⟩
  · intro b c hbc
    obtain ⟨D,_,hD,hm⟩ := physical_side_crease_dense_companions T root u b c hbc
    exact ⟨D,hD,hm⟩

end
end SpectreGeometry.ProductCrease

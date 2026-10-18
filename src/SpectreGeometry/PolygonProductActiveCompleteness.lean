module

public import SpectreGeometry.PolygonProductActiveFrontier
public import SpectreGeometry.PlanarCountableFrontierCompleteness
public import SpectreGeometry.PolygonProductGlobalFlattening

@[expose] public section


/-! Complete homochiral planar factor tilings in every active-edge component
of an arbitrary actual keyed-product tiling. The constant passive coordinate
is supplied by the component placement specification. Cartesian consistency
between distinct columns and period transport remain separate statements. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem product_active_component_union_eq_univ {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    productActiveComponentUnion P b root = univ :=
  closed_plane_eq_univ_of_countable_frontier _
    (product_active_component_union_closed T P b root)
    (product_active_component_union_interior_nonempty P b root)
    ((product_active_component_vertices_countable T P b root).mono
      (product_active_component_frontier_subset_vertices T P b root))

theorem product_active_component_covers {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι)
    (x : EPlane) :
    ∃ i : ProductActiveComponent P b root, x ∈ productActiveComponentPlacement P b root i '' euclideanBody := by
  have hx : x ∈ productActiveComponentUnion P b root := by
    rw [product_active_component_union_eq_univ T P b root]
    trivial
  exact mem_iUnion.mp hx

theorem product_active_component_homochiral_tiling {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    (∀ i : ProductActiveComponent P b root, DirectPlacement (productActiveComponentPlacement P b root i)) ∧
    (Pairwise fun i j : ProductActiveComponent P b root =>
      Disjoint (interior (productActiveComponentPlacement P b root i '' euclideanBody))
        (interior (productActiveComponentPlacement P b root j '' euclideanBody))) ∧
    (∀ x : EPlane, ∃ i : ProductActiveComponent P b root,
      x ∈ productActiveComponentPlacement P b root i '' euclideanBody) :=
  ⟨product_active_component_placement_direct P b root,
    product_active_component_interiors_disjoint P b root
      (raw_product_interiors_disjoint_of_pairing T P),product_active_component_covers T P b root⟩

theorem physical_product_has_complete_active_components {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) :
    ∃ P : ProductKeyPairing f, ∀ (b : Fin 2) (root : ι),
      (∀ i : ProductActiveComponent P b root, DirectPlacement (productActiveComponentPlacement P b root i)) ∧
      (Pairwise fun i j : ProductActiveComponent P b root =>
        Disjoint (interior (productActiveComponentPlacement P b root i '' euclideanBody))
          (interior (productActiveComponentPlacement P b root j '' euclideanBody))) ∧
      (∀ x : EPlane, ∃ i : ProductActiveComponent P b root,
        x ∈ productActiveComponentPlacement P b root i '' euclideanBody) := by
  obtain ⟨P⟩ := exists_productKeyPairing T
  exact ⟨P,fun b root => product_active_component_homochiral_tiling T P b root⟩

end
end SpectreGeometry

module

public import SpectreGeometry.PolygonProductActiveSlices
public import SpectreGeometry.PolygonProductActiveEdgeNeighborhood
public import SpectreGeometry.BoundaryNonvertex

@[expose] public section


/-! Every nonvertex edge point of an active component is interior to its
union. Thus the actual remaining frontier is countable, with no vertex-star
or component-completeness hypothesis. -/
namespace SpectreGeometry
noncomputable section
open Set

def productActiveComponentUnion {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) : Set EPlane :=
  ⋃ i : ProductActiveComponent P b root, productActiveComponentPlacement P b root i '' euclideanBody

def productActiveComponentVertices {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) : Set EPlane :=
  ⋃ i : ProductActiveComponent P b root,
    Set.range (fun v : Fin 14 => productActiveComponentPlacement P b root i (euclideanVertex v))

theorem product_active_component_partner_transition {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (u : ProductKeySite) (hu : u.1 = b) (a : RealPoint) :
    productActiveComponentPlacement P b root i (euclideanCoordinates a) =
      productActiveComponentPlacement P b root (productActiveComponentPartner P b root i u hu)
        (productActiveEdgeTransition u.2.1 (P.partner i.val u).2.2.1 (euclideanCoordinates a)) := by
  let j := productActiveComponentPartner P b root i u hu
  let A := productActiveEdgeTransition u.2.1 (P.partner i.val u).2.2.1
  have ht : (P.partner i.val u).2.1 = b := (P.sameLabel i.val u).symm.trans hu
  have hr : f i.val (productFactorPoint b a 0) = f j.val (productFactorPoint b
      (euclideanCoordinates.symm (A (euclideanCoordinates a))) 0) := by
    simpa only [hu,ht,j,A,productActiveComponentPartner] using registered_product_factor_transition u (P.partner i.val u).2
      (f i.val) (f (P.partner i.val u).1) (P.oppositeSigns i.val u) (P.samePose i.val u) a 0
  have he := (product_active_component_placement_spec P b root i a 0).symm.trans
    (hr.trans (product_active_component_placement_spec P b root j
      (euclideanCoordinates.symm (A (euclideanCoordinates a))) 0))
  simp only [Homeomorph.apply_symm_apply] at he
  have hh := (f root).injective he
  have hh' : productFactorHomeomorph b
      (euclideanCoordinates.symm (productActiveComponentPlacement P b root i (euclideanCoordinates a)),0) =
      productFactorHomeomorph b
      (euclideanCoordinates.symm (productActiveComponentPlacement P b root j (A (euclideanCoordinates a))),0) := by
    simpa only [product_factor_homeomorph_apply] using hh
  exact euclideanCoordinates.symm.injective
    (congrArg Prod.fst ((productFactorHomeomorph b).injective hh'))

theorem product_active_component_open_edge_interior {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (e : Fin 14) (r : ℝ) (hr : 0 < r) (hr' : r < 1) :
    productActiveComponentPlacement P b root i
      (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) r)) ∈
        interior (productActiveComponentUnion P b root) := by
  let u : ProductKeySite := (b,e,false)
  let j := productActiveComponentPartner P b root i u rfl
  have he := registered_active_edge_mem_interior_union
    (productActiveComponentPlacement P b root i) (productActiveComponentPlacement P b root j)
    e (P.partner i.val u).2.2.1
    (product_active_component_partner_transition P b root i u rfl) r hr hr'
  exact interior_mono (union_subset (subset_iUnion _ i) (subset_iUnion _ j)) he

theorem product_active_component_union_interior_nonempty {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    (interior (productActiveComponentUnion P b root)).Nonempty := by
  let i : ProductActiveComponent P b root := ⟨root,Relation.EqvGen.refl root⟩
  obtain ⟨x,hx⟩ := euclideanBody_interior_nonempty
  refine ⟨productActiveComponentPlacement P b root i x,?_⟩
  apply interior_mono (subset_iUnion _ i)
  exact (productActiveComponentPlacement P b root i).toHomeomorph.isOpenMap.image_interior_subset _
    ⟨x,hx,rfl⟩

theorem product_active_component_vertices_countable {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    (productActiveComponentVertices P b root).Countable := by
  letI : Countable (ProductActiveComponent P b root) :=
    Set.countable_univ_iff.mp (product_active_component_countable T P b root)
  exact Set.countable_iUnion (fun i => Set.countable_range _)

theorem product_active_component_frontier_subset_vertices {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :
    frontier (productActiveComponentUnion P b root) ⊆ productActiveComponentVertices P b root := by
  intro x hx
  have hm : x ∈ productActiveComponentUnion P b root := by
    have hc := hx.1
    change x ∈ closure (⋃ i : ProductActiveComponent P b root,
      productActiveComponentPlacement P b root i '' euclideanBody) at hc
    rw [(product_active_component_union_closed T P b root).closure_eq] at hc
    exact hc
  obtain ⟨i,hi⟩ := mem_iUnion.mp hm
  have hni : x ∉ interior (productActiveComponentPlacement P b root i '' euclideanBody) :=
    fun h => hx.2 (interior_mono (subset_iUnion _ i) h)
  have hfi : x ∈ frontier (productActiveComponentPlacement P b root i '' euclideanBody) :=
    ⟨subset_closure hi,hni⟩
  by_contra hv
  let A := productActiveComponentPlacement P b root i
  let H : RealPoint ≃ₜ EPlane := euclideanCoordinates.trans A.toHomeomorph
  have hid : A '' euclideanBody = H '' polygonBody := by
    rw [euclideanBody,Set.image_image]
    rfl
  change x ∈ frontier (A '' euclideanBody) at hfi
  rw [hid,← H.image_frontier] at hfi
  obtain ⟨a,ha,rfl⟩ := hfi
  have hnv : ∀ v : Fin 14, a ≠ realVertex v := by
    intro v he
    apply hv
    apply mem_iUnion.mpr
    refine ⟨i,v,?_⟩
    simp only [he,euclideanVertex,H,Homeomorph.trans_apply,IsometryEquiv.coe_toHomeomorph]
    rfl
  obtain ⟨e,r,hr,hr',he⟩ := frontier_nonvertex_strict_edge a ha hnv
  apply hx.2
  change A (euclideanCoordinates a) ∈ interior (productActiveComponentUnion P b root)
  rw [he]
  exact product_active_component_open_edge_interior P b root i e r hr hr'

end
end SpectreGeometry

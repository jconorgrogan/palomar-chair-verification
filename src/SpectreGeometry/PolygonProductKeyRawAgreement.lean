module

public import SpectreGeometry.PolygonProductKeyFrontier
public import SpectreGeometry.PolygonProductKeyCollarBoundary

@[expose] public section


/-! Every actual modification is confined to a closed small box strictly inside
its recipe collar. Consequently, at a keyed-body boundary point outside all
actual key graph windows there is an open neighborhood of exact raw-P×P
agreement. This is an actual derived germ, not an ordinary-sector premise. -/
namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace Topology

def productKeyModificationZone (s : ProductKeySite) : Set EFour :=
  {x | (∀ j : Fin 3, |inner ℝ (productKeyTangent s j) (x-productKeyCenter s)| ≤
      productKeyEta) ∧
    |inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s)| ≤
      productKeyEta * 2 / (productKeyN : ℝ)}

theorem product_key_modification_zone_isClosed (s : ProductKeySite) :
    IsClosed (productKeyModificationZone s) := by
  have ht (j : Fin 3) : Continuous
      (fun x : EFour => |inner ℝ (productKeyTangent s j) (x-productKeyCenter s)|) :=
    ((unit_inner_continuous _ (productKeyTangent_norm s j)).comp
      (continuous_id.sub continuous_const)).abs
  have hn : Continuous
      (fun x : EFour => |inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s)|) :=
    ((unit_inner_continuous _ (productKeyOutwardNormal_norm s)).comp
      (continuous_id.sub continuous_const)).abs
  simp only [productKeyModificationZone, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun j => isClosed_le (ht j) continuous_const).inter
    (isClosed_le hn continuous_const)

theorem product_key_modification_zone_subset_collar_interior (s : ProductKeySite) :
    productKeyModificationZone s ⊆ interior (productKeyCollar s) := by
  intro x hx
  apply product_key_strict_collar_subset_interior s
  exact ⟨fun j => (hx.1 j).trans_lt (by norm_num [productKeyEta]),
    hx.2.trans_lt (by norm_num [productKeyEta, productKeyN, productKeyRho])⟩

private theorem key_body_iff_raw_outside_collars (x : EFour)
    (hx : ∀ s, x ∉ productKeyCollar s) :
    x ∈ polygonProductKeyBody ↔ x ∈ polygonProductBody := by
  constructor
  · intro h
    rcases h with ⟨hraw, _⟩ | hkey
    · exact hraw
    · obtain ⟨s,hs⟩ := mem_iUnion.mp hkey
      exact (hx s hs.1).elim
  · intro h
    apply Or.inl
    refine ⟨h, ?_⟩
    intro hc
    obtain ⟨s,hs⟩ := mem_iUnion.mp hc
    exact hx s (interior_subset hs)

/-- A change of membership forces the actual nonzero height support and a
normal coordinate between the raw plane and the new graph. -/
theorem polygon_product_key_change_mem_modification_zone (x : EFour)
    (hne : ¬ (x ∈ polygonProductKeyBody ↔ x ∈ polygonProductBody)) :
    ∃ s, x ∈ productKeyModificationZone s := by
  classical
  by_cases hcollar : ∃ s, x ∈ productKeyCollar s
  · obtain ⟨s,hs⟩ := hcollar
    have hkey := polygon_product_key_body_collar_iff s x hs
    have hraw := (product_key_collar_carrier_outward s x hs).1
    have hh : ¬ (inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) ≤
        productKeyHeight s (x-productKeyCenter s) ↔
        inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) ≤ 0) := by
      intro he
      apply hne
      exact hkey.trans (he.trans hraw.symm)
    have hactive : productKeyHeight s (x-productKeyCenter s) ≠ 0 := by
      intro hz
      exact hh (by rw [hz])
    refine ⟨s, product_key_height_support s (x-productKeyCenter s) hactive, ?_⟩
    have hamp := abs_le.mp (product_key_height_amplitude s (x-productKeyCenter s))
    apply abs_le.mpr
    by_cases hnormal : inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) ≤ 0
    · have hnoth : ¬ inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) ≤
          productKeyHeight s (x-productKeyCenter s) := by
        intro hz
        exact hh ⟨fun _ => hnormal, fun _ => hz⟩
      have hpos : 0 ≤ productKeyEta * 2 / (productKeyN : ℝ) := by
        norm_num [productKeyEta, productKeyN]
      constructor <;> linarith
    · have hheight : inner ℝ (productKeyOutwardNormal s) (x-productKeyCenter s) ≤
          productKeyHeight s (x-productKeyCenter s) := by
        by_contra hn
        exact hh ⟨fun hz => (hn hz).elim, fun hz => (hnormal hz).elim⟩
      have hpos : 0 ≤ productKeyEta * 2 / (productKeyN : ℝ) := by
        norm_num [productKeyEta, productKeyN]
      constructor <;> linarith
  · exact (hne (key_body_iff_raw_outside_collars x (by simpa using hcollar))).elim

theorem polygon_product_key_body_iff_raw_outside_modifications (x : EFour)
    (hx : x ∉ ⋃ s, productKeyModificationZone s) :
    x ∈ polygonProductKeyBody ↔ x ∈ polygonProductBody := by
  by_contra hne
  obtain ⟨s,hs⟩ := polygon_product_key_change_mem_modification_zone x hne
  exact hx (mem_iUnion.mpr ⟨s,hs⟩)

theorem polygon_product_key_exists_raw_neighborhood (x : EFour)
    (hx : x ∉ ⋃ s, productKeyModificationZone s) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ polygonProductKeyBody ↔ y ∈ polygonProductBody := by
  refine ⟨(⋃ s, productKeyModificationZone s)ᶜ,
    (isClosed_iUnion_of_finite fun s => product_key_modification_zone_isClosed s).isOpen_compl,
    hx, ?_⟩
  intro y hy
  exact polygon_product_key_body_iff_raw_outside_modifications y hy

/-- Every actual boundary point outside the 56 actual graph windows has an
open raw-carrier neighborhood, including collar boundary points. -/
theorem polygon_product_key_frontier_raw_neighborhood (x : EFour)
    (hx : x ∈ frontier polygonProductKeyBody)
    (hwindow : ∀ s, x ∉ productKeyGraphWindow s) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ polygonProductKeyBody ↔ y ∈ polygonProductBody := by
  apply polygon_product_key_exists_raw_neighborhood x
  rintro h
  obtain ⟨s,hs⟩ := mem_iUnion.mp h
  exact hwindow s ⟨(polygon_product_key_body_frontier_local_iff s x
    (product_key_modification_zone_subset_collar_interior s hs)).mp hx, hs.1⟩

theorem polygon_product_key_frontier_raw_of_no_window (x : EFour)
    (hx : x ∈ frontier polygonProductKeyBody)
    (hwindow : ∀ s, x ∉ productKeyGraphWindow s) :
    x ∈ frontier polygonProductBody := by
  obtain ⟨U,hU,hxU,he⟩ := polygon_product_key_frontier_raw_neighborhood x hx hwindow
  refine ⟨subset_closure ((he x hxU).mp
    (polygon_product_key_body_isClosed.frontier_subset hx)), ?_⟩
  intro hxint
  apply hx.2
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Filter.inter_mem (hU.mem_nhds hxU) (isOpen_interior.mem_nhds hxint))
  intro y hy
  exact (he y hy.1).mpr (interior_subset hy.2)

theorem polygon_product_key_frontier_cover :
    frontier polygonProductKeyBody ⊆ frontier polygonProductBody ∪
      ⋃ s, productKeyGraphWindow s := by
  classical
  intro x hx
  by_cases hw : ∃ s, x ∈ productKeyGraphWindow s
  · exact Or.inr (mem_iUnion.mpr hw)
  · exact Or.inl (polygon_product_key_frontier_raw_of_no_window x hx (by simpa using hw))

end
end SpectreGeometry

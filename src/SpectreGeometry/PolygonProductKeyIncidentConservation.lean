module

public import SpectreGeometry.PolygonProductKeyWindowConeClassification
public import SpectreGeometry.PolygonProductKeyIncidentBoundary
public import SpectreGeometry.FiniteConeFanConservation
public import SpectreGeometry.FiniteSixthSectorClassification

@[expose] public section


/-! Angular conservation for the actual finite incident family of a physical
keyed-product tiling. Coverage, packing, and finite incidence are obtained
from the two-field physical tiling interface. Cone classification is kept
explicit in this assembly layer, and is instantiated in the next layer. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set MeasureTheory FiniteConeFan
open scoped BigOperators

theorem actual_incident_cone_mass_sum {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (x : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u)
    [Fintype (polygonProductIncidentTiles f x)]
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (M : ∀ i : polygonProductIncidentTiles f x, ActualBoundaryConeModel (f i.val) x L) :
    ∑ i, coneAngularMass L (M i).cone = 2*Real.pi := by
  obtain ⟨_,_,U,hU,hxU,_,hcover,hd⟩ := T.finite_key_boundary_germ root u x hx
  let S := fun i : polygonProductIncidentTiles f x => placedPolygonProductKeyBody (f i.val)
  let C := fun i : polygonProductIncidentTiles f x => (M i).cone
  have hg (i : polygonProductIncidentTiles f x) : LocalConeGerm (S i) x (C i) := (M i).germ
  have hlocal : ∃ V : Set EFour, IsOpen V ∧ 0 ∈ V ∧ ∀ z ∈ V, ∃ i, x+z ∈ S i := by
    refine ⟨(fun z : EFour => x+z) ⁻¹' U,hU.preimage (continuous_const.add continuous_id),
      by simpa using hxU,?_⟩
    intro z hz
    obtain ⟨i,hi,hiz⟩ := hcover (x+z) hz
    exact ⟨⟨i,hi⟩,hiz⟩
  obtain ⟨hc,hdc⟩ := finite_local_germs_fan S C x hg
    (fun i t ht z => (M i).signs.homogeneous t ht z) hlocal hd
  exact angular_mass_sum_real L C (fun i => (M i).normals)
    (fun i => (M i).closed) (fun i => (M i).normal_range)
    (fun i z hz hn => (M i).signs.mem_interior_of_off_normals hz hn) hdc hc

/-- Once the proved actual stratum models are supplied, one root key forces
exactly two incident tiles and makes every incident sector a literal key. -/
theorem classified_actual_incidents_two {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (x : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u)
    [Fintype (polygonProductIncidentTiles f x)]
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (M : ∀ i : polygonProductIncidentTiles f x, ActualBoundaryConeModel (f i.val) x L)
    (hclass : ∀ i, ConeSectorClassification (f i.val) x L (M i).cone)
    (hroot : ∃ i, ActualKeyMass (f i.val) x L (M i).cone) :
    Fintype.card (polygonProductIncidentTiles f x) = 2 ∧
      ∀ i, ActualKeyMass (f i.val) x L (M i).cone := by
  apply finite_sixth_sector_classification (fun i => coneAngularMass L (M i).cone)
    (fun i => ActualKeyMass (f i.val) x L (M i).cone)
  · obtain ⟨i,hi⟩ := hroot
    exact ⟨i,hi,hi.bounds.2.2⟩
  · intro i hi
    exact ⟨hi.bounds.1,hi.bounds.2.1⟩
  · intro i hi
    exact (hclass i).resolve_right hi
  · exact actual_incident_cone_mass_sum T root u x hx L M

/-- The resulting companion is a different physical tile and an actual key
crease, with no ordinary-sector, contact, or angular-sum premise. -/
theorem classified_actual_incident_companion {ι : Type*}
    {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
    (root : ι) (u : ProductKeySite) (x : EFour)
    (hx : x ∈ placedProductKeyGraphWindow (f root) u)
    [Fintype (polygonProductIncidentTiles f x)]
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (M : ∀ i : polygonProductIncidentTiles f x, ActualBoundaryConeModel (f i.val) x L)
    (hclass : ∀ i, ConeSectorClassification (f i.val) x L (M i).cone)
    (hroot : ∃ i, ActualKeyMass (f i.val) x L (M i).cone) :
    ∃ j : ι, j ≠ root ∧ ∃ v : ProductKeySite, x ∈ f j '' creaseComplex v := by
  obtain ⟨hcard,hall⟩ := classified_actual_incidents_two T root u x hx L M hclass hroot
  have hr : root ∈ polygonProductIncidentTiles f x :=
    image_mono (product_key_graph_window_subset_body u) hx
  let r : polygonProductIncidentTiles f x := ⟨root,hr⟩
  obtain ⟨j,hjr⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num) r
  obtain ⟨v,hv,_⟩ := hall j
  exact ⟨j.val,fun he => hjr (Subtype.ext he),v,hv⟩

end
end SpectreGeometry.ProductCrease

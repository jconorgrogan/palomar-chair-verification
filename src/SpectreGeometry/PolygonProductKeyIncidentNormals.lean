module

public import SpectreGeometry.PolygonProductKeyCrossPlacement
public import SpectreGeometry.PolygonProductKeyCreaseNormalSpan
public import SpectreGeometry.PolygonProductKeyTransverseClassification

@[expose] public section


/-! Dense actual placed crease points control every incident boundary-plane
normal. The pointwise key classification includes the zero-extension case.
No normal-span, finite-neighbor or contact premise remains in the dense roots. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace

/-- The affine and displacement APIs have the same actual orthogonal part. -/
theorem affine_linear_eq_displacement (f : EFour ≃ᵢ EFour) :
    f.toRealAffineIsometryEquiv.linearIsometryEquiv = f.toRealLinearIsometryEquiv := by
  ext v
  have h : f v = f 0 + f.toRealAffineIsometryEquiv.linearIsometryEquiv v := by
    simpa only [zero_add,IsometryEquiv.coeFn_toRealAffineIsometryEquiv] using
      PhysicalRegistration.affineIsometry_map_add f.toRealAffineIsometryEquiv (0 : EFour) v
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply,h]
  abel


theorem baseGeneric_incident_boundary_normal_span
    {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i))) (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (u : ProductKeySite) (s : ProductKeySide) :
    ∃ D : Set (EFour), D ⊆ f i '' baseGeneric u s ∧
      closure D = f i '' baseCrease u s ∧
      ∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ b : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane b →
          (f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b) ∈ Submodule.span ℝ
            {(f i).toRealLinearIsometryEquiv (productKeyOutwardNormal u), (f i).toRealLinearIsometryEquiv (productKeySideNormal u s)} := by
  obtain ⟨D, hDG, hDC, hplanes⟩ :=
    baseGeneric_crossPlacement f hdisjoint i u s
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j hj b hb
  rw [← affine_linear_eq_displacement (f i)]
  apply placed_baseCrease_containing_normal_mem_span u s (f i)
    ((f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b))
    (productKeyBoundaryPlaneLevel b +
      ⟪(f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b), f j (productKeyBoundaryPlaneCenter b)⟫_ℝ)
  intro y hy
  have h := hplanes x hx j hj b hb hy
  rwa [image_product_key_boundary_plane_uncentered] at h

/-- The analogous endpoint for an actual distinct-axis side crease. -/
theorem sideGeneric_incident_boundary_normal_span
    {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i))) (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (u : ProductKeySite) (s t : ProductKeySide) (hst : s.1 ≠ t.1) :
    ∃ D : Set (EFour), D ⊆ f i '' sideGeneric u s t ∧
      closure D = f i '' sideCrease u s t ∧
      ∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ b : ProductKeyBoundaryPlaneIndex, x ∈ f j '' productKeyBoundaryPlane b →
          (f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b) ∈ Submodule.span ℝ
            {(f i).toRealLinearIsometryEquiv (productKeySideNormal u s), (f i).toRealLinearIsometryEquiv (productKeySideNormal u t)} := by
  obtain ⟨D, hDG, hDC, hplanes⟩ :=
    sideGeneric_crossPlacement f hdisjoint i u s t hst
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j hj b hb
  rw [← affine_linear_eq_displacement (f i)]
  apply placed_sideCrease_containing_normal_mem_span u s t hst (f i)
    ((f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b))
    (productKeyBoundaryPlaneLevel b +
      ⟪(f j).toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b), f j (productKeyBoundaryPlaneCenter b)⟫_ℝ)
  intro y hy
  have h := hplanes x hx j hj b hb hy
  rwa [image_product_key_boundary_plane_uncentered] at h

/-- Pulling a proved world-space span back through an arbitrary placement. -/
theorem normal_mem_span_pair_of_placedNormal_mem_span
    (f : EFour ≃ᵢ EFour) (n p q : EFour)
    (h : f.toRealLinearIsometryEquiv n ∈ Submodule.span ℝ ({p, q} : Set (EFour))) :
    n ∈ Submodule.span ℝ
      {f.toRealLinearIsometryEquiv.symm p,
       f.toRealLinearIsometryEquiv.symm q} := by
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp h
  apply Submodule.mem_span_pair.mpr
  refine ⟨r, s, ?_⟩
  have heq := congrArg f.toRealLinearIsometryEquiv.symm hrs
  simpa only [map_add, map_smul,
    LinearIsometryEquiv.symm_apply_apply] using heq

/-- The actual zero-extension case is retained along with all active strata. -/
def KeyWindowStratum (u : ProductKeySite) (x : EFour) : Prop :=
  (∃ s : ProductKeySide, productKeyBranchProfile u s x < 0) ∨
  (∃ s : ProductKeySide, x ∈ strictBranchRegion u s) ∨
  (∃ s : ProductKeySide, x ∈ baseGeneric u s) ∨
  (∃ s t : ProductKeySide, s.1 ≠ t.1 ∧ x ∈ sideGeneric u s t)

theorem placed_key_window_stratum_of_boundary_normal_span
    (f : EFour ≃ᵢ EFour) (u : ProductKeySite) (x p q : EFour)
    (hx : f.symm x ∈ productKeyGraphWindow u)
    (hplanes : ∀ b : ProductKeyBoundaryPlaneIndex,
      x ∈ f '' productKeyBoundaryPlane b →
      f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b) ∈ Submodule.span ℝ ({p,q} : Set EFour)) :
    KeyWindowStratum u (f.symm x) := by
  apply keyGraphWindow_transverse_stratum_classification u (f.symm x)
    (f.toRealLinearIsometryEquiv.symm p)
    (f.toRealLinearIsometryEquiv.symm q) hx
  · intro s hs
    apply normal_mem_span_pair_of_placedNormal_mem_span f (productKeySideNormal u s) p q
    exact hplanes (.inr (u,some s))
      ⟨f.symm x,product_key_side_face_plane u s _ hs,f.apply_symm_apply x⟩
  · intro hz
    apply normal_mem_span_pair_of_placedNormal_mem_span f (productKeyOutwardNormal u) p q
    exact hplanes (.inr (u,none)) ⟨f.symm x,hz,f.apply_symm_apply x⟩

theorem baseGeneric_incident_key_classification {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (u : ProductKeySite) (b : ProductKeySide) :
    ∃ D : Set EFour, D ⊆ f i '' baseGeneric u b ∧
      closure D = f i '' baseCrease u b ∧
      ∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ v, (f j).symm x ∈ productKeyGraphWindow v →
          KeyWindowStratum v ((f j).symm x) := by
  obtain ⟨D,hDG,hDC,hplanes⟩ := baseGeneric_incident_boundary_normal_span f hdisjoint i u b
  refine ⟨D,hDG,hDC,?_⟩
  intro x hx j hj v hv
  exact placed_key_window_stratum_of_boundary_normal_span (f j) v x
    ((f i).toRealLinearIsometryEquiv (productKeyOutwardNormal u))
    ((f i).toRealLinearIsometryEquiv (productKeySideNormal u b)) hv (hplanes x hx j hj)

theorem sideGeneric_incident_key_classification {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j))))
    (i : ι) (u : ProductKeySite) (b c : ProductKeySide) (hbc : b.1 ≠ c.1) :
    ∃ D : Set EFour, D ⊆ f i '' sideGeneric u b c ∧
      closure D = f i '' sideCrease u b c ∧
      ∀ x ∈ D, ∀ j, x ∈ placedPolygonProductKeyBody (f j) →
        ∀ v, (f j).symm x ∈ productKeyGraphWindow v →
          KeyWindowStratum v ((f j).symm x) := by
  obtain ⟨D,hDG,hDC,hplanes⟩ := sideGeneric_incident_boundary_normal_span f hdisjoint i u b c hbc
  refine ⟨D,hDG,hDC,?_⟩
  intro x hx j hj v hv
  exact placed_key_window_stratum_of_boundary_normal_span (f j) v x
    ((f i).toRealLinearIsometryEquiv (productKeySideNormal u b))
    ((f i).toRealLinearIsometryEquiv (productKeySideNormal u c)) hv (hplanes x hx j hj)

end
end SpectreGeometry.ProductCrease
